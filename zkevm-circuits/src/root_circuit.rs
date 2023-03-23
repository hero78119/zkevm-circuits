//! The Root circuit implementation.
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::serde::SerdeObject,
    plonk::{Circuit, ConstraintSystem, Error},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use itertools::Itertools;
use maingate::MainGateInstructions;
use snark_verifier::{util::arithmetic::MultiMillerLoop, verifier::plonk::PlonkProtocol};
use std::iter;

mod aggregation;

pub use aggregation::{
    aggregate, AggregationConfig, EccChip, Halo2Loader, KzgAs, KzgDk, KzgSvk,
    PlonkSuccinctVerifier, PlonkVerifier, PoseidonTranscript, Snark, SnarkWitness, BITS,
    EC_POINT_LIMBS, LIMBS, NUM_AS_EC_POINTS,
};
pub use snark_verifier::system::halo2::{compile, Config};

#[cfg(any(feature = "test", test))]
pub use aggregation::TestAggregationCircuit;

/// RootCircuit for aggregating SuperCircuit into a much smaller proof.
#[derive(Clone)]
pub struct RootCircuit<'a, M: MultiMillerLoop> {
    svk: KzgSvk<M>,
    snark_witness: SnarkWitness<'a, M::G1Affine>,
    instance: Vec<M::Scalar>,
}

impl<'a, M: MultiMillerLoop> RootCircuit<'a, M>
where
    M::G1Affine: SerdeObject,
    M::G2Affine: SerdeObject,
{
    /// Create a `RootCircuit` with accumulator computed given a `SuperCircuit`
    /// proof and its instance. Returns `None` if given proof is invalid.
    pub fn new(
        params: &ParamsKZG<M>,
        super_circuit_protocol: &'a PlonkProtocol<M::G1Affine>,
        super_circuit_instances: Value<&'a Vec<Vec<M::Scalar>>>,
        super_circuit_proof: Value<&'a [u8]>,
    ) -> Result<Self, snark_verifier::Error> {
        // root circuit instance (aka public input) = {super circuit instances} + {extra AS
        // instance}
        let num_instances = super_circuit_protocol.num_instance.iter().sum::<usize>()
            + NUM_AS_EC_POINTS * EC_POINT_LIMBS;

        // super circuit instances is Vec<Vec<Scalar>> shape, which can be imagine as column -> row
        // representation. Here traverse column -> row instance into flatten, and at the end concat
        // with accumulation (lhs, rhs) instance.
        // NOTE: we didn't witness accumulation is because parings in circuit consume lots of row,
        // therefore instead we do paring on verifier side via precompile, aka "outside" the
        // circuit.
        let instance = {
            let mut instance = Ok(vec![M::Scalar::zero(); num_instances]);

            // TODO find way to retrieve A, B from Value(A) and Value(B) for better better
            // readability
            super_circuit_instances
                .as_ref()
                .zip(super_circuit_proof.as_ref())
                .map(|(super_circuit_instances, super_circuit_proof)| {
                    let snark = Snark::new(
                        super_circuit_protocol,
                        super_circuit_instances,
                        super_circuit_proof,
                    );

                    let accumulator_limbs = aggregate::<M>(params, [snark]).unwrap();

                    // instance = [super_circuit_instances] + [accumulator_limbs]
                    instance = Ok(iter::empty()
                        // Propagate `SuperCircuit`'s instance
                        .chain(super_circuit_instances.iter().flatten().cloned())
                        // Output aggregated accumulator limbs
                        .chain(accumulator_limbs)
                        .collect_vec());
                });

            instance?
        };
        debug_assert_eq!(instance.len(), num_instances);

        Ok(Self {
            svk: KzgSvk::<M>::new(params.get_g()[0]),
            snark_witness: SnarkWitness::new(
                super_circuit_protocol,
                super_circuit_instances,
                super_circuit_proof,
            ),
            instance,
        })
    }

    /// Returns accumulator indices in instance columns, which will be in
    /// the last `4 * LIMBS` rows of instance column in `MainGate`.
    pub fn accumulator_indices(&self) -> Vec<(usize, usize)> {
        let offset = self
            .snark_witness
            .protocol()
            .num_instance
            .iter()
            .sum::<usize>();
        (offset..).map(|idx| (0, idx)).take(4 * LIMBS).collect()
    }

    /// Returns number of instance
    pub fn num_instance(&self) -> Vec<usize> {
        vec![
            self.snark_witness
                .protocol()
                .num_instance
                .iter()
                .sum::<usize>()
                + 4 * LIMBS,
        ]
    }

    /// Returns instance
    pub fn instance(&self) -> Vec<Vec<M::Scalar>> {
        vec![self.instance.clone()]
    }
}

impl<'a, M: MultiMillerLoop> Circuit<M::Scalar> for RootCircuit<'a, M> {
    type Config = AggregationConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            svk: self.svk,
            snark_witness: self.snark_witness.without_witnesses(),
            instance: vec![M::Scalar::zero(); self.instance.len()],
        }
    }

    fn configure(meta: &mut ConstraintSystem<M::Scalar>) -> Self::Config {
        AggregationConfig::configure::<M::G1Affine>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<M::Scalar>,
    ) -> Result<(), Error> {
        config.load_table(&mut layouter)?;
        let (instance, accumulator_limbs) =
            config.aggregate::<M>(&mut layouter, &self.svk, [self.snark_witness])?;

        // Constrain equality to instance values
        let main_gate = config.main_gate();
        for (row, limb) in instance
            .into_iter()
            .flatten()
            .flatten()
            .chain(accumulator_limbs)
            .enumerate()
        {
            main_gate.expose_public(layouter.namespace(|| ""), limb, row)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        root_circuit::{compile, Config, PoseidonTranscript, RootCircuit},
        super_circuit::{super_circuit_tests::block_1tx, SuperCircuit},
    };
    use bus_mapping::circuit_input_builder::CircuitsParams;
    use halo2_proofs::{
        circuit::Value,
        dev::MockProver,
        halo2curves::bn256::Bn256,
        plonk::{create_proof, keygen_pk, keygen_vk},
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverGWC,
        },
    };
    use itertools::Itertools;
    use rand::rngs::OsRng;

    #[ignore = "Due to high memory requirement"]
    #[test]
    fn test_root_circuit() {
        let (params, protocol, proof, instance) = {
            // Preprocess
            const MAX_TXS: usize = 1;
            const MAX_CALLDATA: usize = 32;
            const TEST_MOCK_RANDOMNESS: u64 = 0x100;
            let circuits_params = CircuitsParams {
                max_txs: MAX_TXS,
                max_calldata: MAX_CALLDATA,
                max_rws: 256,
                max_copy_rows: 256,
                max_exp_steps: 256,
                max_bytecode: 512,
                max_evm_rows: 0,
                max_keccak_rows: 0,
            };
            let (k, circuit, instance, _) =
                SuperCircuit::<_, MAX_TXS, MAX_CALLDATA, TEST_MOCK_RANDOMNESS>::build(
                    block_1tx(),
                    circuits_params,
                )
                .unwrap();
            let params = ParamsKZG::<Bn256>::setup(k, OsRng);
            let pk = keygen_pk(&params, keygen_vk(&params, &circuit).unwrap(), &circuit).unwrap();
            // protocol contains
            // 1. all slot in plonkish formula, e.g. query, evaluation, ...
            // 2. ...
            // 3. ...
            let protocol = compile(
                &params,
                pk.get_vk(),
                Config::kzg()
                    .with_num_instance(instance.iter().map(|instance| instance.len()).collect()),
            );

            // Create proof
            // a proof is a transcript. That's why we care `proof size`
            let proof = {
                let mut transcript = PoseidonTranscript::new(Vec::new());
                create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                    &params,
                    &pk,
                    &[circuit],
                    &[&instance.iter().map(Vec::as_slice).collect_vec()],
                    OsRng,
                    &mut transcript,
                )
                .unwrap();
                transcript.finalize()
            };

            (params, protocol, proof, instance)
        };

        let root_circuit = RootCircuit::new(
            &params,
            &protocol,
            Value::known(&instance),
            Value::known(&proof),
        )
        .unwrap();
        assert_eq!(
            MockProver::run(26, &root_circuit, root_circuit.instance())
                .unwrap()
                .verify_par(),
            Ok(())
        );
    }
}
