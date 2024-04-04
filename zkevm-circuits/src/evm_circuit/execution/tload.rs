use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                EVMConstraintBuilder, ReversionInfo, StepStateTransition, Transition::Delta,
            },
            CachedRegion, Cell, StepRws,
        },
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::{
        word::{WordExpr, WordLoHiCell},
        Expr,
    },
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct TloadGadget<F> {
    same_context: SameContextGadget<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    callee_address: WordLoHiCell<F>,
    key: WordLoHiCell<F>,
    value: WordLoHiCell<F>,
    committed_value: WordLoHiCell<F>,
}

impl<F: Field> ExecutionGadget<F> for TloadGadget<F> {
    const NAME: &'static str = "TLOAD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::TLOAD;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let reversion_info = cb.reversion_info_read(None);
        let callee_address = cb.call_context_read_as_word(None, CallContextFieldTag::CalleeAddress);

        let key = cb.query_word_unchecked();
        // Pop the key from the stack
        cb.stack_pop(key.to_word());

        let value = cb.query_word_unchecked();
        let committed_value = cb.query_word_unchecked();
        cb.account_storage_read(
            callee_address.to_word(),
            key.to_word(),
            value.to_word(),
            tx_id.expr(),
            committed_value.to_word(),
        );

        cb.stack_push(value.to_word());

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(9.expr()),
            program_counter: Delta(1.expr()),
            reversible_write_counter: Delta(1.expr()),
            gas_left: Delta(-OpcodeId::TLOAD.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            tx_id,
            reversion_info,
            callee_address,
            key,
            value,
            committed_value,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _chunk: &Chunk<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id)))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;
        self.callee_address
            .assign_h160(region, offset, call.address)?;

        let mut rws = StepRws::new(block, step);

        rws.offset_add(4);

        let key = rws.next().stack_value();
        let (_, committed_value) = rws.next().aux_pair();
        let value = rws.next().stack_value();

        self.key.assign_u256(region, offset, key)?;
        self.value.assign_u256(region, offset, value)?;

        self.committed_value
            .assign_u256(region, offset, committed_value)?;

        rws.next();

        Ok(())
    }
}

#[cfg(test)]
mod test {

    use crate::{evm_circuit::test::rand_word, test_util::CircuitTestBuilder};
    use eth_types::{bytecode, Word};
    use mock::{test_ctx::helpers::tx_from_1_to_0, TestContext, MOCK_ACCOUNTS};

    fn test_ok(key: Word, value: Word) {
        // Here we use two bytecodes to test both is_persistent(STOP) or not(REVERT)
        // Besides, in bytecode we use two TLOADs,
        // the first TLOAD is used to test cold,  and the second is used to test warm
        let bytecode_success = bytecode! {
            PUSH32(key)
            TLOAD
            PUSH32(key)
            TLOAD
            STOP
        };
        let bytecode_failure = bytecode! {
            PUSH32(key)
            TLOAD
            PUSH32(key)
            TLOAD
            PUSH32(0)
            PUSH32(0)
            REVERT
        };
        for bytecode in [bytecode_success, bytecode_failure] {
            let ctx = TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(MOCK_ACCOUNTS[0])
                        .balance(Word::from(10u64.pow(19)))
                        .code(bytecode)
                        .storage(vec![(key, value)].into_iter());
                    accs[1]
                        .address(MOCK_ACCOUNTS[1])
                        .balance(Word::from(10u64.pow(19)));
                },
                tx_from_1_to_0,
                |block, _txs| block,
            )
            .unwrap();

            CircuitTestBuilder::new_from_test_ctx(ctx).run();
        }
    }

    #[test]
    fn tload_gadget_simple() {
        let key = 0x030201.into();
        let value = 0x060504.into();
        test_ok(key, value);
    }

    #[test]
    fn tload_gadget_rand() {
        let key = rand_word();
        let value = rand_word();
        test_ok(key, value);
    }
}
