//! This module contains the CircuitInputBuilder, which is an object that takes
//! types from geth / web3 and outputs the circuit inputs.

mod access;
mod block;
mod call;
mod chunk;
mod execution;
mod input_state_ref;
#[cfg(test)]
mod tracer_tests;
mod transaction;

use self::{
    access::gen_state_access_trace,
    chunk::{Chunk, ChunkSteps},
};
use crate::{
    error::Error,
    evm::opcodes::{gen_associated_ops, gen_associated_steps},
    operation::{
        CallContextField, Op, Operation, OperationContainer, PaddingOp, RWCounter, StartOp,
        StepStateField, StepStateOp, RW,
    },
    rpc::GethClient,
    state_db::{self, CodeDB, StateDB},
};
pub use access::{Access, AccessSet, AccessValue, CodeSource};
pub use block::{Block, BlockContext};
pub use call::{Call, CallContext, CallKind};
pub use chunk::ChunkContext;
use core::fmt::Debug;
use eth_types::{
    self, geth_types,
    sign_types::{pk_bytes_le, pk_bytes_swap_endianness, SignData},
    Address, GethExecStep, GethExecTrace, ToWord, Word,
};
use ethers_providers::JsonRpcClient;
pub use execution::{
    CopyDataType, CopyEvent, CopyStep, ExecState, ExecStep, ExpEvent, ExpStep, NumberOrHash,
};
pub use input_state_ref::CircuitInputStateRef;
use itertools::Itertools;
use log::warn;
use std::{collections::HashMap, ops::Deref};
pub use transaction::{Transaction, TransactionContext};

/// Circuit Setup Parameters
#[derive(Debug, Clone, Copy)]
pub struct FixedCParams {
    /// Maximum number of rw operations in the state circuit (RwTable length /
    /// nummber of rows). This must be at least the number of rw operations
    /// + 1, in order to allocate at least a Start row.
    pub max_rws: usize,
    // TODO: evm_rows: Maximum number of rows in the EVM Circuit
    /// Maximum number of txs in the Tx Circuit
    pub max_txs: usize,
    /// Maximum number of bytes from all txs calldata in the Tx Circuit
    pub max_calldata: usize,
    /// Max ammount of rows that the CopyCircuit can have.
    pub max_copy_rows: usize,
    /// Max number of steps that the ExpCircuit can have. Each step is further
    /// expressed in 7 rows
    pub max_exp_steps: usize,
    /// Maximum number of bytes supported in the Bytecode Circuit
    pub max_bytecode: usize,
    /// Pad evm circuit number of rows.
    /// When 0, the EVM circuit number of rows will be dynamically calculated,
    /// so the same circuit will not be able to proof different witnesses.
    /// In this case it will contain as many rows for all steps + 1 row
    /// for EndBlock.
    pub max_evm_rows: usize,
    /// Pad the keccak circuit with this number of invocations to a static
    /// capacity.  Number of keccak_f that the Keccak circuit will support.
    /// When 0, the Keccak circuit number of rows will be dynamically
    /// calculated, so the same circuit will not be able to prove different
    /// witnesses.
    pub max_keccak_rows: usize,
}

/// Unset Circuits Parameters
///
/// To reduce the testing overhead, we determine the parameters by the testing inputs.
/// A new [`FixedCParams`] will be computed from the generated circuit witness.
#[derive(Debug, Clone, Copy)]
pub struct DynamicCParams {}
/// Circuit Setup Parameters. These can be fixed/concrete or unset/dynamic.
pub trait CircuitsParams: Debug + Copy {
    /// Return the best number of chunks given circuit params
    fn best_chuncks(&self) -> usize;
}

impl CircuitsParams for FixedCParams {
    fn best_chuncks(&self) -> usize {
        2 // TODO(Cecilia)
    }
}
impl CircuitsParams for DynamicCParams {
    fn best_chuncks(&self) -> usize {
        3 // TODO(Cecilia)
    }
}
impl Default for FixedCParams {
    /// Default values for most of the unit tests of the Circuit Parameters
    fn default() -> Self {
        FixedCParams {
            max_rws: 1000,
            max_txs: 1,
            max_calldata: 256,
            // TODO: Check whether this value is correct or we should increase/decrease based on
            // this lib tests
            max_copy_rows: 1000,
            max_exp_steps: 1000 / 7, // exp_circuit::OFFSET_INCREMENT = 7
            max_bytecode: 512,
            max_evm_rows: 0,
            max_keccak_rows: 0,
        }
    }
}

/// Builder to generate a complete circuit input from data gathered from a geth
/// instance. This structure is the centre of the crate and is intended to be
/// the only entry point to it. The `CircuitInputBuilder` works in several
/// steps:
///
/// 1. Take a [`eth_types::Block`] to build the circuit input associated with
/// the block. 2. For each [`eth_types::Transaction`] in the block, take the
/// [`eth_types::GethExecTrace`] to build the circuit input associated with
/// each transaction, and the bus-mapping operations associated with each
/// [`eth_types::GethExecStep`] in the [`eth_types::GethExecTrace`].
///
/// The generated bus-mapping operations are:
/// [`StackOp`](crate::operation::StackOp)s,
/// [`MemoryOp`](crate::operation::MemoryOp)s and
/// [`StorageOp`](crate::operation::StorageOp), which correspond to each
/// [`OpcodeId`](crate::evm::OpcodeId)s used in each `ExecTrace` step so that
/// the State Proof witnesses are already generated on a structured manner and
/// ready to be added into the State circuit.
#[derive(Debug)]
pub struct CircuitInputBuilder<C: CircuitsParams> {
    /// StateDB key-value DB
    pub sdb: StateDB,
    /// Map of account codes by code hash
    pub code_db: CodeDB,
    /// Block
    pub block: Block,
    /// Chunk
    pub chunks: Vec<Chunk>,
    /// Circuits Setup Paramteres
    pub circuits_params: C,
    /// Block Context
    pub block_ctx: BlockContext,
    /// Chunk Context
    pub chunk_ctx: Option<ChunkContext>,
}

impl<'a, C: CircuitsParams> CircuitInputBuilder<C> {
    /// Create a new CircuitInputBuilder from the given `eth_block` and
    /// `constants`.
    pub fn new(sdb: StateDB, code_db: CodeDB, block: Block, params: C) -> Self {
        let total_chunks = params.best_chuncks();
        let chunks = (0..total_chunks)
            .map(|i| Chunk {
                chunk_index: i,
                chunk_steps: ChunkSteps {
                    begin_chunk: ExecStep {
                        exec_state: ExecState::BeginChunk,
                        ..ExecStep::default()
                    },
                    end_chunk: Some(ExecStep {
                        exec_state: ExecState::EndChunk,
                        ..ExecStep::default()
                    }),
                },
                ..Chunk::default()
            })
            .collect::<Vec<Chunk>>();
        Self {
            sdb,
            code_db,
            block,
            chunks,
            circuits_params: params,
            block_ctx: BlockContext::new(),
            chunk_ctx: Some(ChunkContext::new(0, total_chunks)),
        }
    }

    /// Obtain a mutable reference to the state that the `CircuitInputBuilder`
    /// maintains, contextualized to a particular transaction and a
    /// particular execution step in that transaction.
    pub fn state_ref(
        &'a mut self,
        tx: &'a mut Transaction,
        tx_ctx: &'a mut TransactionContext,
    ) -> CircuitInputStateRef {
        CircuitInputStateRef {
            sdb: &mut self.sdb,
            code_db: &mut self.code_db,
            block: &mut self.block,
            block_ctx: &mut self.block_ctx,
            chunk_ctx: self.chunk_ctx.as_mut(),
            tx,
            tx_ctx,
        }
    }

    /// Create a new Transaction from a [`eth_types::Transaction`].
    pub fn new_tx(
        &mut self,
        id: u64,
        eth_tx: &eth_types::Transaction,
        is_success: bool,
    ) -> Result<Transaction, Error> {
        let call_id = self.block_ctx.rwc.0;

        self.block_ctx.call_map.insert(
            call_id,
            (
                eth_tx
                    .transaction_index
                    .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?
                    .as_u64() as usize,
                0,
            ),
        );

        Transaction::new(
            id,
            call_id,
            &self.sdb,
            &mut self.code_db,
            eth_tx,
            is_success,
        )
    }

    /// Iterate over all generated CallContext RwCounterEndOfReversion
    /// operations and set the correct value. This is required because when we
    /// generate the RwCounterEndOfReversion operation in
    /// `gen_associated_ops` we don't know yet which value it will take,
    /// so we put a placeholder; so we do it here after the values are known.
    pub fn set_value_ops_call_context_rwc_eor(&mut self) {
        for oper in self.block.container.call_context.iter_mut() {
            let op = oper.op_mut();
            if matches!(op.field, CallContextField::RwCounterEndOfReversion) {
                let (tx_idx, call_idx) = self
                    .block_ctx
                    .call_map
                    .get(&op.call_id)
                    .expect("call_id not found in call_map");
                op.value = self.block.txs[*tx_idx].calls()[*call_idx]
                    .rw_counter_end_of_reversion
                    .into();
            }
        }
    }

    /// Handle a transaction with its corresponding execution trace to generate
    /// all the associated operations.  Each operation is registered in
    /// `self.block.container`, and each step stores the
    /// [`OperationRef`](crate::exec_trace::OperationRef) to each of the
    /// generated operations.
    fn handle_tx(
        &mut self,
        eth_tx: &eth_types::Transaction,
        geth_trace: &GethExecTrace,
        is_last_tx: bool,
        tx_index: u64,
    ) -> Result<(), Error> {
        let mut tx = self.new_tx(tx_index, eth_tx, !geth_trace.failed)?;
        let mut tx_ctx = TransactionContext::new(eth_tx, geth_trace, is_last_tx)?;

        // Generate BeginTx step
        let begin_tx_step = gen_associated_steps(
            &mut self.state_ref(&mut tx, &mut tx_ctx),
            ExecState::BeginTx,
        )?;
        tx.steps_mut().push(begin_tx_step);

        for (index, geth_step) in geth_trace.struct_logs.iter().enumerate() {
            let mut state_ref = self.state_ref(&mut tx, &mut tx_ctx);
            log::trace!("handle {}th opcode {:?} ", index, geth_step.op);
            let exec_steps = gen_associated_ops(
                &geth_step.op,
                &mut state_ref,
                &geth_trace.struct_logs[index..],
            )?;
            tx.steps_mut().extend(exec_steps);
            if let Some(chunk_ctx) = &self.chunk_ctx {
                // TODO
            }
        }

        // Generate EndTx step
        let end_tx_step =
            gen_associated_steps(&mut self.state_ref(&mut tx, &mut tx_ctx), ExecState::EndTx)?;
        tx.steps_mut().push(end_tx_step);

        self.sdb.commit_tx();
        self.block.txs.push(tx);

        Ok(())
    }

    // TODO Fix this, for current logic on processing `call` is incorrect
    // TODO re-design `gen_chunk_associated_steps` to separate RW
    fn gen_chunk_associated_steps(&mut self, step: &mut ExecStep, rw: RW) {
        let STEP_STATE_LEN = 10;
        let mut dummy_tx = Transaction::default();
        let mut dummy_tx_ctx = TransactionContext::default();

        let rw_counters = (0..STEP_STATE_LEN)
            .map(|_| self.block_ctx.rwc.inc_pre())
            .collect::<Vec<RWCounter>>();
        // just bump rwc in chunk_ctx as block_ctx rwc to assure same delta apply
        let rw_counters_inner_chunk = (0..STEP_STATE_LEN)
            .map(|_| {
                self.chunk_ctx
                    .as_mut()
                    .map_or_else(RWCounter::new, |chunk_ctx| chunk_ctx.rwc.inc_pre())
            })
            .collect::<Vec<RWCounter>>();

        let tags = {
            let state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);
            let last_call = state
                .block
                .txs
                .last()
                .map(|tx| tx.calls[0].clone())
                .unwrap_or_else(Call::default);
            [
                (StepStateField::CodeHash, last_call.code_hash.to_word()),
                (StepStateField::CallID, Word::from(last_call.call_id)),
                (StepStateField::IsRoot, Word::from(last_call.is_root as u64)),
                (
                    StepStateField::IsCreate,
                    Word::from(last_call.is_create() as u64),
                ),
                (StepStateField::ProgramCounter, Word::from(step.pc)),
                (
                    StepStateField::StackPointer,
                    Word::from(step.stack_pointer()),
                ),
                (StepStateField::GasLeft, Word::from(step.gas_left)),
                (
                    StepStateField::MemoryWordSize,
                    Word::from(step.memory_word_size()),
                ),
                (
                    StepStateField::ReversibleWriteCounter,
                    Word::from(step.reversible_write_counter),
                ),
                (StepStateField::LogID, Word::from(step.log_id)),
            ]
        };

        debug_assert_eq!(STEP_STATE_LEN, tags.len());
        let state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);

        tags.iter()
            .zip_eq(rw_counters)
            .zip_eq(rw_counters_inner_chunk)
            .for_each(|(((tag, value), rw_counter), inner_rw_counter)| {
                push_op(
                    &mut state.block.container,
                    step,
                    rw_counter,
                    inner_rw_counter,
                    rw,
                    StepStateOp {
                        field: tag.clone(),
                        value: *value,
                    },
                );
            });
    }

    /// set chunk context
    pub fn set_chunk_ctx(&mut self, chunk_ctx: ChunkContext) {
        self.chunks = (0..chunk_ctx.total_chunks)
            .map(|i| Chunk {
                chunk_index: i,
                chunk_steps: ChunkSteps {
                    begin_chunk: ExecStep {
                        exec_state: ExecState::BeginChunk,
                        ..ExecStep::default()
                    },
                    end_chunk: Some(ExecStep {
                        exec_state: ExecState::EndChunk,
                        ..ExecStep::default()
                    }),
                },
                ..Chunk::default()
            })
            .collect::<Vec<Chunk>>();
        self.chunk_ctx = Some(chunk_ctx);
    }

    ///
    pub fn cur_chunk(&self) -> &Chunk {
        self.chunk_ctx
            .as_ref()
            .map_or_else(|| &self.chunks[0], |ctx| &self.chunks[ctx.cur])
    }

    ///
    pub fn last_chunk(&self) -> &Chunk {
        self.chunk_ctx
            .as_ref()
            .map(|ctx| &self.chunks[ctx.cur - 1])
            .expect("No last chunk found")
    }

    ///
    pub fn is_first_chunk(&self) -> bool {
        self.chunk_ctx
            .as_ref()
            .map_or(true, |ctx| ctx.is_first_chunk())
    }

    ///
    pub fn is_last_chunk(&self) -> bool {
        self.chunk_ctx
            .as_ref()
            .map_or(true, |ctx| ctx.is_last_chunk())
    }
}

impl CircuitInputBuilder<FixedCParams> {
    /// Handle a block by handling each transaction to generate all the
    /// associated operations.
    pub fn handle_block(
        &mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<&CircuitInputBuilder<FixedCParams>, Error> {
        // accumulates gas across all txs in the block
        self.begin_handle_block(eth_block, geth_traces)?;
        self.set_end_chunk_or_block(self.circuits_params.max_rws);
        Ok(self)
    }

    fn set_end_chunk_or_block(&mut self, max_rws: usize) {
        self.chunk_ctx
            .clone()
            .map(|chunk_ctx| {
                if !chunk_ctx.is_last_chunk() {
                    self.set_end_chunk(max_rws);
                    return;
                }
            })
            .unwrap_or(());

        // set end block
        let mut end_block_not_last = self.block.block_steps.end_block_not_last.clone();
        let mut end_block_last = self.block.block_steps.end_block_last.clone();
        end_block_not_last.rwc = self.block_ctx.rwc;
        end_block_last.rwc = self.block_ctx.rwc;
        end_block_not_last.rwc_inner_chunk = self
            .chunk_ctx
            .as_ref()
            .map_or_else(RWCounter::new, |chunk_ctx| chunk_ctx.rwc);
        end_block_last.rwc_inner_chunk = self
            .chunk_ctx
            .as_ref()
            .map_or_else(RWCounter::new, |chunk_ctx| chunk_ctx.rwc);
        let is_first_chunk = self
            .chunk_ctx
            .as_ref()
            .map_or(true, |chunk_ctx| chunk_ctx.is_first_chunk());
        let mut dummy_tx = Transaction::default();
        let mut dummy_tx_ctx = TransactionContext::default();
        let mut state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);

        if let Some(call_id) = state.block.txs.last().map(|tx| tx.calls[0].call_id) {
            state.call_context_read(
                &mut end_block_last,
                call_id,
                CallContextField::TxId,
                Word::from(state.block.txs.len() as u64),
            );
        }

        // rwc index start from 1
        let end_rwc = state.block_ctx.rwc.0;
        let total_rws = end_rwc - 1;

        // We need at least 1 extra Start row
        // because total_rws exclude Rw::Start
        #[allow(clippy::int_plus_one)]
        {
            assert!(
                total_rws + 1 <= max_rws,
                "total_rws + 1 <= max_rws, total_rws={}, max_rws={}",
                total_rws,
                max_rws
            );
        }

        if is_first_chunk {
            push_op(
                &mut state.block.container,
                &mut end_block_last,
                RWCounter(1),
                RWCounter(1),
                RW::READ,
                StartOp {},
            );
        }
        // TODO fix below to adapt multiple chunk
        if max_rws - total_rws > 1 {
            let (padding_start, padding_end) = (total_rws + 1, max_rws - 1);
            push_op(
                &mut state.block.container,
                &mut end_block_last,
                RWCounter(padding_start),
                RWCounter(padding_start),
                RW::READ,
                PaddingOp {},
            );
            if padding_end != padding_start {
                push_op(
                    &mut state.block.container,
                    &mut end_block_last,
                    RWCounter(padding_end),
                    RWCounter(padding_end),
                    RW::READ,
                    PaddingOp {},
                );
            }
        }

        self.block.block_steps.end_block_not_last = end_block_not_last;
        self.block.block_steps.end_block_last = end_block_last;

        // set final rwc value to chunkctx
        if let Some(chunk_ctx) = self.chunk_ctx.as_mut() {
            chunk_ctx.end_rwc = end_rwc
        }
    }

    fn set_end_chunk(&mut self, max_inner_rws: usize) {
        let mut end_chunk = self.cur_chunk().chunk_steps.end_chunk.clone().unwrap();
        end_chunk.rwc = self.block_ctx.rwc;
        end_chunk.rwc_inner_chunk = self
            .chunk_ctx
            .as_ref()
            .map_or_else(RWCounter::new, |chunk_ctx| chunk_ctx.rwc);
        let is_first_chunk = self
            .chunk_ctx
            .as_ref()
            .map_or(true, |chunk_ctx| chunk_ctx.is_first_chunk());

        let mut dummy_tx = Transaction::default();
        let mut dummy_tx_ctx = TransactionContext::default();
        self.gen_chunk_associated_steps(&mut end_chunk, RW::WRITE);
        let state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);

        // rwc index start from 1
        let end_rwc = state.chunk_ctx.map_or(1, |chunk_ctx| chunk_ctx.rwc.0);
        let total_inner_rws = end_rwc - 1;

        // We need at least 1 extra row at offset 0 for chunk continuous
        #[allow(clippy::int_plus_one)]
        {
            assert!(
                total_inner_rws + 1 <= max_inner_rws,
                "total_inner_rws + 1 <= max_rws, total_inner_rws={}, max_rws={}",
                total_inner_rws,
                max_inner_rws
            );
        }

        if is_first_chunk {
            push_op(
                &mut state.block.container,
                &mut end_chunk,
                RWCounter(1),
                RWCounter(1),
                RW::READ,
                StartOp {},
            );
        }
        // TODO fix below to adapt multiple chunk
        if max_inner_rws - total_inner_rws > 1 {
            let (padding_start, padding_end) = (total_inner_rws + 1, max_inner_rws - 1);
            push_op(
                &mut state.block.container,
                &mut end_chunk,
                RWCounter(padding_start),
                RWCounter(padding_start),
                RW::READ,
                PaddingOp {},
            );
            if padding_end != padding_start {
                push_op(
                    &mut state.block.container,
                    &mut end_chunk,
                    RWCounter(padding_end),
                    RWCounter(padding_end),
                    RW::READ,
                    PaddingOp {},
                );
            }
        }
        self.chunks[self.chunk_ctx.as_ref().unwrap().cur]
            .chunk_steps
            .end_chunk = Some(end_chunk);

        // set final rwc value to chunkctx
        if let Some(chunk_ctx) = self.chunk_ctx.as_mut() {
            chunk_ctx.end_rwc = end_rwc
        }
    }
}

fn push_op<T: Op>(
    container: &mut OperationContainer,
    step: &mut ExecStep,
    rwc: RWCounter,
    rwc_inner_chunk: RWCounter,
    rw: RW,
    op: T,
) {
    let op_ref = container.insert(Operation::new(rwc, rwc_inner_chunk, rw, op));
    step.bus_mapping_instance.push(op_ref);
}

impl<C: CircuitsParams> CircuitInputBuilder<C> {
    fn dry_run(
        &mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<BlockContext, Error> {
        // accumulates gas across all txs in the block
        for (idx, tx) in eth_block.transactions.iter().enumerate() {
            let geth_trace = &geth_traces[idx];
            // Transaction index starts from 1
            let tx_id = idx + 1;
            self.handle_tx(
                tx,
                geth_trace,
                tx_id == eth_block.transactions.len(),
                tx_id as u64,
            )?;
        }
        // set eth_block
        self.block.eth_block = eth_block.clone();
        self.set_value_ops_call_context_rwc_eor();

        let block_ctx = self.block_ctx.clone();
        self.clear();

        Ok(block_ctx)
    }

    fn clear(&mut self) {
        let OperationContainer {
            memory,
            stack,
            storage,
            tx_access_list_account,
            tx_access_list_account_storage,
            tx_refund,
            account,
            call_context,
            tx_receipt,
            tx_log,
            start,
            padding,
            step_state,
        } = &mut self.block.container;
        memory.clear();
        stack.clear();
        storage.clear();
        tx_access_list_account.clear();
        tx_access_list_account_storage.clear();
        tx_refund.clear();
        account.clear();
        call_context.clear();
        tx_receipt.clear();
        tx_log.clear();
        start.clear();
        padding.clear();
        step_state.clear();
        self.block_ctx = BlockContext::new();
    }

    fn compute_param(&self, eth_block: &EthBlock) -> FixedCParams {
        let max_txs = eth_block.transactions.len();
        let max_bytecode = self.code_db.num_rows_required_for_bytecode_table();

        let max_calldata = eth_block
            .transactions
            .iter()
            .fold(0, |acc, tx| acc + tx.input.len());
        let max_exp_steps = self
            .block
            .exp_events
            .iter()
            .fold(0usize, |acc, e| acc + e.steps.len());
        // The `+ 2` is used to take into account the two extra empty copy rows needed
        // to satisfy the query at `Rotation(2)` performed inside of the
        // `rows[2].value == rows[0].value * r + rows[1].value` requirement in the RLC
        // Accumulation gate.
        let max_copy_rows = self
            .block
            .copy_events
            .iter()
            .fold(0, |acc, c| acc + c.bytes.len())
            * 2
            + 4; // disabled and unused rows.

        // TODO fix below logic for multiple rw_table chunks
        let total_rws_before_end_block: usize =
            <RWCounter as Into<usize>>::into(self.block_ctx.rwc) - 1; // -1 since rwc start from index `1`
        let max_rws = total_rws_before_end_block
            + {
                1 // +1 for reserving RW::Start at row 1 (offset 0)
                    + if self.is_last_chunk() && total_rws_before_end_block > 0 { 1 /*end_block -> CallContextFieldTag::TxId lookup*/ } else { 0 }
                    + if self.is_last_chunk() {
                        10  /* stepstate lookup */
                    } else { 0 }
            };
        // Computing the number of rows for the EVM circuit requires the size of ExecStep,
        // which is determined in the code of zkevm-circuits and cannot be imported here.
        // When the evm circuit receives a 0 value it dynamically computes the minimum
        // number of rows necessary.
        let max_evm_rows = 0;
        // Similarly, computing the number of rows for the Keccak circuit requires
        // constants that cannot be accessed from here (NUM_ROUNDS and KECCAK_ROWS).
        // With a 0 value the keccak circuit computes dynamically the minimum number of rows
        // needed.
        let max_keccak_rows = 0;
        FixedCParams {
            max_rws,
            max_txs,
            max_calldata,
            max_copy_rows,
            max_exp_steps,
            max_bytecode,
            max_evm_rows,
            max_keccak_rows,
        }
    }

    /// First part of handle_block, common for dynamic and static circuit parameters.
    pub fn begin_handle_block(
        &mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<(), Error> {
        self.chunk_ctx
            .clone()
            .map(|chunk_ctx| {
                if !chunk_ctx.is_first_chunk() {
                    let mut begin_chunk = self.cur_chunk().chunk_steps.begin_chunk.clone();
                    self.gen_chunk_associated_steps(&mut begin_chunk, RW::READ);
                }
            })
            .unwrap_or(());

        // accumulates gas across all txs in the block
        for (idx, tx) in eth_block.transactions.iter().enumerate() {
            let geth_trace = &geth_traces[idx];
            // Transaction index starts from 1
            let tx_id = idx + 1;
            self.handle_tx(
                tx,
                geth_trace,
                tx_id == eth_block.transactions.len(),
                tx_id as u64,
            )?;
        }
        // set eth_block
        self.block.eth_block = eth_block.clone();
        self.set_value_ops_call_context_rwc_eor();
        Ok(())
    }
}

impl CircuitInputBuilder<DynamicCParams> {
    /// Handle a block by handling each transaction to generate all the
    /// associated operations. From these operations, the optimal circuit parameters
    /// are derived and set.
    pub fn handle_block(
        mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<CircuitInputBuilder<FixedCParams>, Error> {
        self.begin_handle_block(eth_block, geth_traces)?;

        // Compute subcircuits parameters
        let c_params = {
            let max_txs = eth_block.transactions.len();
            let max_bytecode = self.code_db.num_rows_required_for_bytecode_table();

            let max_calldata = eth_block
                .transactions
                .iter()
                .fold(0, |acc, tx| acc + tx.input.len());
            let max_exp_steps = self
                .block
                .exp_events
                .iter()
                .fold(0usize, |acc, e| acc + e.steps.len());
            // The `+ 2` is used to take into account the two extra empty copy rows needed
            // to satisfy the query at `Rotation(2)` performed inside of the
            // `rows[2].value == rows[0].value * r + rows[1].value` requirement in the RLC
            // Accumulation gate.
            let max_copy_rows = self
                .block
                .copy_events
                .iter()
                .fold(0, |acc, c| acc + c.bytes.len())
                * 2
                + 4; // disabled and unused rows.

            // TODO fix below logic for multiple rw_table chunks
            let total_rws_before_end_block: usize =
                <RWCounter as Into<usize>>::into(self.block_ctx.rwc) - 1; // -1 since rwc start from index `1`
            let max_rws = total_rws_before_end_block
                + {
                    1 // +1 for reserving RW::Start at row 1 (offset 0)
                    + if self.is_last_chunk() && total_rws_before_end_block > 0 { 1 /*end_block -> CallContextFieldTag::TxId lookup*/ } else { 0 }
                    + if self.is_last_chunk() {
                        10  /* stepstate lookup */
                    } else {0}
                };
            // Computing the number of rows for the EVM circuit requires the size of ExecStep,
            // which is determined in the code of zkevm-circuits and cannot be imported here.
            // When the evm circuit receives a 0 value it dynamically computes the minimum
            // number of rows necessary.
            let max_evm_rows = 0;
            // Similarly, computing the number of rows for the Keccak circuit requires
            // constants that cannot be accessed from here (NUM_ROUNDS and KECCAK_ROWS).
            // With a 0 value the keccak circuit computes dynamically the minimum number of rows
            // needed.
            let max_keccak_rows = 0;
            FixedCParams {
                max_rws,
                max_txs,
                max_calldata,
                max_copy_rows,
                max_exp_steps,
                max_bytecode,
                max_evm_rows,
                max_keccak_rows,
            }
        };
        let mut cib = CircuitInputBuilder::<FixedCParams> {
            sdb: self.sdb,
            code_db: self.code_db,
            block: self.block,
            chunks: self.chunks,
            circuits_params: c_params,
            block_ctx: self.block_ctx,
            chunk_ctx: self.chunk_ctx,
        };

        cib.set_end_chunk_or_block(c_params.max_rws);
        Ok(cib)
    }
}

/// Return all the keccak inputs used during the processing of the current
/// block.
pub fn keccak_inputs(block: &Block, code_db: &CodeDB) -> Result<Vec<Vec<u8>>, Error> {
    let mut keccak_inputs = Vec::new();
    // Tx Circuit
    let txs: Vec<geth_types::Transaction> = block.txs.iter().map(|tx| tx.deref().clone()).collect();
    keccak_inputs.extend_from_slice(&keccak_inputs_tx_circuit(&txs, block.chain_id.as_u64())?);
    // Bytecode Circuit
    for bytecode in code_db.clone().into_iter() {
        keccak_inputs.push(bytecode.code());
    }
    // EVM Circuit
    keccak_inputs.extend_from_slice(&block.sha3_inputs);
    // MPT Circuit
    // TODO https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/696
    Ok(keccak_inputs)
}

/// Generate the keccak inputs required by the SignVerify Chip from the
/// signature datas.
pub fn keccak_inputs_sign_verify(sigs: &[SignData]) -> Vec<Vec<u8>> {
    let mut inputs = Vec::new();
    for sig in sigs {
        let pk_le = pk_bytes_le(&sig.pk);
        let pk_be = pk_bytes_swap_endianness(&pk_le);
        inputs.push(pk_be.to_vec());
    }
    // Padding signature
    let pk_le = pk_bytes_le(&SignData::default().pk);
    let pk_be = pk_bytes_swap_endianness(&pk_le);
    inputs.push(pk_be.to_vec());
    inputs
}

/// Generate the keccak inputs required by the Tx Circuit from the transactions.
pub fn keccak_inputs_tx_circuit(
    txs: &[geth_types::Transaction],
    chain_id: u64,
) -> Result<Vec<Vec<u8>>, Error> {
    let mut inputs = Vec::new();
    let sign_datas: Vec<SignData> = txs
        .iter()
        .enumerate()
        .filter(|(i, tx)| {
            if tx.v == 0 && tx.r.is_zero() && tx.s.is_zero() {
                warn!("tx {} is not signed, skipping tx circuit keccak input", i);
                false
            } else {
                true
            }
        })
        .map(|(_, tx)| tx.sign_data(chain_id))
        .try_collect()?;
    // Keccak inputs from SignVerify Chip
    let sign_verify_inputs = keccak_inputs_sign_verify(&sign_datas);
    inputs.extend_from_slice(&sign_verify_inputs);
    // NOTE: We don't verify the Tx Hash in the circuit yet, so we don't have more
    // hash inputs.
    Ok(inputs)
}

/// Retrieve the init_code from memory for {CREATE, CREATE2}
pub fn get_create_init_code<'a>(
    call_ctx: &'a CallContext,
    step: &GethExecStep,
) -> Result<&'a [u8], Error> {
    let offset = step.stack.nth_last(1)?.low_u64() as usize;
    let length = step.stack.nth_last(2)?.as_usize();

    let mem_len = call_ctx.memory.0.len();
    if offset >= mem_len {
        return Ok(&[]);
    }

    let offset_end = offset.checked_add(length).unwrap_or(mem_len);

    Ok(&call_ctx.memory.0[offset..offset_end])
}

/// Retrieve the memory offset and length of call.
pub fn get_call_memory_offset_length(step: &GethExecStep, nth: usize) -> Result<(u64, u64), Error> {
    let offset = step.stack.nth_last(nth)?;
    let length = step.stack.nth_last(nth + 1)?;
    if length.is_zero() {
        Ok((0, 0))
    } else {
        Ok((offset.low_u64(), length.low_u64()))
    }
}

type EthBlock = eth_types::Block<eth_types::Transaction>;

/// Struct that wraps a GethClient and contains methods to perform all the steps
/// necessary to generate the circuit inputs for a block by querying geth for
/// the necessary information and using the CircuitInputBuilder.
pub struct BuilderClient<P: JsonRpcClient> {
    cli: GethClient<P>,
    chain_id: Word,
    circuits_params: FixedCParams,
}

/// Get State Accesses from TxExecTraces
pub fn get_state_accesses(
    eth_block: &EthBlock,
    geth_traces: &[eth_types::GethExecTrace],
) -> Result<AccessSet, Error> {
    let mut block_access_trace = vec![Access::new(
        None,
        RW::WRITE,
        AccessValue::Account {
            address: eth_block
                .author
                .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?,
        },
    )];
    for (tx_index, tx) in eth_block.transactions.iter().enumerate() {
        let geth_trace = &geth_traces[tx_index];
        let tx_access_trace = gen_state_access_trace(eth_block, tx, geth_trace)?;
        block_access_trace.extend(tx_access_trace);
    }

    Ok(AccessSet::from(block_access_trace))
}

/// Build a partial StateDB from step 3
pub fn build_state_code_db(
    proofs: Vec<eth_types::EIP1186ProofResponse>,
    codes: HashMap<Address, Vec<u8>>,
) -> (StateDB, CodeDB) {
    let mut sdb = StateDB::new();
    for proof in proofs {
        let mut storage = HashMap::new();
        for storage_proof in proof.storage_proof {
            storage.insert(storage_proof.key, storage_proof.value);
        }
        sdb.set_account(
            &proof.address,
            state_db::Account {
                nonce: proof.nonce.as_u64(),
                balance: proof.balance,
                storage,
                code_hash: proof.code_hash,
            },
        )
    }

    let mut code_db = CodeDB::default();
    for (_address, code) in codes {
        code_db.insert(code.clone());
    }
    (sdb, code_db)
}

impl<P: JsonRpcClient> BuilderClient<P> {
    /// Create a new BuilderClient
    pub async fn new(client: GethClient<P>, circuits_params: FixedCParams) -> Result<Self, Error> {
        let chain_id = client.get_chain_id().await?;

        Ok(Self {
            cli: client,
            chain_id: chain_id.into(),
            circuits_params,
        })
    }

    /// Step 1. Query geth for Block, Txs, TxExecTraces, history block hashes
    /// and previous state root.
    pub async fn get_block(
        &self,
        block_num: u64,
    ) -> Result<(EthBlock, Vec<eth_types::GethExecTrace>, Vec<Word>, Word), Error> {
        let eth_block = self.cli.get_block_by_number(block_num.into()).await?;
        let geth_traces = self.cli.trace_block_by_number(block_num.into()).await?;

        // fetch up to 256 blocks
        let mut n_blocks = std::cmp::min(256, block_num as usize);
        let mut next_hash = eth_block.parent_hash;
        let mut prev_state_root: Option<Word> = None;
        let mut history_hashes = vec![Word::default(); n_blocks];
        while n_blocks > 0 {
            n_blocks -= 1;

            // TODO: consider replacing it with `eth_getHeaderByHash`, it's faster
            let header = self.cli.get_block_by_hash(next_hash).await?;

            // set the previous state root
            if prev_state_root.is_none() {
                prev_state_root = Some(header.state_root.to_word());
            }

            // latest block hash is the last item
            let block_hash = header
                .hash
                .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?
                .to_word();
            history_hashes[n_blocks] = block_hash;

            // continue
            next_hash = header.parent_hash;
        }

        Ok((
            eth_block,
            geth_traces,
            history_hashes,
            prev_state_root.unwrap_or_default(),
        ))
    }

    /// Step 2. Get State Accesses from TxExecTraces
    pub fn get_state_accesses(
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<AccessSet, Error> {
        get_state_accesses(eth_block, geth_traces)
    }

    /// Step 3. Query geth for all accounts, storage keys, and codes from
    /// Accesses
    pub async fn get_state(
        &self,
        block_num: u64,
        access_set: AccessSet,
    ) -> Result<
        (
            Vec<eth_types::EIP1186ProofResponse>,
            HashMap<Address, Vec<u8>>,
        ),
        Error,
    > {
        let mut proofs = Vec::new();
        for (address, key_set) in access_set.state {
            let mut keys: Vec<Word> = key_set.iter().cloned().collect();
            keys.sort();
            let proof = self
                .cli
                .get_proof(address, keys, (block_num - 1).into())
                .await
                .unwrap();
            proofs.push(proof);
        }
        let mut codes: HashMap<Address, Vec<u8>> = HashMap::new();
        for address in access_set.code {
            let code = self
                .cli
                .get_code(address, (block_num - 1).into())
                .await
                .unwrap();
            codes.insert(address, code);
        }
        Ok((proofs, codes))
    }

    /// Step 4. Build a partial StateDB from step 3
    pub fn build_state_code_db(
        proofs: Vec<eth_types::EIP1186ProofResponse>,
        codes: HashMap<Address, Vec<u8>>,
    ) -> (StateDB, CodeDB) {
        build_state_code_db(proofs, codes)
    }

    /// Step 5. For each step in TxExecTraces, gen the associated ops and state
    /// circuit inputs
    pub fn gen_inputs_from_state(
        &self,
        sdb: StateDB,
        code_db: CodeDB,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
        history_hashes: Vec<Word>,
        prev_state_root: Word,
    ) -> Result<CircuitInputBuilder<FixedCParams>, Error> {
        let block = Block::new(self.chain_id, history_hashes, prev_state_root, eth_block)?;
        let mut builder = CircuitInputBuilder::new(sdb, code_db, block, self.circuits_params);
        builder.handle_block(eth_block, geth_traces)?;
        Ok(builder)
    }

    /// Perform all the steps to generate the circuit inputs
    pub async fn gen_inputs(
        &self,
        block_num: u64,
    ) -> Result<
        (
            CircuitInputBuilder<FixedCParams>,
            eth_types::Block<eth_types::Transaction>,
        ),
        Error,
    > {
        let (eth_block, geth_traces, history_hashes, prev_state_root) =
            self.get_block(block_num).await?;
        let access_set = Self::get_state_accesses(&eth_block, &geth_traces)?;
        let (proofs, codes) = self.get_state(block_num, access_set).await?;
        let (state_db, code_db) = Self::build_state_code_db(proofs, codes);
        let builder = self.gen_inputs_from_state(
            state_db,
            code_db,
            &eth_block,
            &geth_traces,
            history_hashes,
            prev_state_root,
        )?;
        Ok((builder, eth_block))
    }
}
