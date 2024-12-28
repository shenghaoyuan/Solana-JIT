theory JIT_def
imports
  Main
  rBPFCommType rBPFSyntax
  x64Syntax
  StepSem
begin



axiomatization x64_encode :: "instruction \<Rightarrow> x64_bin option"

record CallFrame = (*  /// The caller saved registers
    pub caller_saved_registers: [u64; ebpf::SCRATCH_REGS],
*)
caller_saved_registers :: "u64 list"
frame_pointer :: u64
target_pc :: u64

record stack_state = 
call_depth :: u64
stack_pointer :: u64
call_frames :: "CallFrame list"

type_synonym func_key = u32

type_synonym func_val = u64
type_synonym func_map = "(func_key, func_val) map"




end