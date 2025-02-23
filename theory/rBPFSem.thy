theory rBPFSem
imports
    Main
    rBPFCommType rBPFSyntax Mem
begin

type_synonym reg_map = "bpf_ireg \<Rightarrow> u64"

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


definition eval_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_reg dst rs = rs dst"
syntax "_upd_reg" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" ("_ # _ <-- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_upd_reg a b c" => "a(b := c)"

datatype sbpf_state =
  SBPF_OK u64 reg_map mem (* stack_state SBPFV func_map u64 u64 *) | (**r normal state *)
  SBPF_Success u64 |
  SBPF_Err

fun eval_snd_op_u64 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_snd_op_u64 (SOImm i) _ = scast i" |
"eval_snd_op_u64 (SOReg r) rs = rs r"

definition eval_alu :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_alu bop dst sop rs = (
  case sop of (SOImm x) \<Rightarrow> None | SOReg x \<Rightarrow> 
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case bop of
  BPF_ADD   \<Rightarrow> Some (rs#dst <-- (dv+sv)) |
  BPF_MUL   \<Rightarrow> Some (rs#dst <-- (dv*sv)) |
  _ \<Rightarrow> None
)))"

fun sbpf_step :: "ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_step prog (SBPF_OK pc rs m) = (
  if length prog = 0 then SBPF_Err
  else if unat pc \<ge> length prog \<or> unat pc < 0 then SBPF_Err
  else (
    case prog!(unat pc) of
    BPF_ALU64 bop d sop \<Rightarrow> (
      case bop of
      BPF_ADD \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m
      ) |
      BPF_MUL \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m
      ) |
    _ \<Rightarrow> SBPF_Err) |
    BPF_JA off \<Rightarrow> SBPF_OK (pc+1+scast off) rs m | 
    BPF_EXIT \<Rightarrow> SBPF_Success (rs BR0) |
    _ \<Rightarrow> SBPF_Err
))" |
"sbpf_step prog _  = SBPF_Err" 

fun sbpf_sem :: "nat \<Rightarrow> ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_sem 0 _ st = st" |
"sbpf_sem (Suc n) prog st = sbpf_sem n prog (sbpf_step prog st)"


value "sbpf_step [BPF_ALU64 BPF_ADD BR0 (SOReg BR1)] (SBPF_OK 1 (\<lambda> x. 0) Map.empty)" 

value "sbpf_sem 0 [BPF_ALU64 BPF_ADD BR0 (SOReg BR1)] (SBPF_OK 1 (\<lambda>x. 0) Map.empty)"
(*
n = 0
  prog = [BPF_LD_IMM BR0 0 0]
  s = SBPF_OK 1 (\<lambda>x. 0) Map.empty
  s' = SBPF_OK 1 _ _
  pc = 1
  rs = _
  m = _
  pc' = 1
  rs' = _
  m' = _*)
end