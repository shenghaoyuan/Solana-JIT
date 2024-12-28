theory rBPFSem
imports
    Main
    rBPFCommType rBPFSyntax Mem
begin

type_synonym reg_map = "bpf_ireg \<Rightarrow> u64"


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
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case bop of
  BPF_ADD   \<Rightarrow> Some (rs#dst <-- (dv+sv)) |
  _ \<Rightarrow> None
)))"

fun sbpf_step :: "ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_step prog (SBPF_OK pc rs m) = (
  if length prog = 0 then SBPF_Err
  else (
    case prog!(unat pc) of
    BPF_ALU64 bop d sop \<Rightarrow> (
      case bop of
      BPF_ADD \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m
      ) |
    _ \<Rightarrow> SBPF_Err) |
    BPF_EXIT \<Rightarrow> SBPF_Success (rs BR0) |
    _ \<Rightarrow> SBPF_Err
))" |
"sbpf_step _ _ = SBPF_Err"

fun sbpf_sem :: "nat \<Rightarrow> ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_sem 0 _ st = st" |
"sbpf_sem (Suc n) prog st = sbpf_sem n prog (sbpf_step prog st)"

end