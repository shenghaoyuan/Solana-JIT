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

fun eval_snd_op_i64 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> i64" where
"eval_snd_op_i64 (SOImm i) _ = scast i" |
"eval_snd_op_i64 (SOReg r) rs = scast (rs r)"


fun eval_snd_op_u32 :: "snd_op \<Rightarrow> reg_map \<Rightarrow> u32" where
"eval_snd_op_u32 (SOImm i) _ = ucast i" |
"eval_snd_op_u32 (SOReg r) rs = ucast (rs r)"


definition eval_alu64_aux2 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_alu64_aux2 bop dst sop rs = (
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u32 = and (eval_snd_op_u32 sop rs) 63 in (
  case bop of
  BPF_LSH \<Rightarrow> Some (rs#dst <-- (dv << unat sv)) |  \<comment> \<open> to unat \<close>
  BPF_RSH \<Rightarrow> Some (rs#dst <-- (dv >> unat sv))    \<comment> \<open> to unat \<close>
)))" 

definition eval_alu64_aux3 :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_alu64_aux3 bop dst sop rs = (
  let dv :: i64 = scast (eval_reg dst rs) in (
  let sv :: u32 = and (eval_snd_op_u32 sop rs) 63 in (
  case bop of
  BPF_ARSH \<Rightarrow> Some (rs#dst <-- (ucast (arsh64 dv (unat sv))::u64)) 
)))"


definition eval_alu :: "binop \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> reg_map option" where
"eval_alu bop dst sop rs = (
  case sop of (SOImm x) \<Rightarrow> None | SOReg x \<Rightarrow> 
  let dv :: u64 = eval_reg dst rs in (
  let sv :: u64 = eval_snd_op_u64 sop rs in (
  case bop of
  BPF_ADD   \<Rightarrow> Some (rs#dst <-- (dv+sv)) |
  BPF_MUL   \<Rightarrow> Some (rs#dst <-- (dv*sv)) |
  BPF_LSH   \<Rightarrow>  eval_alu64_aux2 bop dst sop rs |
  BPF_RSH   \<Rightarrow>  eval_alu64_aux2 bop dst sop rs |
  BPF_ARSH  \<Rightarrow>  eval_alu64_aux3 bop dst sop rs |
  _ \<Rightarrow> None
)))"

definition eval_jmp :: "condition \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> reg_map \<Rightarrow> bool" where
"eval_jmp cond dst sop rs = (
  let udv :: u64 = eval_reg dst rs in (
  let usv :: u64 = eval_snd_op_u64 sop rs in (
  let sdv :: i64 = scast udv in (
  let ssv :: i64 = eval_snd_op_i64 sop rs in (
  case cond of
  Eq  \<Rightarrow> udv = usv |
  Gt  \<Rightarrow> udv > usv |
  Ge  \<Rightarrow> udv \<ge> usv |
  Lt  \<Rightarrow> udv < usv |
  Le  \<Rightarrow> udv \<le> usv |
  SEt \<Rightarrow> and udv usv\<noteq>0 |
  Ne  \<Rightarrow> udv \<noteq> usv |
  SGt \<Rightarrow> ssv <s sdv |
  SGe \<Rightarrow> ssv \<le>s sdv |
  SLt \<Rightarrow> sdv <s ssv |
  SLe \<Rightarrow> sdv \<le>s ssv ))))
)"


definition eval_store :: "memory_chunk \<Rightarrow> dst_ty \<Rightarrow> snd_op \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> mem option" where
"eval_store chk dst sop off rs mem = (
  case sop of (SOImm x) \<Rightarrow> None | SOReg x \<Rightarrow> 
  let dv  =  (eval_reg dst rs) in (
  let vm_addr :: u64 = (dv + (scast off)) in (  
  let sv :: u64 = eval_snd_op_u64 sop rs in ( \<comment> \<open> TODO: sv is signed for imm and unsigned for src reg? \<close>
  (storev chk mem (Vlong vm_addr) (memory_chunk_value_of_u64 chk sv))
))))"


definition eval_load :: "memory_chunk \<Rightarrow> dst_ty \<Rightarrow> src_ty \<Rightarrow> off_ty \<Rightarrow> reg_map \<Rightarrow> mem \<Rightarrow> reg_map option" where
"eval_load chk dst sop off rs mem = (
  let sv :: u64 = eval_snd_op_u64 (SOReg sop) rs in (
  let vm_addr :: val = Vlong (sv + (scast off)) in (  
  let v = loadv chk mem vm_addr in (
    case v of 
    None \<Rightarrow> None |
    Some Vundef \<Rightarrow>  None | 
    Some (Vlong v) \<Rightarrow>  Some (rs#dst <-- v) |
    Some (Vint v) \<Rightarrow> Some (rs#dst <-- (ucast v)) |
    Some (Vshort v) \<Rightarrow> Some (rs#dst <-- (ucast v)) |
    Some (Vbyte v) \<Rightarrow> Some (rs#dst <-- (ucast v))
))))"

(*BPF_JA off \<Rightarrow> SBPF_OK (pc+1+scast off) rs m | *)
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
      BPF_LSH \<Rightarrow> (
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m
      ) |
      BPF_RSH \<Rightarrow> (
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m
      ) |
      BPF_ARSH \<Rightarrow> (
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m
      ) |
    _ \<Rightarrow> SBPF_Err) |

    BPF_LDX chk dst sop off \<Rightarrow> (
      case eval_load chk dst sop off rs m of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ) |

    BPF_JUMP cond dst snd_op off \<Rightarrow> 
      (case snd_op of (SOImm x) \<Rightarrow> SBPF_Err | SOReg x \<Rightarrow> 
      if eval_jmp cond dst snd_op rs then SBPF_OK (pc+1+scast off) rs m 
      else SBPF_OK (pc + 1) rs m) | 

    BPF_ST chk dst sop off \<Rightarrow> (
      case eval_store chk dst sop off rs m of
        None \<Rightarrow> SBPF_Err |
        Some m' \<Rightarrow> SBPF_OK (pc+1) rs m' ) |
    
BPF_EXIT \<Rightarrow> SBPF_Success (rs BR0) |
    _ \<Rightarrow> SBPF_Err
))" |
"sbpf_step prog _  = SBPF_Err" 

fun sbpf_sem :: "nat \<Rightarrow> ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_sem 0 _ st = st" |
"sbpf_sem (Suc n) prog st = sbpf_sem n prog (sbpf_step prog st)"


value "sbpf_step [BPF_ALU64 BPF_ADD BR0 (SOReg BR1)] (SBPF_OK 1 (\<lambda> x. 0) init_mem)" 

value "sbpf_sem 0 [BPF_ALU64 BPF_ADD BR0 (SOReg BR1)] (SBPF_OK 1 (\<lambda>x. 0) init_mem)"
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