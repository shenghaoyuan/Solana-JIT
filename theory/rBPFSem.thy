theory rBPFSem
imports
    Main
    rBPFCommType rBPFSyntax Mem vm
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

type_synonym func_key = u32

type_synonym func_val = u64

type_synonym func_map = "(func_key, func_val) map"

definition get_function_registry ::"func_key \<Rightarrow> func_map \<Rightarrow> func_val option" where
"get_function_registry key fm = fm key"


definition eval_reg :: "dst_ty \<Rightarrow> reg_map \<Rightarrow> u64" where
"eval_reg dst rs = rs dst"
syntax "_upd_reg" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" ("_ # _ <-- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_upd_reg a b c" => "a(b := c)"

datatype sbpf_state =
  SBPF_OK u64 reg_map mem stack_state (* stack_state SBPFV func_map u64 u64 *) | (**r normal state *)
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
  BPF_SUB   \<Rightarrow> Some (rs#dst <-- (dv-sv)) |
  BPF_MOV   \<Rightarrow> Some (rs#dst <-- (sv)) |
  BPF_OR  \<Rightarrow> Some (rs#dst <-- (or dv sv)) |
  BPF_AND  \<Rightarrow> Some (rs#dst <-- (and dv sv)) |
  BPF_XOR  \<Rightarrow> Some (rs#dst <-- (xor dv sv)) |
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

definition update_stack ::"u64 list \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> stack_state \<Rightarrow> stack_state option" where
  "update_stack caller fp npc ss = (let update1 = call_depth ss +1 in 
  if update1 = max_call_depth then None
   else 
    let frame = \<lparr>caller_saved_registers = caller, frame_pointer = fp, target_pc = npc\<rparr> in
    let update2 = stack_pointer ss;  
         update3 = (call_frames ss)[unat(call_depth ss):= frame] in
    let stack = Some \<lparr> call_depth = update1, stack_pointer = update2,
        call_frames = update3\<rparr> in stack )"

definition push_frame:: "reg_map \<Rightarrow> stack_state \<Rightarrow> u64 \<Rightarrow> stack_state option \<times> reg_map" where
"push_frame rs ss pc = (
  let npc = pc +1 in
  let fp = eval_reg BR10 rs in
  let caller = [eval_reg BR6 rs, eval_reg BR7 rs,
                eval_reg BR8 rs, eval_reg BR9 rs] in
  let stack = update_stack caller fp npc ss in 
       let reg = rs#BR10 <-- (stack_pointer ss) in
          (stack, reg)
)"

(*
definition push_frame:: "reg_map \<Rightarrow> stack_state \<Rightarrow> u64 \<Rightarrow> stack_state option \<times> reg_map" where
"push_frame rs ss pc = (
  let npc = pc +1 in
  let fp = eval_reg BR10 rs in
  let caller = [eval_reg BR6 rs, eval_reg BR7 rs,
                eval_reg BR8 rs, eval_reg BR9 rs] in
  let frame = \<lparr> caller_saved_registers = caller,
                frame_pointer = fp, target_pc = npc\<rparr> in 
  let update1 = call_depth ss +1 in (
    if update1 = max_call_depth then (None, rs)
    else (
      let update2 = stack_pointer ss;  
        update3 = (call_frames ss)[unat(call_depth ss):= frame] in
      let stack = Some \<lparr> call_depth = update1, stack_pointer = update2,
        call_frames = update3\<rparr>;
        reg = rs#BR10 <-- update2 in
          (stack, reg)
)))"*)

(*
definition eval_call_reg :: "src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> u64 \<Rightarrow> 
  (u64 \<times> reg_map \<times> stack_state) option" where
"eval_call_reg src imm rs ss pc = (
 (let pc1 = eval_reg src rs in  
    let (x, rs') = push_frame rs ss pc in
      case x of
      None \<Rightarrow> None |
      Some ss' \<Rightarrow> 
        if pc1 < program_vm_addr then None else (
          let next_pc = (pc1 - program_vm_addr)div (of_nat INSN_SIZE) in 
            Some (next_pc, rs', ss')
)))"*)

definition eval_call_imm :: "src_ty \<Rightarrow> imm_ty \<Rightarrow> reg_map \<Rightarrow> stack_state \<Rightarrow> u64 \<Rightarrow>(u64 \<times> reg_map \<times> stack_state) option" where
"eval_call_imm src imm rs ss pc = (
  let pc_option =
      Some (ucast imm) in
  case pc_option of
  None \<Rightarrow> None |
  Some npc \<Rightarrow> (
    let (x, rs') = push_frame rs ss pc in (
      case x of
      None \<Rightarrow> None |
      Some ss' \<Rightarrow> Some (npc, rs', ss')
    ))
)"

definition pop_frame:: "stack_state \<Rightarrow> CallFrame" where 
"pop_frame ss = (call_frames ss)!(unat (call_depth ss - 1)) "

definition update_stack2 ::"stack_state \<Rightarrow> (u64 \<times> stack_state \<times> u64 list \<times> u64)" where
  "update_stack2 ss = (
  let x = call_depth ss-1 in
  let frame = pop_frame ss in 
  let y = stack_pointer ss in 
  let z = butlast (call_frames ss) in 
  let ss' = \<lparr>call_depth = x, stack_pointer= y, call_frames = z\<rparr> in
  let caller = (caller_saved_registers frame) in
  let pc = target_pc frame in 
  let fp = frame_pointer frame in 
  (pc, ss', caller,fp)) "


definition eval_exit :: "reg_map \<Rightarrow> stack_state \<Rightarrow> (u64 \<times> reg_map \<times> stack_state)" where
"eval_exit rs ss = (
  let (pc, ss', caller,fp) = update_stack2 ss in 
  let rs'= (((((
            rs#BR10 <-- fp)
              #BR9  <-- (caller!(3)))
              #BR8  <-- (caller!(2)))
              #BR7  <-- (caller!(1)))
              #BR6  <-- (caller!(0))) in 
    (pc, rs', ss')
)"
(*
definition eval_exit :: "reg_map \<Rightarrow> stack_state \<Rightarrow> (u64 \<times> reg_map \<times> stack_state)" where
"eval_exit rs ss = (
  let x = call_depth ss-1 in
  let frame = pop_frame ss in
  let rs'= (((((
            rs#BR10 <-- (frame_pointer frame))
              #BR9  <-- ((caller_saved_registers frame)!(3)))
              #BR8  <-- ((caller_saved_registers frame)!(2)))
              #BR7  <-- ((caller_saved_registers frame)!(1)))
              #BR6  <-- ((caller_saved_registers frame)!(0))) in 
  let y = stack_pointer ss in 
  let z = butlast (call_frames ss) in
  let ss' = \<lparr>call_depth = x, stack_pointer= y, call_frames = z\<rparr> in
  let pc = target_pc frame in 
    (pc, rs', ss')
)"*)

(*BPF_JA off \<Rightarrow> SBPF_OK (pc+1+scast off) rs m | *)
fun sbpf_step :: "ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_step prog (SBPF_OK pc rs m ss) = (
  if length prog = 0 then SBPF_Err
  else if unat pc \<ge> length prog \<or> unat pc < 0 then SBPF_Err
  else (
    case prog!(unat pc) of
    BPF_ALU64 bop d sop \<Rightarrow> (
      case bop of
      BPF_ADD \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |
       BPF_SUB \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |
      
      BPF_AND \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |

      BPF_OR \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |

      BPF_XOR \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |

      BPF_MUL \<Rightarrow>(
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |
      BPF_LSH \<Rightarrow> (
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |
      BPF_RSH \<Rightarrow> (
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |
      BPF_ARSH \<Rightarrow> (
        case eval_alu bop d sop rs of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss
      ) |
    _ \<Rightarrow> SBPF_Err) |

    BPF_LDX chk dst sop off \<Rightarrow> (
      case eval_load chk dst sop off rs m of
        None \<Rightarrow> SBPF_Err |
        Some rs' \<Rightarrow> SBPF_OK (pc+1) rs' m ss) |

    BPF_JUMP cond dst snd_op off \<Rightarrow> 
      (case snd_op of (SOImm x) \<Rightarrow> SBPF_Err | SOReg x \<Rightarrow> 
      if eval_jmp cond dst snd_op rs then SBPF_OK (pc+1+scast off) rs m ss
      else SBPF_OK (pc + 1) rs m ss) | 

    BPF_ST chk dst sop off \<Rightarrow> (
      case eval_store chk dst sop off rs m of
        None \<Rightarrow> SBPF_Err |
        Some m' \<Rightarrow> SBPF_OK (pc+1) rs m' ss) |
   
    BPF_CALL_IMM src imm \<Rightarrow> (
    case eval_call_imm src imm rs ss pc of
      None \<Rightarrow> SBPF_Err |
    Some (pc', rs', ss') \<Rightarrow> SBPF_OK pc' rs' m ss') |
    
    BPF_EXIT \<Rightarrow> 
      (if call_depth ss = 0 then SBPF_Success (rs BR0)
      else (let (pc', rs', ss') = eval_exit rs ss in SBPF_OK pc' rs' m ss')) |
    _ \<Rightarrow> SBPF_Err
))" |
"sbpf_step prog _  = SBPF_Err" 

fun sbpf_sem :: "nat \<Rightarrow> ebpf_asm \<Rightarrow> sbpf_state \<Rightarrow> sbpf_state" where
"sbpf_sem 0 _ st = st" |
"sbpf_sem (Suc n) prog st = sbpf_sem n prog (sbpf_step prog st)"

(*
value "sbpf_step [BPF_ALU64 BPF_ADD BR0 (SOReg BR1)] (SBPF_OK 1 (\<lambda> x. 0) init_mem)" 

value "sbpf_sem 0 [BPF_ALU64 BPF_ADD BR0 (SOReg BR1)] (SBPF_OK 1 (\<lambda>x. 0) init_mem)"*)
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