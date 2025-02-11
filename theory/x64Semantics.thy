section \<open> x64 Semantics \<close>

theory x64Semantics
imports
  Main
  rBPFCommType Val Mem x64Syntax x64Disassembler x64Assembler
begin

(*axiomatization x64_decode :: "nat \<Rightarrow> u8 list \<Rightarrow> (nat * instruction) option"*)

text \<open> define our x64 semantics in Isabelle/HOL, following the style of CompCert x64 semantics: https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v  \<close>

type_synonym regset = "ireg \<Rightarrow> u64"

syntax "_pregmap_set" :: "'a => 'b => 'c => 'a" ("_ # _ <- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_pregmap_set a b c" => "(a(b := c))"


fun undef_regs :: "ireg list \<Rightarrow> regset \<Rightarrow> regset" where
"undef_regs [] rs = rs" |
"undef_regs (r#l') rs = undef_regs l' (rs#r <- 0)"

datatype outcome = Next u64 regset mem | Stuck

definition exec_ret :: "memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> outcome" where
"exec_ret chunk m rs = (
  let nsp = (rs SP) + (u64_of_memory_chunk chunk) in
    case Mem.loadv M64 m nsp of
    None \<Rightarrow> Stuck |
    Some ra \<Rightarrow> (
      case ra of
      Vlong v \<Rightarrow> let rs1 = rs#SP <- nsp in
                  Next v rs1 m |
      _ \<Rightarrow> Stuck)
)"

definition exec_pop :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> ireg \<Rightarrow> outcome" where
"exec_pop pc sz chunk m rs rd = (
  let nsp = (rs SP) + (u64_of_memory_chunk chunk) in
    let addr = (rs SP) in
      case Mem.loadv chunk m addr of
        None \<Rightarrow> Stuck |
        Some (Vlong v) => let rs1 = rs#rd <- v in
          Next (pc + sz) (rs1# SP <- nsp) m
)"

definition exec_push :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> usize \<Rightarrow> outcome" where
"exec_push pc sz chunk m rs v = ( 
  let nsp = (rs SP) - (u64_of_memory_chunk chunk) in
      case Mem.storev chunk m nsp (Vlong v) of
        None \<Rightarrow> Stuck |
        Some m' => Next (pc + sz) (rs#SP <- nsp) m'
)"

definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i sz pc rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  Paddq_rr  rd r1 \<Rightarrow> Next (pc + sz) (rs#rd <- ((rs rd) + (rs r1))) m |
  Pret            \<Rightarrow> exec_ret M64 m rs |
  Ppopl     rd    \<Rightarrow> exec_pop pc sz M32 m rs rd |
  Ppushl_r  r1    \<Rightarrow> exec_push pc sz M32 m rs (rs r1) |
  Pmovq_rr rd r1  \<Rightarrow> Next (pc + sz) (rs#rd <- (rs r1)) m |
  Pmulq_r   r1    \<Rightarrow> let rs1 = rs#RAX <- ((rs RAX)*(rs r1)) in
                     Next (pc + sz) (rs1# RDX <-( (rs RAX)*(rs r1) div (2 ^ 32))) m 
)"
(*
definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i pc rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  Paddq_rr  rd r1 \<Rightarrow> Next (pc + 3) (rs#rd <- ((rs rd) + (rs r1))) m |
  Pret            \<Rightarrow> exec_ret M64 m rs |
  Ppopl     rd    \<Rightarrow> exec_pop pc 2 M32 m rs rd |
  Ppushl_r  r1    \<Rightarrow> exec_push pc 2 M32 m rs (rs r1) |
  Pmovq_rr rd r1  \<Rightarrow> Next (pc + 3) (rs#rd <- (rs r1)) m |
  Pmulq_r   r1    \<Rightarrow> let rs1 = rs#RAX <- ((rs RAX)*(rs r1)) in
                     Next (pc + 3) (rs1# RDX <-( (rs RAX)*(rs r1) div (2 ^ 32))) m 
)"
*)
(*
  Pmovq_rr src R11

  Ppushl_r RDX

  RAX=RAX*R11
  RDX=RAX*R11 div 2^32

  Ppopl RDX
*)

(*fun x64_sem :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem 0 _ st = st" |
"x64_sem _ _ Stuck = Stuck" |
"x64_sem (Suc n) l (Next pc rs m) = (
  case x64_decode (unat pc) l of
  None \<Rightarrow> Stuck |
  Some (sz, ins) \<Rightarrow>
    x64_sem n l (exec_instr ins (of_nat sz) pc rs m)
)"
*)

fun x64_sem :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem 0 _ st = st" |
"x64_sem _ _ Stuck = Stuck" |
"x64_sem (Suc n) l (Next pc rs m) = (
  case x64_decode (unat pc) l of
  None \<Rightarrow> Stuck |
  Some (sz, ins) \<Rightarrow>
    x64_sem n l (exec_instr ins (of_nat sz) pc rs m)
)"

fun x64_sem1 :: "nat \<Rightarrow> u64 \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem1 0 _ _ st = (let xst_temp =
   case st of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck in xst_temp )" |
"x64_sem1 (Suc n) pc lt xst = (
  let (num,off,l) = lt!(unat pc) in
  let xst_temp = (
    case xst of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck) in
  let xst' = x64_sem num l xst_temp in (
    x64_sem1 n (pc+off) lt xst'))"

(*
definition init_reg_map :: "regset" where
"init_reg_map = (\<lambda> _. 0) (RAX:= 0b00000011, RBX:= 0b00000001)"

definition init_map::"mem" where
"init_map = Map.empty"

value "init_reg_map RBX"

value "init_reg_map RCX"

value "init_mem 0"

value "x64_sem 2 [0b01001000,0b00000001,0b11011000,0b11000011] (Next (0::u64) (init_reg_map) m)"
value "x64_sem 1 [0b01001000,0b00000001,0b11011000,0b11000011] (Next (0::u64) (init_reg_map) m)"
value "x64_sem 0 [0b01001000,0b00000001,0b11011000,0b11000011] (Next (0::u64) (init_reg_map) m)"

value "x64_sem 1 [0b11000011] (Next (0::u64) (init_reg_map) m)"

value "x64_sem 2 [0b11000011] (Next (0::u64) (init_reg_map) m)"

value "x64_sem1 (2::nat) 1 [((1::nat),(1::u64),[0b01001000,0b00000001,0b11011000]),((1::nat),(1::u64),[0b11000011])] (Next (0::u64) (init_reg_map) m)"

lemma "x64_sem1 (1::nat) 1 [((1::nat),(1::u64),[0b01001000,0b00000001,0b11011000]),((1::nat),(1::u64),[0b11000011])] (Next xpc rs m)  = exec_instr Pret 1 0 rs m "
  using x64_decode_def by simp*)

fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next pc rs m \<Rightarrow> 
    interp3 l (exec_instr ins 1 pc rs m)
)"

(*
fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next pc rs m \<Rightarrow> (
    let x = (x64_encode ins) in
      case x of None \<Rightarrow> Stuck |
                Some res \<Rightarrow> 
          let result = x64_decode 0 res in
              case result of None \<Rightarrow> Stuck |
                             Some res \<Rightarrow> let len = fst res
    in interp3 l (exec_instr ins (of_nat len) pc rs m)
))"



fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next pc rs m \<Rightarrow> (
    let len = (case ins of Pret \<Rightarrow> 1 |
                  Ppopl dst \<Rightarrow> 2 |
                  Ppushl_r dst \<Rightarrow> 2 |
                   _ \<Rightarrow> 3 )
    in interp3 l (exec_instr ins len pc rs m)
))"
*)
value "x64_sem1 0 "

(*definition x64_sem1 ::"nat \<Rightarrow> (nat \<times> x64_bin) list \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem1 pc lt xst \<equiv> (let (fuel,l) = lt!pc in
                       let xst_temp = (case xst of (Next xpc rs m) \<Rightarrow> Next 0 rs m | Stuck \<Rightarrow> Stuck) in
                       let xst' = x64_sem fuel l xst_temp in (xst', pc+1))"*)

value "length [1::nat,2,3]"

(*fun x64_sem1 ::"nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> (outcome \<times> nat)" where
"x64_sem1 pc l Stuck = (Stuck, pc)" |
"x64_sem1 pc l (Next pc rs m) = (case x64_decode (unat pc) l of
  None \<Rightarrow> Stuck |
  Some (sz, ins) \<Rightarrow>
    x64_sem1 n l (exec_instr ins (of_nat sz) pc rs m))"
*)
(*
fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next rs m \<Rightarrow> (
        interp3 l (exec_instr ins 1 rs m)
))"
*)


type_synonym x64_state = outcome

end
