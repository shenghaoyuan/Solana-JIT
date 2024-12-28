section \<open> x64 Semantics \<close>

theory x64Semantics
imports
  Main
  rBPFCommType Val Mem x64Syntax
begin

axiomatization x64_decode :: "nat \<Rightarrow> u8 list \<Rightarrow> (nat * instruction) option"

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

definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i sz pc rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  Paddq_rr  rd r1 \<Rightarrow> Next (pc + sz) (rs#rd <- ((rs rd) + (rs r1))) m |
  Pret            \<Rightarrow> exec_ret M64 m rs |
  _               \<Rightarrow> Stuck
)"

fun x64_sem :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem 0 _ st = st" |
"x64_sem _ _ Stuck = Stuck" |
"x64_sem (Suc n) l (Next pc rs m) = (
  case x64_decode (unat pc) l of
  None \<Rightarrow> Stuck |
  Some (sz, ins) \<Rightarrow>
    x64_sem n l (exec_instr ins (of_nat sz) pc rs m)
)"

type_synonym x64_state = outcome

end
