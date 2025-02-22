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
  let nsp =  (rs SP) + (u64_of_memory_chunk chunk) in
    case Mem.loadv M64 m (Vlong nsp) of
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
      case Mem.loadv chunk m (Vptr sp_block addr) of
        None \<Rightarrow> Stuck |
        Some x => 
          (case x of Vlong v \<Rightarrow> let rs1 =rs # SP <- nsp  in
          Next (pc + sz) (rs1#rd <- v ) m |
                     _ \<Rightarrow> Stuck)
)"

definition exec_push :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> usize \<Rightarrow> outcome" where
"exec_push pc sz chunk m rs v = ( 
  let nsp = (rs SP) - (u64_of_memory_chunk chunk) in
      case Mem.storev chunk m (Vptr sp_block nsp) (Vlong v) of
        None \<Rightarrow> Stuck |
        Some m' => Next (pc + sz) (rs#SP <- nsp) m'
)"

definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i sz pc rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  Paddq_rr  rd r1 \<Rightarrow> Next (pc + sz) (rs#rd <- ((rs rd) + (rs r1))) m |
  Pret            \<Rightarrow> exec_ret M64 m rs |
  Ppopl     rd    \<Rightarrow> exec_pop pc sz M64 m rs rd |
  Ppushl_r  r1    \<Rightarrow> exec_push pc sz M64 m rs (rs r1) |
  Pmovq_rr rd r1  \<Rightarrow> Next (pc + sz) (rs#rd <- (rs r1)) m |
  Pmulq_r   r1    \<Rightarrow> let rs1 = rs#RAX <- ((rs RAX)*(rs r1)) in
                     Next (pc + sz) (rs1# RDX <-( (rs RAX)*(rs r1) div (2 ^ 32))) m 
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

lemma x64_sem_add_stuck : 
" x64_sem (m + n) x64_prog Stuck = xst' \<Longrightarrow>
  x64_sem n x64_prog (x64_sem m x64_prog Stuck) = xst'"
  apply (cases m,simp)
  subgoal for m
    apply(cases n,simp)                
    by auto
  done

lemma x64_sem_add: 
  "x64_sem (m+n) x64_prog xst = xst' \<Longrightarrow>
    xst = (Next pc rs ms) \<Longrightarrow>
    \<exists> xst1.
    x64_sem m x64_prog xst = xst1 \<and> 
    x64_sem n x64_prog xst1 = xst'"
  apply (induction m arbitrary: n x64_prog xst xst' pc rs ms)
  subgoal by simp
  subgoal for m n x64_prog xst xst' pc rs ms
    apply simp
    apply (cases "x64_decode (unat pc) x64_prog"; simp)
    subgoal by (cases n; simp)
    subgoal for ins1
      apply (cases ins1; simp)
      subgoal for sz ins
        apply (cases "(exec_instr ins (word_of_nat sz) pc rs ms)"; simp)
        apply (erule x64_sem_add_stuck)
        done
      done
    done
  done


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


type_synonym x64_state = outcome



end
