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
      case Mem.loadv chunk m (Vptr 1 addr) of
        None \<Rightarrow> Stuck |
        Some x => 
          (case x of Vlong v \<Rightarrow> let rs1 =rs # SP <- nsp  in
          Next (pc + sz) (rs1#rd <- v ) m |
                     _ \<Rightarrow> Stuck)
)"

definition exec_push :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> usize \<Rightarrow> outcome" where
"exec_push pc sz chunk m rs v = ( 
  let nsp = (rs SP) - (u64_of_memory_chunk chunk) in
      case Mem.storev chunk m (Vptr 1 nsp) (Vlong v) of
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



fun interp3 :: "instruction list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp3 [] s = s" |
"interp3 (ins#l) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next pc rs m \<Rightarrow> 
    interp3 l (exec_instr ins 1 pc rs m)
)"

fun interp2 :: "instruction list \<Rightarrow> nat list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp2 [] _ s = s" |
"interp2 _ [] s = s" |
"interp2 (ins#l) (x#xs) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next pc rs m \<Rightarrow> 
    interp2 l xs (exec_instr ins (of_nat x) pc rs m)
)"

fun interp1 :: "(nat \<times> instruction) list \<Rightarrow> outcome \<Rightarrow> outcome" where
"interp1 [] s = s" |
"interp1 (x#xs) st = (
  case st of
  Stuck \<Rightarrow> Stuck |
  Next pc rs m \<Rightarrow> 
    let sz = fst x; ins = snd x in
    interp1 xs (exec_instr ins (of_nat sz) pc rs m)
)"

definition x64_sem2 :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem2 num l st = 
  (case st of Stuck \<Rightarrow> Stuck |
     (Next pc rs m) \<Rightarrow>
      (case x64_decodes_aux num (unat pc) l of
          None \<Rightarrow> Stuck |
          Some xs \<Rightarrow> interp1 xs st
))"

(*
"x64_sem 0 _ st = st" 
"x64_sem _ _ Stuck = Stuck" 

definition x64_sem2 :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem2 num l st = 
  (case st of Stuck \<Rightarrow> Stuck |
     (Next pc rs m) \<Rightarrow>
      (case x64_decodes_aux num (unat pc) l of
          None \<Rightarrow> Stuck |
          Some xs \<Rightarrow> interp3 (map snd xs) st
))"
*)

(*
definition corr_state:: "outcome \<Rightarrow> outcome \<Rightarrow> bool" where
"corr_state bst1 bst2 \<equiv> 
  (case bst1 of
      Next xpc xrs xm \<Rightarrow>
        (case bst2 of 
           Next xpc2 xrs2 xm2 \<Rightarrow>
            (xrs = xrs2) \<and> xm = xm2 |
           _ \<Rightarrow> False)|
      _ \<Rightarrow> False)"

definition match_stack :: "regset \<Rightarrow> mem \<Rightarrow> bool" where
"match_stack xrs m = (
  \<exists> v. Mem.loadv M64 m (Vptr 1 ((xrs SP) + (u64_of_memory_chunk M64))) = Some v)" (* v of Vlong or Vint?*)
*)

(*
lemma interp1_increase_pc:
  "interp1 [ins] (Next pc rs m) = (Next pc1 rs1 m1 ) \<Longrightarrow>
  pc1 = pc + of_nat (fst ins)"
  using exec_instr_def apply(cases "(Next pc rs m)",simp_all)
  subgoal for x11 apply(unfold exec_instr_def Let_def)
    apply(cases "snd ins",simp_all)
      apply(unfold exec_ret_def Let_def)
    apply(cases "loadv M64 m (rs SP + u64_of_memory_chunk M64)",simp_all)
    subgoal for a apply(cases a,simp_all)
      sorry
    subgoal for x3 apply(unfold exec_push_def Let_def)
      by(cases "storev M64 m (rs SP - u64_of_memory_chunk M64) (Vlong (rs x3))",simp_all)
    subgoal for x4 apply(unfold exec_pop_def Let_def)
      apply(cases "loadv M64 m (rs SP)",simp_all)
      subgoal for a by(cases a,simp_all)
      done
    done
  done

(*lemma x64_decodes_aux_induct3:"
  x64_decode (unat pc) xs = Some res1 \<Longrightarrow>
  len = (fst res1) \<Longrightarrow>
  x64_decodes_aux n (unat (pc + of_nat len)) xs = Some res2 \<Longrightarrow>
  x64_decodes_aux n (unat pc) (drop len xs) = Some res3 \<Longrightarrow> 
  res2 = res3"
  sorry
*)

lemma x64_decodes_aux_induct3:"
  x64_decode (unat pc) xs = Some res1 \<Longrightarrow>
  len = (fst res1) \<Longrightarrow>
  x64_decodes_aux n (unat (pc + of_nat len)) xs = 
  x64_decodes_aux n (unat pc) (drop len xs) "
  sorry


lemma x64_sem2_induct_aux1:
  "x64_sem2 (Suc num) l st = Next pc' rs' m' \<Longrightarrow>
   x64_sem2 1 l st = st' \<Longrightarrow>
   x64_sem2 num l st' = Next pc' rs' m' "
proof-
  assume a0:"x64_sem2 (Suc num) l st = Next pc' rs' m'" and
    a1:"x64_sem2 1 l st = st'"
  have b0:"st \<noteq> Stuck" using a0 x64_sem2_def by auto
  have "\<exists> pc rs m. Next pc rs m = st" using b0 by (metis outcome.exhaust)
  then obtain pc rs m where b1:"Next pc rs m = st" by auto
  have "x64_sem2 (Suc num) l st = Next pc' rs' m' \<longrightarrow> x64_decodes_aux (Suc num) (unat pc) l \<noteq> None" 
    using x64_sem2_def
    apply(cases st) using b1
    apply(cases "x64_decodes_aux (Suc num) (unat pc) l",simp_all) 
    apply auto[1] by auto
  hence b2:"x64_decodes_aux (Suc num) (unat pc) l \<noteq> None" using a0 by blast

  have "\<exists> res. Some res = x64_decodes_aux (Suc num) (unat pc) l"
    by (meson b2 option.collapse)
  then obtain res where b3:"Some res = x64_decodes_aux (Suc num) (unat pc) l" by auto
  have b4:"x64_decode (unat pc) l \<noteq> None"
    by (metis (no_types, lifting) b2 option.simps(4) x64_decodes_aux.simps(2))
  hence "\<exists> res1. x64_decode (unat pc) l = Some res1" by blast
  then obtain res1 where b4:"x64_decode (unat pc) l = Some res1" by auto
  let "?len" = "fst res1"
  have "\<exists> res2. x64_decodes_aux num (unat pc) (drop ?len l) = Some res2 \<and> res = res1#res2"
    using x64_decodes_aux_induct2 b3 b4 by auto
  then obtain res2 where b5:"x64_decodes_aux num (unat pc) (drop ?len l) = Some res2 \<and> res = res1#res2" by auto

  have c0:"x64_sem2 1 l st = interp1 [res1] st" using b4 x64_sem2_def b1 by auto
  have c1:"st' \<noteq> Stuck" using a0 sorry
  have c1_1:"interp1 [res1] st = st'" using c0 a1 by simp


  have "\<exists> pc1 rs1 m1. Next pc1 rs1 m1 = st'" using c1 by (metis outcome.exhaust)
  then obtain pc1 rs1 m1 where c2_1:"Next pc1 rs1 m1 = st'" by auto
  have c2_2:"pc1 = pc + of_nat (fst res1)" using interp1_increase_pc b1 c2_1 b4 c1_1 by auto
  (*have "x64_decodes_aux num (unat pc) (drop ?len l) \<noteq> None" sorry*)
  hence c2_3:"x64_decodes_aux num (unat pc1) l = x64_decodes_aux num (unat pc) (drop ?len l)" 
    using x64_decodes_aux_induct3 c2_2 b4 b5 by blast
  have c2_4:"x64_sem2 num l st' = 
      (case x64_decodes_aux num (unat pc1) l of
          None \<Rightarrow> Stuck |
          Some xs \<Rightarrow> interp1 xs st')" using x64_sem2_def c2_1 by auto 
  hence "x64_sem2 num l st' =  (case x64_decodes_aux num (unat pc) (drop ?len l) of
          None \<Rightarrow> Stuck |
          Some xs \<Rightarrow> interp1 xs st')" using c2_3 by simp
  hence c2:"x64_sem2 num l st' =  interp1 res2 st'" using b5 by simp
  have c3:"x64_sem2 (Suc num) l st = interp1 res st" using b1 b3 by (metis option.case(2) outcome.simps(4) x64_sem2_def)
  have c4:"interp1 res2 (interp1 [res1] st) = interp1 (res1#res2) st" using b1 by force
  thus ?thesis using c0 c1 c1_1 c2 c3 c4 a0 b5 by argo
qed


lemma x64_sem2_induct:
  "x64_sem2 (Suc num) l st = st2 \<Longrightarrow>
  \<exists> st'. x64_sem2 1 l st = st' \<and> x64_sem2 num l st' = st2"
  using x64_sem2_induct_aux1 sorry


lemma x64_sem_and_sem2_match_reg_and_mem:
 "x64_sem num l st = Next pc1 rs1 m1 \<Longrightarrow>
  x64_sem2 num l st = Next pc2 rs2 m2  \<Longrightarrow>
  pc1 = pc2 \<and> rs1 = rs2 \<and> m1 = m2"
proof(induct num arbitrary: l st pc1 rs1 m1 pc2 rs2 m2)
  case 0
  then show ?case using x64_sem2_def by simp
next
  case (Suc num)
  assume assm1:"x64_sem (Suc num) l st = Next pc1 rs1 m1" and
         assm2:"x64_sem2 (Suc num) l st = Next pc2 rs2 m2" 
  have b0_1:"st \<noteq> Stuck" using assm1 by auto
  have b0_2:"\<exists> pc rs m. Next pc rs m = st" using b0_1 by (metis outcome.exhaust)
  then obtain pc rs m where b0_3:"Next pc rs m = st" by auto
  have "x64_sem2 (Suc num) l st = Next pc2 rs2 m2 \<longrightarrow> x64_decodes_aux (Suc num) (unat pc) l \<noteq> None" 
    using x64_sem2_def
    apply(cases st) using b0_3
    apply(cases "x64_decodes_aux (Suc num) (unat pc) l",simp_all) 
    apply auto[1] by blast
  hence b0:"x64_decodes_aux (Suc num) (unat pc) l \<noteq> None" using assm2 by blast

  have "\<exists> res. Some res = x64_decodes_aux (Suc num) (unat pc) l"
    by (meson b0 option.collapse)
  then obtain res where b1_0:"Some res = x64_decodes_aux (Suc num) (unat pc) l" by auto
  have "x64_decode (unat pc) l \<noteq> None" using assm1 b0_3 apply(cases "x64_decode (unat pc) l")  
    apply simp 
    apply auto[1]
    by blast
  hence "\<exists> res1. x64_decode (unat pc) l = Some res1" by blast
  then obtain res1 where b1_1:"x64_decode (unat pc) l = Some res1" by auto
  let "?len" = "fst res1"
  have "\<exists> res2. x64_decodes_aux num (unat pc) (drop ?len l) = Some res2 \<and> res = res1#res2"
    using x64_decodes_aux_induct2 b1_0 b1_1 by auto
  then obtain res2 where b1:"x64_decodes_aux num (unat pc) (drop ?len l) = Some res2 \<and> res = res1#res2" by auto

  have b2_0:"res = res1#res2" using b1 by blast
  have b2_1:"interp1 res st = Next pc2 rs2 m2"
    using assm2 x64_sem2_def b1_0
    by (metis b0_3 option.simps(5) outcome.simps(4))
  let "?st'" = "interp1 [res1] st"
  have b2_2:"interp1 res2 ?st' = Next pc2 rs2 m2" using b1
    using b0_3 b2_1 by force
  have b2_3:"?st' \<noteq> Stuck" using b2_2 apply(cases ?st',simp_all)
    apply(cases st,simp_all)
    subgoal for x11 x12 x13 apply(unfold exec_instr_def)
      apply(cases "snd res1",simp_all)
      apply (metis interp1.elims outcome.simps(3) outcome.simps(5))
       apply (metis interp1.elims outcome.simps(3) outcome.simps(5))
      by (metis interp1.elims outcome.simps(3) outcome.simps(5))
    using b0_1 by auto

  (*have "?st' = x64_sem 1 l st" using assm1 b0_3 
    by (metis (mono_tags, lifting) One_nat_def b1_1 case_prod_beta interp1.simps(1) interp1.simps(2) option.simps(5) outcome.simps(4) x64_sem.simps(1) x64_sem.simps(3))*)

  have c0_1:"?st' = x64_sem2 1 l st" using b0_3 assm2 b1_1 x64_sem2_def by fastforce
  let "?st2'" = "(exec_instr (snd res1) (of_nat (fst res1)) pc rs m)"
  have c0_2:"?st2' = x64_sem 1 l st" using assm1 b0_3 b1_1
    by (metis (mono_tags, lifting) One_nat_def case_prod_beta option.simps(5) x64_sem.simps(1) x64_sem.simps(3))
  have c0:"x64_sem2 1 l st = x64_sem 1 l st" using b0_3 c0_1 c0_2 by fastforce

  have c1_1:"x64_sem num l ?st2' = Next pc1 rs1 m1" using assm1 b1_1
    by (metis (no_types, lifting) b0_3 case_prod_conv option.simps(5) split_pairs x64_sem.simps(3))
  have c1_2:"x64_sem2 num l ?st' = Next pc2 rs2 m2" 
    using x64_sem2_induct assm2 b2_2 b1 x64_sem2_def b2_3 c0_1 by force
  have "pc1 = pc2 \<and> rs1 = rs2 \<and> m1 = m2" using c1_1 c1_2 Suc.hyps c0 c0_1 c0_2 by auto
  then show ?case by simp
qed

(*lemma x64_sem_and_sem2_match_reg_and_mem2:
 "x64_sem num l st = st1 \<Longrightarrow>
  x64_sem2 num l st = st2  \<Longrightarrow>
  st1 = Stuck \<longrightarrow> st2 = Stuck"
  sorry*)

(*lemma x64_sem_and_sem2_corr_state:
  "x64_sem num l st = st1 \<Longrightarrow>
  x64_sem2 num l st = st2  \<Longrightarrow>
  corr_state st1 st2"
  using corr_state_def x64_sem_and_sem2_match_reg_and_mem
  apply(cases "st1",simp_all)
   apply(cases "st2",simp_all)
  subgoal for pc1 rs1 m1*)

lemma x64_sem_and_sem2_corr_state:
  "x64_sem num l st = Next pc1 rs1 m1 \<Longrightarrow>
  x64_sem2 num l st = Next pc2 rs2 m2  \<Longrightarrow>
  corr_state (Next pc1 rs1 m1) (Next pc2 rs2 m2)"
  using corr_state_def x64_sem_and_sem2_match_reg_and_mem
  by(cases "Next pc1 rs1 m1",simp_all)
*)

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
(*
lemma x64_sem_and_sem2_match_reg_and_mem2:
 "x64_sem num l st = st1 \<Longrightarrow>
  x64_sem2 num l st = st2  \<Longrightarrow>
  st1 = Stuck \<Longrightarrow> st2 = Stuck"
proof(induct num arbitrary: l st st1 st2)
  case 0
  then show ?case using x64_sem2_def by simp
next
  case (Suc num)
  assume assm1:"x64_sem (Suc num) l st = st1" and
         assm2:"x64_sem2 (Suc num) l st = st2" and
         assm3:"st1 = Stuck"
  have b0_1:"st \<noteq> Stuck \<or> st = Stuck" by auto
  thus ?case
  proof(cases "st = Stuck")
    case True
    then show ?thesis using True apply(cases st,simp_all)
      using assm2 x64_sem2_def by auto
  next
    case False
    have b0_2:"\<exists> pc rs m. Next pc rs m = st" using b0_1 False by (metis outcome.exhaust)
    then obtain pc rs m where b0_3:"Next pc rs m = st" by auto
    let "?st'" = "x64_sem 1 l st"
    have b1:"?st' = Stuck \<or> ?st' \<noteq> Stuck" by simp
    thus ?thesis
    proof(cases "?st' = Stuck")
      case True
      have b2:"(x64_decode (unat pc) l = None) \<or> (\<exists> sz ins. x64_decode (unat pc) l = Some(sz,ins) \<and> x64_sem 0 l (exec_instr ins (of_nat sz) pc rs m) = Stuck)" 
        by (metis (mono_tags, lifting) One_nat_def True b0_3 case_prod_beta option.case_eq_if option.exhaust_sel split_pairs x64_sem.simps(3))
      thus ?thesis
      proof(cases "x64_decode (unat pc) l = None")
        case True
        have c0:"x64_decodes_aux (Suc num) (unat pc) l = None" using True apply(cases "x64_decode (unat pc) l") apply simp by auto
        have c1:"x64_sem2 (Suc num) l st = Stuck" using c0 x64_sem2_def apply(cases st,simp_all) using b0_3 by force
        then show ?thesis using assm2 by blast
      next
        case False
        have c0:"(\<exists> sz ins. x64_decode (unat pc) l = Some(sz,ins) \<and> x64_sem 0 l (exec_instr ins (of_nat sz) pc rs m) = Stuck)" using False b2 by auto
        then obtain sz ins where c1:"x64_decode (unat pc) l = Some(sz,ins) \<and> x64_sem 0 l (exec_instr ins (of_nat sz) pc rs m) = Stuck" by auto
        hence c2:"exec_instr ins (of_nat sz) pc rs m = Stuck" by simp
        have c3:"interp1 [(sz,ins)] st = Stuck" using c2 b0_3 by(cases st,simp_all)
        have c4:"x64_decodes_aux 1 (unat pc) l = Some [(sz,ins)]" using c1 by simp
        have c5:"x64_sem2 1 l st = Stuck" using c3 b0_3 x64_sem2_def c4 by(cases st,simp_all) 
        let "?st2'" = "x64_sem2 1 l st"
        have c6:"x64_sem2 num l ?st2' = st2" 
          using x64_sem2_induct assm2 b0_3 by simp
        have c7:"st2 = Stuck" using c6 c5 x64_sem2_def by auto
        then show ?thesis using c6 c7 by blast
      qed
    next
      case False
      have d0:"x64_sem num l ?st' = st1"
        by (metis assm1 b0_3 plus_1_eq_Suc x64_sem_add)
      let "?st2'" = "x64_sem2 1 l st"
      have d0_1:"(x64_decode (unat pc) l \<noteq> None)" using False b0_3  apply(cases st,simp_all) 
        by (smt (verit) option.case_eq_if x64_decode_def) 
      have d1_0:"the (x64_decodes_aux 1 (unat pc) l) = [the (x64_decode (unat pc) l)]" apply(cases "x64_decode (unat pc) l",simp_all)  using d0_1 by fastforce
      have d1:"?st2' \<noteq> Stuck" using x64_sem2_def d0_1 d1_0 apply(cases st,simp_all) apply(cases "x64_decodes_aux 1 (unat pc) l",simp_all) 
        apply auto[1] 
        apply (smt (verit) False One_nat_def b0_3 case_prod_conv interp1.elims list.distinct(1) list.inject option.simps(5) outcome.inject outcome.simps(4) split_pairs x64_sem.simps(1) x64_sem.simps(3))
        apply(cases "x64_decode (unat pc) l",simp_all) 
        subgoal for a 
          apply(cases st,simp_all) using b0_3 by blast 
        done
        have d2:"x64_sem2 num l ?st2' = st2" using x64_sem2_induct assm2 by presburger
      have d3:"?st2' = ?st'" using x64_sem_and_sem2_match_reg_and_mem d1 False
        by (smt (verit, del_insts) outcome.exhaust)
      have "st2 = Stuck" using d0 d1 d2 d3 assm3 by (metis Suc.hyps)
      then show ?thesis by simp
    qed
  qed
qed

lemma interp3_equals_interp1:
  "interp3 (map snd xs) st1 = Next pc1 rs1 m1 \<Longrightarrow> 
  interp1 xs st2 = Next pc2 rs2 m2 \<Longrightarrow>
  st1 = Next x1 rs m \<Longrightarrow>
  st2 = Next y1 rs m \<Longrightarrow>
  rs1 = rs2 \<and> m1 = m2"
proof(induct xs arbitrary:st1 pc1 rs1 m1 st2 pc2 rs2 m2 x1 rs m y1)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume a0:"interp3 (map snd (a # xs)) st1 = Next pc1 rs1 m1" and
  a1:"interp1 (a # xs) st2 = Next pc2 rs2 m2" and
  a2:"st1 = Next x1 rs m" and
  a3:"st2 = Next y1 rs m"

  let "?res1" = "interp1 [a] (Next y1 rs m)"
  let "?res3" = "interp3 [snd a] (Next x1 rs m)"
  have "?res3 \<noteq> Stuck" using a0 by (smt (verit, best) a2 interp3.elims list.distinct(1) list.inject list.simps(9) outcome.distinct(1) outcome.simps(4) outcome.simps(5))
  hence "\<exists> pc' rs' m'. Next pc' rs' m' = interp3 [snd a] (Next x1 rs m)"  by (metis outcome.exhaust)
  then obtain pc' rs' m' where c0:"Next pc' rs' m' = interp3 [snd a] (Next x1 rs m)" by auto
  have "?res1 \<noteq> Stuck" using a0 
    by (smt (verit) Cons.prems(2) a3 interp1.elims list.distinct(1) list.sel(3) nth_Cons_0 outcome.simps(3) outcome.simps(4) outcome.simps(5))
  hence "\<exists> pc'' rs'' m''. Next pc'' rs'' m'' = interp1 [a] (Next y1 rs m)"  by (metis outcome.exhaust)
  then obtain pc'' rs'' m'' where c1:"Next pc'' rs'' m'' = interp1 [a] (Next y1 rs m)" by auto
  have c2:"rs' = rs'' \<and> m' = m''" using c1 c0 a2 a3 apply(cases st1,simp_all) apply(cases st2,simp_all)
    subgoal for x11 apply(unfold exec_instr_def)
      apply(cases "snd a",simp_all)
        apply(unfold exec_ret_def Let_def)
        apply(cases "loadv M64 m (rs SP + u64_of_memory_chunk M64)",simp_all)
      subgoal for aa by(cases aa,simp_all)
      subgoal for x3 apply(unfold exec_push_def Let_def)
        by(cases "storev M64 m (rs SP - u64_of_memory_chunk M64) (Vlong (rs x3))",simp_all)
      subgoal for x4 apply(unfold exec_pop_def Let_def)
        apply(cases "loadv M64 m (rs SP)",simp_all)
        subgoal for aa by(cases aa,simp_all)
        done
      done
    done
  have d0:"interp3 (map snd xs) (Next pc' rs' m') = Next pc1 rs1 m1" using a0 c0 Cons.prems(3) by auto
  have d1:"interp1 xs (Next pc'' rs'' m'') = Next pc2 rs2 m2" using a1 c1 Cons.prems(4) by auto
  have "rs1 = rs2 \<and> m1 = m2" using Cons d0 d1 a0 a1 a2 a3 using c2 by blast
  then show ?case by auto
qed

lemma interp1_and_interp3_corr_state:
  "interp3 (map snd xs) st1 = Next pc1 rs1 m1 \<Longrightarrow> 
  interp1 xs st2 = Next pc2 rs2 m2 \<Longrightarrow>
  st1 = Next x1 rs m \<Longrightarrow>
  st2 = Next y1 rs m \<Longrightarrow>
  corr_state (Next pc1 rs1 m1) (Next pc2 rs2 m2)"
  using corr_state_def interp3_equals_interp1
  by(cases "Next pc1 rs1 m1",simp_all)


lemma interp3_equals_interp1_2:
 "interp3 (map snd xs) st1 = st1' \<Longrightarrow>
  interp1 xs st2 = st2'  \<Longrightarrow>
  st1 = Next x1 rs m \<Longrightarrow>
  st2 = Next y1 rs m \<Longrightarrow>
  st2' = Stuck \<Longrightarrow> st1' = Stuck"
proof(induct xs arbitrary:st1 st1' st2 st2' x1 rs m y1)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume a0:"interp3 (map snd (a # xs)) st1 = st1'" and
  a1:"interp1 (a # xs) st2 = st2'" and
  a2:"st1 = Next x1 rs m" and
  a3:"st2 = Next y1 rs m" and
  a4:"st2' = Stuck"

  let "?res1" = "interp1 [a] (Next y1 rs m)"
  let "?res3" = "interp3 [snd a] (Next x1 rs m)"
  have "?res1 = Stuck \<or> ?res1 \<noteq> Stuck" by simp
  thus ?case
  proof(cases "?res1 = Stuck")
    case True
    have b0:"?res3 = Stuck" 
      apply(cases a,simp_all) 
      apply(unfold exec_instr_def)subgoal for aa b apply(cases b,simp_all)
        using True exec_instr_def apply auto[1] 
            apply(unfold exec_ret_def Let_def) 
            apply(cases "loadv M64 m (rs SP + u64_of_memory_chunk M64) ",simp_all)
        subgoal for ab apply(cases ab,simp_all)
          subgoal for x5 
            using True exec_instr_def exec_ret_def by fastforce
          done
        subgoal for x3 apply(unfold exec_push_def Let_def)
          apply(cases "storev M64 m (rs SP - u64_of_memory_chunk M64) (Vlong (rs x3))",simp_all)
          using True exec_instr_def exec_push_def by force
        subgoal for x4 apply(unfold exec_pop_def Let_def)
          apply(cases "loadv M64 m (rs SP)",simp_all)
          subgoal for ab apply(cases ab,simp_all)
            subgoal for x5 using True exec_instr_def exec_pop_def by force
            done
          done
        subgoal for x51 x52 using True exec_instr_def by simp
        subgoal for x6 using True exec_instr_def by simp
        done
      done
    have b1:"interp3 (map snd xs) ?res3 = Stuck" using b0 apply(cases ?res3,simp_all) 
            by (metis (no_types, lifting) interp3.elims outcome.simps(5))
    thus ?thesis using Cons.prems(1) Cons.prems(3) by fastforce
  next
    case False
    have c0:"?res1 \<noteq> Stuck" using False by simp
    have "\<exists> pc'' rs'' m''. Next pc'' rs'' m'' = interp1 [a] (Next y1 rs m)" using False by (metis outcome.exhaust)
    then obtain pc'' rs'' m'' where c1:"Next pc'' rs'' m'' = interp1 [a] (Next y1 rs m)" by auto
    have c2:"interp1 xs (Next pc'' rs'' m'') = st2'" using a1 c1 Cons.prems(4) by auto
    have "\<exists> pc' rs' m'. Next pc' rs' m' = interp3 [snd a] (Next x1 rs m)" using c1 
    apply(cases a,simp_all) 
      apply(unfold exec_instr_def)subgoal for aa b apply(cases b,simp_all)
        using False exec_instr_def apply auto[1] 
        subgoal for x3 apply(unfold exec_push_def Let_def)
          apply(cases "storev M64 m (rs SP - u64_of_memory_chunk M64) (Vlong (rs x3))",simp_all)
          using False exec_instr_def exec_push_def done
        subgoal for x4 apply(unfold exec_pop_def Let_def)
          apply(cases "loadv M64 m (rs SP)",simp_all)
          subgoal for ab apply(cases ab,simp_all) done
          done
        done
      done
    then obtain pc' rs' m' where c3:"Next pc' rs' m' = interp3 [snd a] (Next x1 rs m)" by auto
    have c4:"interp3 (map snd xs) (Next pc' rs' m') = st1'" 
      using Cons.prems(1) Cons.prems(3) c3 by auto
    have "st1' = Stuck" using Cons c3 c4 
      by (metis c1 c2 interp3_equals_interp1 list.simps(8) list.simps(9))
    thus ?thesis by blast
  qed
qed

*)

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
