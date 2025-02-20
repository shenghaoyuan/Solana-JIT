section \<open> A collection of common type of JIT \<close>

theory JIT
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler Proof1
  JITState
begin

definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_exit :: "x64_bin option " where
"per_jit_exit = (
  let ins = Pret in
    x64_encode ins
)"

fun per_jit_ins ::" bpf_instruction \<Rightarrow> x64_bin option"where
"per_jit_ins bins = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  _ \<Rightarrow> None
)"

(*fun jit1 :: "ebpf_asm \<Rightarrow> u8 list \<Rightarrow> usize list \<Rightarrow> (u8 list * usize list) option" where
"jit1 [] l_bin l_pc = Some (l_bin, l_pc)" |
"jit1 (h#t) l_bin l_pc = (
  case per_jit_ins h of
  None \<Rightarrow> None |
  Some ins \<Rightarrow> (
    jit1 t (l_bin @ ins) (l_pc @ [of_nat (length l_bin)])
  )
)"*)

(*fun jit :: "ebpf_asm \<Rightarrow> (u8 list * usize list) option" where
"jit [] = Some ([], [])" |
"jit (h#t) = (
  case jit t of
  None \<Rightarrow> None |
  Some (l_bin, l_pc) \<Rightarrow> (
    case per_jit_ins h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> Some (ins @l_bin, 0#(map (\<lambda> i. i + (of_nat (length ins))) l_pc))
  )
)"
*)

(*
fun jit :: "ebpf_asm \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list option" where
"jit [] = Some []" |
"jit (h#t) = (
  case jit t of
  None \<Rightarrow> None |
  Some l_bin \<Rightarrow> (
    case per_jit_ins h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> Some ((1,1,ins) #l_bin)
  )
)"
*)


fun jit :: "ebpf_asm \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list option" where
  "jit [] = Some []" |
  "jit (h#xs) = (case per_jit_ins h of 
                   None \<Rightarrow> None 
                 | Some x \<Rightarrow> 
                     (case jit xs of 
                        None \<Rightarrow> None 
                      | Some res \<Rightarrow> Some ((1,1,x) # res)))"

(*
fun jit :: "ebpf_asm \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list option" where
"jit [] = Some []" |
"jit (h#xs) = (case per_jit_ins h of None \<Rightarrow> None | Some x \<Rightarrow> Some ((1,1,x) # the (jit xs)))"
*)


definition jit1 :: "ebpf_asm \<Rightarrow> x64_bin list option" where
"jit1 ls \<equiv> if \<exists> s \<in> set ls. per_jit_ins s = None then None else 
  Some ((map the (map per_jit_ins ls)))"


(*definition jit :: "ebpf_asm \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list option" where
"jit ls \<equiv> if \<exists> s \<in> set ls. per_jit_ins s = None then None else 
  let x = 
  in Some ((map the (map per_jit_ins ls)))"
*)

(*definition jit :: "ebpf_asm \<Rightarrow> u8 list list option" where
"jit ls \<equiv> if \<exists> s \<in> set ls. per_jit_ins s = None then None else Some ((map the (map per_jit_ins ls)))"
*)                               
(*
fun jit :: "ebpf_asm \<Rightarrow> u8 list option" where
"jit [] = Some []" |
"jit (h#t) = (
    case per_jit_ins h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> Some (ins @the (jit t))
)"
*)

value "Some ((map the (map per_jit_ins [BPF_ALU64 BPF_ADD BR0 (SOReg BR6),BPF_ALU64 BPF_ADD BR0 (SOReg BR1)])))"

value "jit [BPF_ALU64 BPF_SUB BR0 (SOReg BR6),BPF_EXIT]"


(*lemma "\<forall> s \<in> set ls. per_jit_ins s \<noteq> None \<Longrightarrow> jit ls = Some (concat (map the (map per_jit_ins ls)))"
  apply(cases ls, simp_all)
  subgoal for a list apply(cases a, simp_all)
    subgoal for x91 x92 x93 apply(cases x91,simp_all)
      apply(cases x93, simp_all)
      subgoal for x2 apply (unfold per_jit_add_reg64_1_def)
*)
                 
value "snd (snd ((the (jit [BPF_EXIT,BPF_EXIT]))!(0::nat)))"

value "jit []"

value "jit [BPF_ALU64 BPF_SUB BR0 (SOReg BR6),BPF_ALU64 BPF_ADD BR0 (SOReg BR6)]"

value "jit [BPF_ALU64 BPF_ADD BR0 (SOReg BR6),BPF_ALU64 BPF_SUB BR0 (SOReg BR6)]"

value "jit [BPF_ALU64 BPF_ADD BR0 (SOReg BR6), BPF_ALU64 BPF_ADD BR0 (SOReg BR6), BPF_EXIT]"


value "per_jit_ins (BPF_ALU64 BPF_ADD BR0 (SOReg BR6))"
(**r simulation relation *)
(*
definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> usize list \<Rightarrow> bool" where
"match_state bst xst pc_map = (
  case bst of
  SBPF_OK pc rs m \<Rightarrow> (
    case xst of
      Next xpc xrs xm \<Rightarrow>
        (\<forall> r. (rs r) = xrs (bpf_to_x64_reg r)) \<and> \<comment>\<open> for ALU + MEM + Call \<close>
        pc_map!(unat pc) = xpc \<and>  \<comment>\<open> for Jump \<close>
        m = xm  \<comment>\<open> for MEM + Call \<close> |
      _ \<Rightarrow> False
  ) |
  SBPF_Success v \<Rightarrow>(
    case xst of
    Next xpc xrs xm \<Rightarrow> v = xrs (bpf_to_x64_reg BR0) \<comment>\<open> for EXIT \<close> |
      _ \<Rightarrow> False
  ) |
  _ \<Rightarrow> False
)"
*)

definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> bool" where
"match_state bst xst = (
  case bst of
  SBPF_OK pc rs m \<Rightarrow> (
    case xst of
      Next xpc xrs xm \<Rightarrow>
        (\<forall> r. (rs r) = xrs (bpf_to_x64_reg r)) \<and> \<comment>\<open> for ALU + MEM + Call \<close>
        m = xm  \<comment>\<open> for MEM + Call \<close> |
      _ \<Rightarrow> False
  ) |
  SBPF_Success v \<Rightarrow>(
    case xst of
    Next xpc xrs xm \<Rightarrow> v = xrs (bpf_to_x64_reg BR0) \<comment>\<open> for EXIT \<close> |
      _ \<Rightarrow> False
  ) |
  _ \<Rightarrow> False
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

lemma sbpf_sem_induct: 
  "sbpf_sem (m+n) prog s = s' \<Longrightarrow>
    \<exists> temps.
    sbpf_sem m prog s = temps \<and> 
    sbpf_sem n prog temps = s'"
  apply (induct m arbitrary: n prog s s')
  apply simp_all
  done

lemma sbpf_sem_add: 
  "sbpf_sem (m+n) prog s = s' \<Longrightarrow>
    s = (SBPF_OK pc rs mem) \<Longrightarrow>
    s'\<noteq> SBPF_Err \<Longrightarrow>
    \<exists> temps.
    sbpf_sem m prog s = temps \<and> 
    sbpf_sem n prog temps = s'"
  using sbpf_sem_induct by blast

lemma sbpf_sem_err: 
  "sbpf_sem (m+n) prog s = s' \<Longrightarrow>
    s = SBPF_Err \<Longrightarrow>
    \<exists> temps.
    sbpf_sem m prog s = temps \<and> 
    sbpf_sem n prog temps = s'"
  using sbpf_sem_induct by blast

lemma err_is_still_err:" sbpf_sem x prog SBPF_Err = s' \<Longrightarrow> s' = SBPF_Err "
  apply(induct x, simp)
  by auto

lemma suc_success_is_err:"x > 0 \<Longrightarrow> sbpf_sem x prog (SBPF_Success v) = s' \<Longrightarrow> s' = SBPF_Err "
  apply(induct x, simp)
  using err_is_still_err by force

lemma intermediate_step_is_ok:"sbpf_sem x prog s = s' \<Longrightarrow> x > 0 \<Longrightarrow> s' \<noteq> SBPF_Err \<Longrightarrow> \<exists> pc rs mem. s = (SBPF_OK pc rs mem)"
  apply(induct x arbitrary: prog s s')
  apply simp 
  using err_is_still_err suc_success_is_err
  by (metis sbpf_step.elims)

lemma aluq_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow>
     xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')  \<Longrightarrow>
     Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow>
     reg (bpf_to_x64_reg dst) = rs dst \<Longrightarrow>
     reg (bpf_to_x64_reg src) = rs src \<Longrightarrow>
     reg' (bpf_to_x64_reg dst) = (rs' dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply(cases "prog ! unat pc",simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done


lemma aluq_subgoal_rr_aux2_1:"xins = Paddq_rr dst src \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' r = reg r"
  by (simp add: exec_instr_def)


lemma aluq_subgoal_rr_aux2:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)"
  using aluq_subgoal_rr_aux2_1 by simp


lemma aluq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m') \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow>
  \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases bins,simp_all)
  apply(cases "prog ! unat pc", simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done


lemma addq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and
       a1:"per_jit_add_reg64_1 dst src = Some l_bin" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' m' = exec_instr xins sz spc reg m" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg m) " and
       a7:"prog!(unat pc) = bins"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' m') "
proof -
  have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a3 
    by (metis option.inject prod.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def by simp
    moreover have b2:"(rs src) = reg (bpf_to_x64_reg src)" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (bpf_to_x64_reg dst)" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg ((bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    thus ?thesis using b3 match_state_def by force
  qed


lemma exit_subgoal_rr_generic:
  assumes a0:"bins = BPF_EXIT" and
       a1:"per_jit_exit = Some l_bin" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = st'" and
       a5:"xst' = exec_instr xins sz spc reg m" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg m) " and
       a7:"prog!(unat pc) = bins" and
       a8:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0"
     shows "match_state st' xst'"
proof-
  have b0:"st' = SBPF_Success (rs BR0)" using a0 a4 a7 a8 by simp
  have b1:"xins = Pret" using x64_encode_decode_consistency per_jit_exit_def a0 a1 a3
    by (metis Pair_inject option.inject)
  moreover have b2:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def by simp
  moreover have b3:"(rs BR0) = reg (bpf_to_x64_reg BR0)" using a6 spec b2 by simp
  have b4:"Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) \<noteq> None" sorry
  hence "\<exists> x. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = x \<and> x\<noteq> None" by simp
  hence "\<exists> v. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some v" by simp
  hence b5_1:"\<exists> v. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some (Vlong v)" sorry
  obtain v where b5_2:"Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some (Vlong v)" using b5_1 by blast
  let "?reg'" = "(reg#SP <- ((reg SP) + (u64_of_memory_chunk M64)))"
  have b5_3:"\<exists> reg'. xst' = Next v ?reg' m" using exec_instr_def exec_ret_def a5 b1 b5_2 by simp
  hence b5:"?reg' (bpf_to_x64_reg BR0) = reg (bpf_to_x64_reg BR0)" by (simp add: bpf_to_x64_reg_def)
  thus ?thesis using exec_instr_def b3 b1 b0 a5 using b5_2 exec_ret_def match_state_def by force
qed

lemma aux1:"length prog \<noteq> 0 \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow>
  s = (SBPF_OK pc rs m) \<Longrightarrow> 
  s' = (SBPF_OK pc' rs' m) \<Longrightarrow> 
  \<exists> dst src. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src)"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x91 x92 x93 
   apply(unfold eval_alu_def Let_def)
    apply(cases x91,simp_all) 
    apply(cases x93, simp_all)
    done
  done

lemma aux2:"length prog \<noteq> 0 \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow>
  s = (SBPF_OK pc rs m) \<Longrightarrow> 
  s' \<noteq> SBPF_Err \<Longrightarrow> 
  \<exists> dst src. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> prog!(unat pc) = BPF_EXIT"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x91 x92 x93 
   apply(unfold eval_alu_def Let_def)
    apply(cases x91,simp_all) 
     apply(cases x93, simp_all)
    apply(cases x93, simp_all)
    subgoal for x2  try

    done
  done


lemma aux3:"jit prog = Some x64_prog \<Longrightarrow> length x64_prog = length prog"
proof (induction prog arbitrary: x64_prog)
  case Nil
  then show ?case by simp
next
  case (Cons h xs)
  assume "jit (h # xs) = Some x64_prog"
  then have a0:"\<exists> x. per_jit_ins h = Some x" using Cons(1) by (cases "per_jit_ins h"; auto)
  obtain x where a1:"per_jit_ins h = Some x" using a0 by auto
  then have a2:"\<exists> res. jit xs = Some res" using Cons(1) apply (cases "jit xs"; auto) 
    using Cons.prems(1) by force
  obtain res where a3:"jit xs = Some res" using a2 by auto
  have a4:"x64_prog = (1, 1, x) # res" using Cons(1) a3 a1
    using Cons.prems(1) by force
  then have a5:"length ( x64_prog) = length (h # xs)" using a4 Cons.IH a3 by fastforce
  then show ?case using Cons by simp
qed


value "[2::nat,3]!(unat (0::u64))"

lemma aux4:"jit prog = Some x64_prog \<Longrightarrow> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow> x64_prog!(unat pc) = l_bin \<Longrightarrow> prog \<noteq> [] 
  \<Longrightarrow> Some (snd(snd l_bin)) = per_jit_ins bins"
proof (induction prog arbitrary: x64_prog pc bins l_bin)
  case Nil
  then show ?case by simp
next
  case (Cons a prog)
  then show ?case
  proof-
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have "unat pc = 0" using True a0 by simp
      have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
      then have b2:"\<exists> res. jit prog = Some res" using Cons(1) apply (cases "jit prog"; auto) 
        using Cons.prems(1) by force
      obtain res where b3:"jit prog = Some res" using b2 by auto
      have b4:"x64_prog = (1, 1, x) # res" using Cons(1) b3 b1 Cons by force
      have bn:"Some (snd (snd l_bin)) = per_jit_ins bins" using b1 b2 
        using Cons.prems(3) Cons.prems(4) True b4 by fastforce
      then show ?thesis using bn by blast
    next
      case False
      let "?x" = "the (jit prog)"
      have c0:"\<exists> x. Some ((1, 1, x) # ?x) = Some x64_prog" using Cons 
        by (metis (no_types, lifting) jit.simps(2) option.case_eq_if option.discI)
      have c1:"unat pc \<ge> 1" using a0 False by blast
      have c2:"(a#prog) ! unat pc = bins" using c0 Cons.prems(3) by blast
      let "?pc'" = "unat pc -1"
      have c4:"0 \<le> ?pc' \<and> ?pc' < length prog \<and>
      prog ! ?pc' = bins \<and> ?x ! ?pc' = l_bin \<and> prog \<noteq> []" using Cons.prems(2) Cons.prems(3) Cons.prems(4) c0 c1 by auto
      (* have cn:"0 \<le> unat pc \<and> unat pc < length prog \<Longrightarrow> 
  prog ! unat pc = bins \<Longrightarrow> ?x ! unat pc = l_bin \<Longrightarrow> Some (snd (snd l_bin)) = per_jit_ins bins" using Cons
        by (metis (no_types, lifting) jit.simps(2) option.case_eq_if option.collapse)*)
      have c5:"Some (snd (snd l_bin)) = per_jit_ins bins" using c4 Cons 
        by (metis (no_types, lifting) False jit.simps(2) option.case_eq_if option.collapse option.discI order_neq_le_trans unat_gt_0 unat_minus_one)
      then show ?thesis using c5 by blast
    qed
  qed
qed


(*lemma aux3:"jit prog = x64_prog \<Longrightarrow> x64_prog \<noteq> None \<Longrightarrow> length (the x64_prog) = length prog"
  by (metis length_map option.sel)

lemma aux4:"jit prog = x64_prog \<Longrightarrow> x64_prog \<noteq> None \<Longrightarrow> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow> prog \<noteq> [] \<Longrightarrow>
  prog!(unat pc) = bins \<Longrightarrow> (the x64_prog)!(unat pc) = l_bin 
  \<Longrightarrow> Some l_bin = per_jit_ins bins"
  using jit_def aux3 by (metis (no_types, lifting) list.map_comp map_equality_iff nth_map nth_mem option.collapse option.sel)
*)

lemma demo1: assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m)" and
  a3:"xst = (Next xpc xrs m)" and
  a4:"match_state s xst" and
  a5:"jit prog = Some x64_prog" and
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a7:"xpc = 0" 
shows "\<exists> xst'. let l = (x64_prog!(unat pc)) in x64_sem 1 (snd (snd l)) xst = xst' \<and> 
  match_state s' xst'"
(* \<and> snd xst' = unat (pc+1)*)
proof-
  let "?bpf_ins" = "prog!(unat pc)"
  have b0:"length prog \<noteq> 0" using a6 by blast
  have b1:"\<exists> src dst. ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src)" using a0 a1 a2 a6 b0 aux1 by blast
  obtain src dst where b2:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src)" using b1 by blast
  let "?l_bin"= "the (per_jit_ins ?bpf_ins)"
  have c0:"(?l_bin = the (per_jit_add_reg64_1 dst src))" using b2 by fastforce
  have c1:"Some ?l_bin = x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" using per_jit_add_reg64_1_def c0 by fastforce
  have c2:"snd (snd (x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux4 by (metis option.sel)
  let "?st" = "x64_sem 1 ?l_bin xst"
  have c3:"\<exists> size2 xins2. x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) \<and> ?st = exec_instr xins2 size2 xpc xrs m" using x64_encode_decode_consistency a3 a7 c1 by fastforce
  obtain size2 xins2 where c4:"x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) \<and> ?st = exec_instr xins2 size2 xpc xrs m" using c3 by auto
  have c5:"xins2 = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using Pair_inject c4 c1 option.inject x64_encode_decode_consistency by metis
  have c6:"\<exists> xrs' xpc'. ?st = Next xpc' xrs' m" using exec_instr_def spec c5 c4 by auto
  obtain xrs' xpc' where c7:"?st = Next xpc' xrs' m" using c6 by auto
  have c8:"match_state s' ?st" using addq_subgoal_rr_generic by (metis a0 a1 a2 c7 a4 a3 c1 per_jit_add_reg64_1_def b2 c4)
    show ?thesis using c8 c2 by simp
  qed

lemma match_s_not_stuck:"match_state s xst \<Longrightarrow> xst \<noteq> Stuck"
  apply(cases s, simp_all)
  apply(unfold match_state_def)
  subgoal for x11 x12 x13 by auto
  subgoal for x2 by auto
  by simp

lemma mem_is_not_changed:"s2 = sbpf_step prog s1 \<Longrightarrow> s1 = (SBPF_OK pc1 rs1 m1) \<Longrightarrow> s2 = (SBPF_OK pc2 rs2 m2) \<Longrightarrow> m1 = m2"
  apply(cases "prog!(unat pc1)", simp_all)
  subgoal for x11 x12 x13 
    by (metis bpf_instruction.simps(361) sbpf_state.simps(6))
  subgoal for x21 x22 x23 x24
    by (metis bpf_instruction.simps(362) sbpf_state.simps(6))
  subgoal for x31 x32 x33 x34 
    by (metis bpf_instruction.simps(363) sbpf_state.simps(6))
  subgoal for x4 
    by (metis bpf_instruction.simps(364) sbpf_state.distinct(3))
  subgoal for x51 x52 x53 
    by (metis bpf_instruction.simps(365) sbpf_state.simps(6))
  subgoal for x6 
    by (metis bpf_instruction.simps(366) sbpf_state.simps(6))
  subgoal for x71 x72
    by (metis bpf_instruction.simps(367) sbpf_state.simps(6))
  subgoal for x81 x82
    by (metis bpf_instruction.simps(368) sbpf_state.simps(6))
  subgoal for x91 x92 x93
    apply(split if_splits, simp_all)
    apply(split if_splits, simp_all)
    apply(cases x91, simp_all)
     apply(cases "eval_alu BPF_ADD x92 x93 rs1", simp_all)
    apply(cases "eval_alu BPF_MUL x92 x93 rs1",simp_all)
    done
  subgoal for x10
    by (metis bpf_instruction.simps(370) sbpf_state.simps(6))
  subgoal for x111 x112
    by (metis bpf_instruction.simps(371) sbpf_state.simps(6))
  subgoal for x121 x122 x123
    by (metis bpf_instruction.simps(372) sbpf_state.simps(6))
  subgoal for x131 x132 x133
    by (metis bpf_instruction.simps(373) sbpf_state.simps(6))
  subgoal for x141 x142 x143
    by (metis bpf_instruction.simps(374) sbpf_state.simps(6))
  subgoal for x15
    by (metis bpf_instruction.simps(375) sbpf_state.simps(6))
  subgoal for x161 x162 x163 x164
    by (metis bpf_instruction.simps(376) sbpf_state.simps(6))
  subgoal for x171 x172
    by (metis bpf_instruction.simps(377) sbpf_state.simps(6))
  subgoal for x181 x182
    by (metis bpf_instruction.simps(378) sbpf_state.simps(6))
  by (metis (no_types, lifting) bpf_instruction.simps(379) sbpf_state.distinct(1) sbpf_state.simps(6))             

(*lemma mem_is_not_changed2:"x64_sem 1 l xst1 = xst2 \<Longrightarrow> xst1 = Next xpc1 xrs1 m1 \<Longrightarrow> xst2 = Next xpc2 xrs2 m2 \<Longrightarrow> m1 = m2"
  apply(cases "x64_decode (unat xpc1) l", simp_all)
  subgoal for a apply(cases a, simp_all)
    subgoal for aa b
      apply(unfold exec_instr_def)
      apply (cases b, simp_all)
      apply(unfold exec_ret_def Let_def) 
      apply(cases "loadv M64 m1 (xrs1 SP + u64_of_memory_chunk M64)", simp_all)
      subgoal for ab apply(cases ab, simp_all)
        done
      done
    done
  done*)

lemma demo2:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m);
   xst = (Next xpc xrs m);
   match_state s xst;
   jit prog = Some x64_prog;
   prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0;
   xpc = 0;
   x64_sem1 n pc x64_prog xst = xst' \<rbrakk> \<Longrightarrow>
   match_state s' xst'"
(* \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"*)
proof (induction n arbitrary: prog s s' pc rs m pc' rs' xst' xst xpc xrs x64_prog xst')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume assm1: "sbpf_sem (Suc n) prog s = s'" and
       assm2:"s = SBPF_OK pc rs m" and
       assm3:"s' = SBPF_OK pc' rs' m" and
       assm4:"xst = Next xpc xrs m" and
       assm5:"match_state s xst" and
       assm6:"jit prog = Some x64_prog" and
       assm7:"prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc " and
       assm8:"xpc = 0" and
       assm9:"x64_sem1 (Suc n) pc x64_prog xst = xst'"
  then obtain s1 where s1_eq: "s' = sbpf_step prog s1" 
    by (metis add_Suc_right sbpf_sem.simps(1) sbpf_sem.simps(2) sbpf_sem_induct)
  from Suc have s'_def:"sbpf_sem (Suc n) prog s = s'" by blast
  have one_step_def:"\<exists> s1. sbpf_sem n prog s = s1 \<and> sbpf_step prog s1 = s'" using s1_eq s'_def sbpf_sem_induct
    by (metis add_Suc_right sbpf_sem.simps(1) sbpf_sem.simps(2))
  obtain s1 where get_s1:"sbpf_sem n prog s = s1 \<and> sbpf_step prog s1 = s'" using one_step_def by simp
  have a1:"s1 = sbpf_sem n prog s" using one_step_def s1_eq using get_s1 by force
  have a3:"\<exists> pc1 rs1 m1. s1 = (SBPF_OK pc1 rs1 m1)" 
    by (smt (verit) Suc.prems(3) get_s1 sbpf_state.simps(6) sbpf_step.elims)
  obtain pc1 rs1 m1 where "s1 = (SBPF_OK pc1 rs1 m1)" using a3 by auto
  moreover have "m1 = m" using mem_is_not_changed Suc.prems(3) calculation get_s1 by blast
  hence a4:"s1 = (SBPF_OK pc1 rs1 m)" using calculation by blast
  have "\<exists> xst1. x64_sem1 n pc x64_prog xst = xst1" by blast
  (*have "\<exists> xst1. x64_sem1 n pc x64_prog xst = xst1 \<and> x64_sem 1 (snd (snd ((x64_prog!(unat pc1))))) xst1 = xst'" sorry*)
  then obtain xst1 where a2:"x64_sem1 n pc x64_prog xst = xst1" using a4 by auto
  from Suc.IH have "sbpf_sem n prog s = s' \<Longrightarrow>
           s = SBPF_OK pc rs m \<Longrightarrow>
           s' = SBPF_OK pc' rs' m \<Longrightarrow>
           xst = Next xpc xrs m \<Longrightarrow>
           match_state s xst \<Longrightarrow>
           jit prog = Some x64_prog \<Longrightarrow>
           prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc \<Longrightarrow> xpc = 0 \<Longrightarrow> x64_sem1 n pc x64_prog xst = xst' \<Longrightarrow> 
           match_state s' xst'" by blast
  from Suc have a5:"match_state s1 xst1" using a1 assm2 a4 assm4 assm5 assm6 assm7 assm8 a2 by blast
  have b0:"\<exists> xpc1 xrs1 m2. xst1 = (Next xpc1 xrs1 m2)" using match_s_not_stuck a5 by (meson outcome.exhaust)
  obtain xpc1 xrs1 m2 where "xst1 = (Next xpc1 xrs1 m2)" using b0 by auto
  moreover have "m2 = m" using a4 a5 calculation(2) match_state_def by auto
  hence b2:"xst1 = (Next xpc1 xrs1 m)" using calculation by blast
  have b3:"xpc1 = 0" sorry
  have b4:"unat pc1 < length prog \<and> unat pc1 \<ge> 0" 
    by (metis (no_types, lifting) a4 assm3 get_s1 linorder_not_less sbpf_state.simps(6) sbpf_step.simps(1))
  have b6:"\<exists> xst2. x64_sem 1 (snd (snd ((x64_prog!(unat pc1))))) xst1 = xst2 \<and> match_state s' xst2" 
    using s1_eq a4 assm3 b2 a5 assm6 assm7 b3 demo1 b4 by (metis get_s1)
  obtain xst2 where "x64_sem 1 (snd (snd ((x64_prog!(unat pc1))))) xst1 = xst2 \<and> match_state s' xst2" using b6 by auto
  moreover have "xst2 = xst'" using x64_sem1_induct 
    using a2 assm9 b3 calculation(2) calculation(3) by blast
  then show ?case  using calculation(3) by fastforce
qed


end