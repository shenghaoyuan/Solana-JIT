section \<open> JIT-Per: translate SBPF assembly to IR1 \<close>

text\<open> IR1 is a list-list binary code:
- each SBPF assembly is mapped a list of binary code
    where SBPF_JUMP ofs is set to 0 in the target binary 
- SBPF assembly and IR1 have the same pc value because JIT-Per is one-by-one 

SBPF: 0: BPF_ADD; 1: BPF_SUB; 2: BPF_EXIT

x64:  0:[add...]; 1:[sub...]; 2: [ret...]
 \<close>

theory JITPer
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
   x64DecodeProofAux
  JITPer_add JITPer_mul_rax JITPer_mul_rdx JITPer_exit JITPer_jump

begin


lemma one_step_equiv_proof: 
  assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" 
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
(* \<and> snd xst' = unat (pc+1)*)
proof-
  let "?bpf_ins" = "prog!(unat pc)"
  have b1:"(\<exists> src dst. ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src))
  \<or> (\<exists> src dst x cond. ?bpf_ins = BPF_JUMP cond dst (SOReg src) x)" using a0 a1 a2 a6 aux1 by fast
  obtain src dst x cond where b2:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src) \<or> ?bpf_ins = BPF_JUMP cond dst (SOReg src) x" using b1 by auto
  show ?thesis
  proof (cases "?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src) ")
    case True
      have c0:"?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using True by simp
      have c1:"(bpf_to_x64_reg dst) = RDX \<or> (bpf_to_x64_reg dst) = RAX \<or> (bpf_to_x64_reg dst) \<notin> {RAX, RDX}"  by blast
      then show ?thesis
      proof(cases "(bpf_to_x64_reg dst) = RDX")
        case True   
          then show ?thesis using mulq_one_step_rdx a0 a1 a2 a3 a4 a5 a6 True c1 c0 by blast
        next
        case False
          have c2:"(bpf_to_x64_reg dst) = RAX \<or> (bpf_to_x64_reg dst) \<notin> {RAX, RDX}" using c1 False by simp
          thus ?thesis
        proof (cases "(bpf_to_x64_reg dst) = RAX")
          case True
            then show ?thesis using mulq_one_step_rax a0 a1 a2 a3 a4 a5 a6 False c1 c0 by blast
        next
          case False
            have c3:"(bpf_to_x64_reg dst) \<notin> {RAX, RDX}" using c2 False by blast
            then show ?thesis sorry
        qed   
      qed 
    next
    case False
      have c4:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> (?bpf_ins = BPF_JUMP cond dst (SOReg src) x)" using False b2 by blast
      thus ?thesis 
      proof(cases "(?bpf_ins = BPF_JUMP cond dst (SOReg src) x)")
        case True
          then show ?thesis using True False a0 a1 a2 a3 a4 a5 a6 jump_one_step by blast
        next
        case False
          have c5:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src)" using False c4 by simp
          then show ?thesis using False a0 a1 a2 a3 a4 a5 a6 addq_one_step c5 by blast
      qed
    qed
  qed

lemma x64_sem1_induct_aux1:
 "x64_sem1 (m+n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. x64_sem1 m x64_prog xst = xst1 \<and>
  x64_sem1 n x64_prog xst1 = xst'"
 apply(induct m arbitrary: n x64_prog xst xst' )
   apply auto[1]
  subgoal for m n x64_prog xst xst'
    apply (simp add: Let_def)
    apply(cases xst;simp)
    done
  done

lemma x64_sem1_induct_aux3:
  "x64_sem1 (Suc n) x64_prog xst = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem1 1 x64_prog xst = xst1 \<Longrightarrow> 
  x64_sem1 n x64_prog xst1 = xst'"  
using x64_sem1_induct_aux1
  by (metis plus_1_eq_Suc)


lemma n_steps_equiv_proof_aux:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m');
   xst = (Next xpc xrs xm);
   match_state s (pc,xst);
   jitper prog = Some x64_prog;
   prog \<noteq> [];
   x64_sem1 n x64_prog (pc,xst) = xst' \<rbrakk> \<Longrightarrow>
   match_state s' xst'"
(* \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"*)
proof (induction n arbitrary: prog s s' pc rs m pc' rs' m' xst' xst xpc xrs xm x64_prog xst')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume 
       assm1: "sbpf_sem (Suc n) prog s = s'" and
       assm2:"s = SBPF_OK pc rs m" and
       assm3:"s' = SBPF_OK pc' rs' m'" and
       assm4:"xst = Next xpc xrs xm" and
       assm5:"match_state s (pc,xst)" and
       assm6:"jitper prog = Some x64_prog" and
       assm7:"prog \<noteq> [] " and
       assm9:"x64_sem1 (Suc n) x64_prog (pc,xst) = xst'"
  then obtain s1 where s1_eq: "s1 = sbpf_step prog s" by simp
  have n_step_def:"sbpf_sem n prog s1 = s'" using s1_eq assm1 sbpf_sem_induct
    by (metis sbpf_sem.simps(2))
  have a0:"unat pc < length prog \<and> unat pc \<ge> 0" using assm1 assm3 
    using Suc.prems(2) assm7 pc_scope_aux by blast
  moreover have a1:"\<exists> pc1 rs1 m1. s1 = (SBPF_OK pc1 rs1 m1)"
    by (metis Suc.prems(3) bot_nat_0.not_eq_extremum intermediate_step_is_ok n_step_def sbpf_sem.simps(1) sbpf_state.simps(6))
  obtain pc1 rs1 m1 where a2:"s1 = (SBPF_OK pc1 rs1 m1)" using a1 by auto
  have a3:"m1 = m" using mem_is_not_changed s1_eq assm2 a2 by blast
  
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where a6:"x64_prog!(unat pc) = (num,off,l)" by auto
  have a7:"l = (snd (snd ((x64_prog!(unat pc)))))" using a6 by simp

  have "\<exists> xst1. x64_sem1 1 x64_prog (pc,xst) = (pc1,xst1) \<and> match_state s1 (pc1,xst1)"
    using s1_eq assm2 a2 assm4 assm5 assm6 assm7 one_step_equiv_proof a6 a7 a0 by blast
  then obtain xst1 where a4:"x64_sem1 1 x64_prog (pc,xst) = (pc1,xst1) \<and> match_state s1 (pc1,xst1)" by auto
  hence a4_1:"x64_sem1 1 x64_prog (pc,xst) = (pc1,xst1)" by auto
  have an:"\<exists> xpc1 xrs1 xm1. xst1 = Next xpc1 xrs1 xm1" using a4 by (metis match_s_not_stuck outcome.exhaust)
  then obtain xpc1 xrs1 xm1 where a10:"xst1 = Next xpc1 xrs1 xm1" by auto
  have a5:"match_state s1 (pc1,xst1)" using an match_state_def
    using a10 a2 a4 by fastforce
  have    "sbpf_sem n prog s = s' \<Longrightarrow>
           s = SBPF_OK pc rs m \<Longrightarrow>
           s' = SBPF_OK pc' rs' m' \<Longrightarrow>
           xst = Next xpc xrs xm \<Longrightarrow>
           match_state s (pc, xst) \<Longrightarrow>
           jitper prog = Some x64_prog \<Longrightarrow> 
           prog \<noteq> [] \<Longrightarrow> 
           x64_sem1 n x64_prog (pc, xst) = xst' \<Longrightarrow> 
           match_state s' xst'" using Suc by blast
  
  have "\<exists> xst''. x64_sem1 n x64_prog (pc1, xst1) = xst''" by blast
  then obtain xst'' where b0:"x64_sem1 n x64_prog (pc1, xst1) = xst''" by auto
  hence b1:"xst' = xst''" 
    using x64_sem1_induct_aux1 a2 assm2 s1_eq assm4 assm9 a6 a4 a10 by (metis plus_1_eq_Suc)
  hence "match_state s' xst''"
    using n_step_def a2 assm3 a10 a5 assm6 assm7 Suc b0 by simp
  hence an:"match_state s' xst'" using b1 by simp
  then show ?case using an by auto
qed

lemma n_steps_equiv_proof:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m');
   xst = (Next xpc xrs xm);
   match_state s (pc,xst);
   jitper prog = Some x64_prog;
   prog \<noteq> [] \<rbrakk> \<Longrightarrow>
   \<exists> xst'.  x64_sem1 n x64_prog (pc,xst) = xst' \<and>
   match_state s' xst'"
  using n_steps_equiv_proof_aux
  by blast
                                 
end