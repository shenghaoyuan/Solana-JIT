theory JITPer2
  imports JITPer JITPer2Aux
begin

lemma mulq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_MUL dst (SOReg src)" and
       a1:"per_jit_mul_reg64 dst src = Some (n, off, l_bin)" and
       a3:"x64_decodes_aux n 0 l_bin = Some xins" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = interp3 (map snd xins) (Next spc reg xm)" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg xm) " and
       a7:"prog!(unat pc) = bins" and 
       a8:"(bpf_to_x64_reg dst) = RAX"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' xm') "
proof -
  let "?xins" = "map snd xins"
  have b0:"?xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]"
    using x64_encodes_decodes_consistency per_jit_mul_reg64_def a1 a3 a8 
    by(cases "bpf_to_x64_reg dst",simp_all) 
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def by simp
    moreover have b2:"(rs src) = reg (bpf_to_x64_reg src)" using a6 spec b1 by simp
    moreover have "(rs dst) = reg (bpf_to_x64_reg dst)" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (bpf_to_x64_reg dst)" 
      using mulq_subgoal_rr_aux1 a0 mulq_subgoal_rr_aux1 b0 a5 a8 a0 a4 a7 b2 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 mulq_subgoal_rr_aux2 
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using mulq_subgoal_rr_aux3 a0 a4 a7 by force
     moreover have b6:"\<forall> r \<noteq> dst. (rs r) = reg ((bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg' xm'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed mem_is_not_changed_by_add match_state_def a6
      by (metis (no_types, lifting) a4 a5 b0 outcome.simps(4) sbpf_state.simps(9))
    thus ?thesis using b3 b7 match_state_def b8 b9 by fastforce
  qed


lemma mulq_subgoal_rr_aux2_3:"xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX] \<Longrightarrow> 
  Next pc1 reg1 m1 = exec_instr (Pmulq_r (bpf_to_x64_reg src)) sz pc reg m \<Longrightarrow>
  Next pc2 reg2 m2 = interp3 xins (Next pc reg m) \<Longrightarrow>
  reg1 (bpf_to_x64_reg src) =  reg2 (bpf_to_x64_reg src) "
  apply(unfold exec_instr_def)
  apply(cases "xins ! 2",simp_all)
  subgoal for x6
    apply(cases "exec_instr (Pmovq_rr (bpf_to_x64_reg src) REG_SCRATCH) 1 pc reg m",simp_all)
    subgoal for x11 x12 x13
      apply(cases "exec_instr (Ppushl_r RDX) 1 x11 x12 x13",simp_all)
      subgoal for x11a x12a x13a
        apply(cases "exec_instr (Pmulq_r REG_SCRATCH) 1 x11a x12a x13a",simp_all)
        subgoal for x11b x12b x13b
          apply(unfold exec_instr_def)
          apply(cases "Ppopl RDX",simp_all)
          subgoal for x4 apply(unfold exec_push_def Let_def)
            apply(cases "storev M32 x13 (x12 SP - u64_of_memory_chunk M32) (Vlong (x12 RDX))",simp_all)
            by (simp add: storev_def)
          done
        done
      done
    done
  done


(*lemma mulq_subgoal_rr_aux2_4:
  assumes a0:"xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]" and
  a1:"Next pc' reg' m' = interp3 xins (Next pc reg m)"
  shows "bpf_to_x64_reg src \<notin> {RAX, RDX} \<longrightarrow> reg' (bpf_to_x64_reg src) = reg (bpf_to_x64_reg src)"
proof-
 let "?xins" = "Pmulq_r (bpf_to_x64_reg src)" 
  have "\<exists> result sz. exec_instr ?xins sz pc reg m = result" by blast
  then obtain result sz where b1_1:"exec_instr ?xins sz pc reg m = result" by auto
  have "result \<noteq> Stuck"using exec_instr_def b1_1 by auto
  hence b1:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = exec_instr ?xins sz pc reg m" using b1_1
    by (metis outcome.exhaust)
  then obtain pc1 reg1 m1 where b1:"Next pc1 reg1 m1 = exec_instr ?xins sz pc reg m" by auto
  have b2:"reg1 (bpf_to_x64_reg src) =  reg' (bpf_to_x64_reg src)" using mulq_subgoal_rr_aux2_3 a0 a1 b1 by simp
  have b3:"\<forall> r.  bpf_to_x64_reg r \<notin> {RAX, RDX} \<longrightarrow>reg1 (bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using mulq_subgoal_rr_aux2_2 b1 by simp
  thus ?thesis using b2 b3 by auto
qed*)


lemma mov_does_not_alter_mem_and_SP:
  "xins = Pmovq_rr (bpf_to_x64_reg src) (bpf_to_x64_reg dst) \<Longrightarrow>
   (exec_instr xins sz pc reg m) = Next pc' reg' m' \<Longrightarrow>
  m' = m \<and> reg' SP = reg SP"
  using exec_instr_def reg_rsp_consist by fastforce


lemma mul_does_not_alter_mem_and_SP:
  "xins = Pmulq_r (bpf_to_x64_reg src)   \<Longrightarrow>
   (exec_instr xins sz pc reg m) = Next pc' reg' m' \<Longrightarrow>
  m' = m \<and> reg' SP = reg SP"
  using exec_instr_def reg_rsp_consist by fastforce


lemma mulq_subgoal_rr_aux2_4:
  assumes a0:"xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]" and
  a1:"Next pc' reg' m' = interp3 xins (Next pc reg m)" and
  a2:"(bpf_to_x64_reg src) = RDX"
  shows "reg RDX = reg' RDX"
proof-
  have "\<exists> result1. (exec_instr (xins!0) 1 pc reg m) = result1" by simp
  obtain result1 where b0_1:"(exec_instr (xins!0) 1 pc reg m) = result1" by auto
  have "result1 \<noteq> Stuck" using a0 a1 b0_1 interp3_list_aux1 by blast
  hence "\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = result1"  by (metis outcome.exhaust)
  then obtain pc1 reg1 m1 where b0_2:"Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m)" using b0_1 by auto
  moreover have b0_4:"m1 = m" using mov_does_not_alter_mem_and_SP a0 calculation exec_instr_def by auto
  hence b0:"Next pc1 reg1 m = (exec_instr (xins!0) 1 pc reg m)" using calculation by blast
  let "?xins" = "tl xins"
  have c1:"hd ?xins = Ppushl_r RDX" using a0 a2 by simp
  have c2:"last ?xins = Ppopl RDX" using a0 by simp
  have "\<exists> result2. (exec_instr (xins!1) 1 pc1 reg1 m1) = result2" by simp
  obtain result2 where b1_1:"(exec_instr (xins!1) 1 pc1 reg1 m1) = result2" by auto
  have b1_2:"result2 \<noteq> Stuck" using a0 b1_1
    by (metis One_nat_def b0_2 a1 calculation interp3.simps(2) interp3_list_aux1 list.simps(3) nth_Cons_0 nth_Cons_Suc outcome.simps(4))
  then obtain pc2 reg2 m2 where b1_3:"Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1)" using b1_1 by (metis outcome.exhaust)
  have "\<exists> result3. (exec_instr (xins!2) 1 pc1 reg1 m1) = result3" by simp
  obtain result3 where b2_1:"(exec_instr (xins!2) 1 pc2 reg2 m2) = result3" by auto
  have "result3 \<noteq> Stuck" using a0 b2_1 exec_instr_def by auto
  then obtain pc3 reg3 m3 where b3_0:"Next pc3 reg3 m3 = (exec_instr (xins!2) 1 pc2 reg2 m2)" using b2_1 by (metis outcome.exhaust)
  have b3:"reg3 SP = reg2 SP" using mul_does_not_alter_mem_and_SP a0 exec_instr_def b3_0 by force
  have "m3 = m2" using mul_does_not_alter_mem_and_SP a0 exec_instr_def b3_0 exec_instr_def by simp
  hence b4:"interp3 (butlast(tl ?xins)) (Next pc2 reg2 m2) = Next pc3 reg3 m2" using a0 b3_0 by auto
  have b5:"reg RDX = reg3 RDX" using a0 a1 b3_0 b1_3
    by (simp add: exec_instr_def exec_push_def storev_def)
  have c3:"reg1 RDX = reg' RDX" using exec_instr_def a0 b0_2  b1_2 b1_1 exec_push_def storev_def by auto
  thus ?thesis using c3 b5 by simp
qed


lemma mulq_subgoal_rr_aux2_5:
  "xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX] \<Longrightarrow>
  Next pc' reg' m' = interp3 xins (Next pc reg m) \<Longrightarrow>
  reg RAX = reg' RAX"
  sorry

lemma mulq_subgoal_rr_aux2:
  assumes a0:"xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]" and
  a1:"Next pc' reg' m' = interp3 xins (Next pc reg m)"
  shows "reg' (bpf_to_x64_reg src) = reg (bpf_to_x64_reg src)"
proof-
 let "?xins" = "Pmulq_r (bpf_to_x64_reg src)" 
  have "\<exists> result sz. exec_instr ?xins sz pc reg m = result" by blast
  then obtain result sz where b1_1:"exec_instr ?xins sz pc reg m = result" by auto
  have "result \<noteq> Stuck"using exec_instr_def b1_1 by auto
  hence b1:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = exec_instr ?xins sz pc reg m" using b1_1
    by (metis outcome.exhaust)
  then obtain pc1 reg1 m1 where b1:"Next pc1 reg1 m1 = exec_instr ?xins sz pc reg m" by auto
  have b2:"reg1 (bpf_to_x64_reg src) =  reg' (bpf_to_x64_reg src)" using mulq_subgoal_rr_aux2_3 a0 a1 b1 by simp
  have b3:"bpf_to_x64_reg src = RAX \<or> bpf_to_x64_reg src = RDX \<or> bpf_to_x64_reg src \<notin>{RAX,RDX}" by auto
  show ?thesis
  proof(cases "bpf_to_x64_reg src \<notin>{RAX,RDX}")
    case True
    have bn:"\<forall> r. bpf_to_x64_reg r \<notin> {RAX, RDX} \<longrightarrow> reg1 (bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using mulq_subgoal_rr_aux2_2 b1 by simp
    thus ?thesis using b2 b3 True by auto
  next
    case False
    have b4:"bpf_to_x64_reg src = RAX \<or> bpf_to_x64_reg src = RDX" using False b3 by simp
    then show ?thesis 
    proof(cases "bpf_to_x64_reg src = RAX")
      case True
      
      then show ?thesis sorry
    next
      case False
      have c0:"bpf_to_x64_reg src = RDX" using False b3 b4 by simp
      then show ?thesis using mulq_subgoal_rr_aux2_4 c0 a0 a1 by metis
    qed
  qed
  
qed


lemma mulq_subgoal_rr_aux2_3:"xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX] \<Longrightarrow> 
  Next pc' reg' m' = interp3 xins (Next pc reg m) \<Longrightarrow>
  \<forall> r.  bpf_to_x64_reg r \<notin> {RAX, RDX} \<longrightarrow> reg' (bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)"
  using mulq_subgoal_rr_aux2_2 mulq_subgoal_rr_aux2_3 



end
