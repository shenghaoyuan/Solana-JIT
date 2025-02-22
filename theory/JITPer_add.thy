theory JITPer_add
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma aluq_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow>
     xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')  \<Longrightarrow>
     Next spc' reg' xm' = exec_instr xins sz spc reg xm \<Longrightarrow>
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

lemma stack_is_not_changed_by_add:"Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow> xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> match_stack reg m \<Longrightarrow> match_stack reg' m'"
proof-
  assume a0:"Next spc' reg' m' = exec_instr xins sz spc reg m" and
  a1:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) " and
  a2:"match_stack reg m"
  have b0:"bpf_to_x64_reg dst \<noteq> RSP" using bpf_to_x64_reg_def by (cases dst,simp_all)
  have b1:"reg SP = reg' SP" using exec_instr_def a0 a1 exec_instr_def b0 by simp
  have b2:"m = m'" using a0 a1 exec_instr_def by force
  have "match_stack reg' m'" using b1 b2 a2 match_stack_def by auto
  thus ?thesis by blast
qed

lemma mem_is_not_changed_by_add:"Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow> xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> m = m'"
  using exec_instr_def by simp

lemma addq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and
       a1:"per_jit_add_reg64_1 dst src = Some (n, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = exec_instr xins sz spc reg xm" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg xm) " and
       a7:"prog!(unat pc) = bins"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' xm') "
proof -
    have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" 
      using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def match_reg_def by simp
    moreover have b2:"(rs src) = reg (bpf_to_x64_reg src)" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (bpf_to_x64_reg dst)" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg ((bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg' xm'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed mem_is_not_changed_by_add match_state_def a6
      by (metis (no_types, lifting) a4 a5 b0 outcome.simps(4) sbpf_state.simps(9))
    thus ?thesis using b3 b7 match_state_def b8 b9 match_reg_def by fastforce
  qed
      


end