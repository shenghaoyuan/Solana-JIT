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
     reg (IR (bpf_to_x64_reg dst)) = rs dst \<Longrightarrow>
     reg (IR (bpf_to_x64_reg src)) = rs src \<Longrightarrow>
     reg' (IR (bpf_to_x64_reg dst)) = (rs' dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply(cases "prog ! unat pc",simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done


lemma aluq_subgoal_rr_aux2_1:"xins = Paddq_rr dst src \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (IR r) = reg (IR r)"
  by (simp add: exec_instr_def)


lemma aluq_subgoal_rr_aux2:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
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
  have b1:"reg (IR SP) = reg' (IR SP)" using exec_instr_def a0 a1 exec_instr_def b0 by simp
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
       a6:"match_state (SBPF_OK pc rs m) (pc,(Next spc reg xm)) " and
       a7:"prog!(unat pc) = bins"
  shows "match_state (SBPF_OK pc' rs' m') (pc',(Next spc' reg' xm')) "
proof -
    have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" 
      using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def by simp
    moreover have b2:"(rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' (IR (bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg' xm'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed mem_is_not_changed_by_add match_state_def a6
      using a4 a5 b0 outcome.simps(4) sbpf_state.simps(9) by fastforce
    (*have b10:"pc = spc" using match_state_def a6 by simp
    have "pc' = pc+1" using a4 a7 a0 
      apply(cases bins,simp_all) 
      subgoal for x91 apply(split if_splits,simp_all) 
        using eval_alu_def
        by (smt (verit) binop.simps(133) bpf_instruction.simps(369) option.simps(5) sbpf_state.distinct(3) sbpf_state.inject(1) snd_op.simps(6))
      done
    have "spc' = spc+sz" using a5 apply(unfold exec_instr_def,simp_all) using b0 by(cases xins,simp_all)*)
    thus ?thesis using b3 b7 match_state_def b8 b9 match_reg_def by fastforce
  qed

lemma addq_one_step:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src)" 
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  proof-
    let "?bpf_ins" = "prog!(unat pc)"
    let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
    have c0:"?l_bin = snd (snd (the (per_jit_add_reg64_1 dst src)))" using a8 per_jit_ins_def by fastforce
    have c1:"?l_bin = x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" using per_jit_add_reg64_1_def c0 by fastforce
    have c2:"snd (snd(x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
    let "?one_step" = "x64_sem1 1 x64_prog (pc,xst)"
    let "?st" = "snd ?one_step"
    have c2_1:"?st = snd (one_step x64_prog (pc,xst))" 
      by (metis One_nat_def prod.collapse x64_sem1.simps(1) x64_sem1.simps(2))

    have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
    then have c3_0:"x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src)" using a8 per_jit_ins_def by simp

    have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
    then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto

    then have c3_1:"num = 1" using per_jit_add_reg64_1_def c3_0 by simp
    moreover have "list_in_list ?l_bin 0 ?l_bin" using  list_in_list_prop per_jit_ins_def by simp
    hence "\<exists> xins2. x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) " 
      using x64_encode_decode_consistency a3 c1 list_in_list_prop c3_1 by blast
    then obtain xins2 where c3:"x64_decode 0 ?l_bin = Some (length ?l_bin, xins2)" by auto

    have c3_2:"off = 0" using corr_pc_aux1_1 a5 a6 a8 c_aux by fastforce

    have c3_3:"?st = x64_sem num l (Next 0 xrs xm)" using c2_1 c3_2 a3 by (simp add: c_aux one_step_def)

    have c4:"?st = exec_instr xins2 (of_nat (length ?l_bin)) 0 xrs xm" using c3 a8 a3 c_aux c3_3 c_aux c3_0 per_jit_ins_def
      apply(cases "Next 0 xrs xm",simp_all) apply(cases "prog ! unat pc",simp_all) by (simp add: calculation)
    have c5:"xins2 = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using Pair_inject c4 c3 c1 option.inject x64_encode_decode_consistency list_in_list_prop by metis
    have c6:"\<exists> xrs' xpc' xm'. ?st = Next xpc' xrs' xm'" using exec_instr_def spec c5 c4 by auto
    obtain xrs' xpc' xm' where c7:"?st = Next xpc' xrs' xm'" using c6 by auto
    have c8:"x64_sem num l (Next 0 xrs xm) = ?st \<and> match_state s' (pc',?st)"  
      using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 per_jit_add_reg64_1_def a8 c4 c3 c2 c_aux c3_1 c1 c3_3 match_state_eqiv by metis
    (*have c8:"match_state s' (pc',?st)" using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 per_jit_add_reg64_1_def b2 c4 c3 True by fastforce*)
    have "x64_sem1 1 x64_prog (pc,xst) = (pc',(Next xpc' xrs' xm')) \<and> match_state s' (pc', Next xpc' xrs' xm')" 
      using a8 c3_2 a0 a1 a2 a3 a5 a6 x64_sem1_pc_aux1 c7 c8 c_aux by (metis insertCI)
    thus ?thesis by simp
  qed


end