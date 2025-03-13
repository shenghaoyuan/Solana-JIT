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
   \<Longrightarrow> match_stack reg \<Longrightarrow> match_stack reg' "
proof-
  assume a0:"Next spc' reg' m' = exec_instr xins sz spc reg m" and
  a1:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) " and
  a2:"match_stack reg"
  have b0:"bpf_to_x64_reg dst \<noteq> RSP" using bpf_to_x64_reg_def by (cases dst,simp_all)
  have b1:"reg (IR SP) = reg' (IR SP)" using exec_instr_def a0 a1 exec_instr_def b0 by simp
  have b2:"m = m'" using a0 a1 exec_instr_def by force
  have "match_stack reg' " using b1 b2 a2 match_stack_def by auto
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
       a6:"match_state (SBPF_OK pc rs m) (pc,(Next spc reg xm)) " and
       a7:"prog!(unat pc) = bins"
     shows "match_state (SBPF_OK pc' rs' m') (pc',exec_instr xins sz spc reg xm) "
proof -
    have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" 
      using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
  have "\<exists> spc' reg' xm'. Next spc' reg' xm' = exec_instr xins sz spc reg xm" using exec_instr_def b0 by simp
  then obtain spc' reg' xm' where a5:"Next spc' reg' xm' = exec_instr xins sz spc reg xm" by auto

  moreover have b1:"(\<forall> r. (rs r) = reg (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def by simp
    moreover have b2:"(rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' (IR (bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed_by_add match_state_def a6
      using a4 a5 b0 outcome.simps(4) sbpf_state.simps(9) 
      by (smt (verit) a0 a7 binop.simps(133) bpf_instruction.simps(369) option.case_eq_if sbpf_state.distinct(3) sbpf_state.inject(1) sbpf_step.elims snd_conv)
    thus ?thesis using b3 b7 match_state_def b8 b9 match_reg_def
      using a0 a1 a3 a4 a5 a6 a7
      by (smt (verit, del_insts) fst_conv outcome.simps(4) sbpf_state.simps(9) snd_conv)
  qed

lemma addq_one_step1:
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
  apply simp

(* 1. as BPF_ADD generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_add_reg64_1 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_add_reg64_1 dst src) = (1, 0, x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))")
       prefer 2
      subgoal by (simp add: per_jit_add_reg64_1_def)
      apply (subgoal_tac "(x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) !1 \<noteq> 0x39")
       prefer 2
      subgoal apply(unfold x64_encode_def) 
        by(cases "Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)",simp_all) 
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to remove another case statement *)
        apply (subgoal_tac "x64_decode 0 (x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) = Some (3, Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "(x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))" in x64_encode_decode_consistency)
          subgoal by (rule list_in_list_prop)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        subgoal
          apply simp
          apply (erule subst)

(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
          apply (rule conjI)
          subgoal
            using a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3 by metis
          subgoal
            unfolding a1 a2
            by (metis a0 a1 a2 a3 a4 a8 addq_subgoal_rr_generic list_in_list_prop match_state_eqiv per_jit_add_reg64_1_def x64_encode_decode_consistency)
          done
        done
      done
    done
  done


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
    let "?x64_ins" = "Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)"

(*1. when sbpf_step executes BPF_ADD, x64_sem1 should execute the binary of x64_ins*)
    have c0:"?l_bin = snd (snd (the (per_jit_add_reg64_1 dst src)))" using a8 per_jit_ins_def by fastforce
    have c1:"?l_bin = x64_encode ?x64_ins" using per_jit_add_reg64_1_def c0 by fastforce
    have c2:"snd (snd(x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
    let "?pc1_xst1" = "x64_sem1 1 x64_prog (pc,xst)"
    let "?xst1" = "snd ?pc1_xst1"
    have c2_1:"?xst1 = snd (one_step x64_prog (pc,xst))" 
      by (metis One_nat_def prod.collapse x64_sem1.simps(1) x64_sem1.simps(2))

    have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
    then have c3_0:"x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src)" using a8 per_jit_ins_def by simp

(*2. using consistency to ensure that x64_sem1 (or x64_sem) runs x64_ins assembly *)
    have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
    then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto
    have "l = x64_encode ?x64_ins" using aux5 a6 a5 a8 c_aux c3_0 per_jit_add_reg64_1_def by simp
    hence c3_4:"l!1 \<noteq> 0x39" using c1 apply(unfold x64_encode_def) 
      apply(cases "Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)",simp_all) 
      done

    have c3_1:"num = 1" using per_jit_add_reg64_1_def c3_0 c_aux by simp
    have c3_2:"off = 0" using per_jit_add_reg64_1_def c3_0 c_aux by simp
    have "list_in_list ?l_bin 0 ?l_bin" using  list_in_list_prop by blast
    hence c3:"x64_decode 0 ?l_bin = Some (length ?l_bin, ?x64_ins) " 
      using x64_encode_decode_consistency a3 c1 list_in_list_prop c3_1 by blast

    have c3_3:"?xst1 = x64_sem num l (Next 0 xrs xm)" using c2_1 c3_2 a3 c3_4 by (simp add: c_aux one_step_def)

    have c4:"?xst1 = exec_instr ?x64_ins (of_nat (length ?l_bin)) 0 xrs xm" using c3 a8 a3 c_aux c3_3 c_aux c3_0 per_jit_ins_def c3_1 by simp

(*3. show the final states between sbpf_step and x64_sem1 are match_state  *)
    have c6:"\<exists> xrs' xpc' xm'. ?xst1 = Next xpc' xrs' xm'" using exec_instr_def spec c4 by auto
    obtain xrs' xpc' xm' where c7:"?xst1 = Next xpc' xrs' xm'" using c6 by auto
    have c8:"x64_sem num l (Next 0 xrs xm) = ?xst1 \<and> match_state s' (pc',?xst1)"
      using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 per_jit_add_reg64_1_def a8 c4 c3 c2 c_aux c3_1 c1 c3_3 match_state_eqiv by metis
    have "x64_sem1 1 x64_prog (pc,xst) = (pc',(Next xpc' xrs' xm')) \<and> match_state s' (pc', Next xpc' xrs' xm')" 
      using a8 c3_2 a0 a1 a2 a3 a5 a6 x64_sem1_pc_aux1 c7 c8 c3_4 c_aux by (metis insertCI)
    thus ?thesis by simp
  qed

end