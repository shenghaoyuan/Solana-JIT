theory JITPer_sub
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma subq_one_step_match_reg:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
   match_reg rs' (xrs(IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg dst)) - xrs (IR (bpf_to_x64_reg src))))"
  apply (simp add: match_state_def match_reg_def eval_alu_def eval_reg_def)
  done

lemma subq_one_step_match_mem:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
   x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) ! Suc (0::nat) \<noteq> (57::8 word) \<Longrightarrow> match_mem m' xm"
  apply (simp add: match_state_def match_mem_def eval_alu_def eval_reg_def)
  done
  
lemma subq_one_step_match_stack:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
    x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) ! Suc (0::nat) \<noteq> (57::8 word) \<Longrightarrow>
    match_stack (xrs(IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg dst)) - xrs (IR (bpf_to_x64_reg src))))"
  apply (simp add: match_state_def match_stack_def eval_alu_def eval_reg_def)
  using reg_rsp_consist by blast



lemma aluq_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
     xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc rs m ss) = (SBPF_OK pc' rs' m' ss')  \<Longrightarrow>
     Next spc' reg' xm' xss' = exec_instr xins sz spc reg xm xss \<Longrightarrow>
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


lemma aluq_subgoal_rr_aux2_1:"xins = Psubq_rr dst src \<Longrightarrow> 
  Next pc' reg' m' xss' = exec_instr xins sz pc reg m xss \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (IR r) = reg (IR r)"
  by (simp add: exec_instr_def)



lemma aluq_subgoal_rr_aux2:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' xss' = exec_instr xins sz pc reg m xss \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using aluq_subgoal_rr_aux2_1 by simp



lemma aluq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc rs m ss) = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow>
  \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases bins,simp_all)
  apply(cases "prog ! unat pc", simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done

lemma stack_is_not_changed_by_sub:"Next spc' reg' m' xss' = exec_instr xins sz spc reg m xss \<Longrightarrow> xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> match_stack reg \<Longrightarrow> match_stack reg'"
proof-
  assume a0:"Next spc' reg' m' xss' = exec_instr xins sz spc reg m xss" and
  a1:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) " and
  a2:"match_stack reg"
  have b0:"bpf_to_x64_reg dst \<noteq> RSP" using bpf_to_x64_reg_def by (cases dst,simp_all)
  have b1:"reg (IR SP) = reg' (IR SP)" using exec_instr_def a0 a1 exec_instr_def b0 by simp
  have b2:"m = m'" using a0 a1 exec_instr_def by force
  have "match_stack reg'" using b1 b2 a2 match_stack_def by auto
  thus ?thesis by blast
qed

lemma mem_is_not_changed_by_sub:"Next spc' reg' m' xss' = exec_instr xins sz spc reg m xss \<Longrightarrow> xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> m = m'"
  using exec_instr_def by simp

lemma mem_and_stack_are_not_changed_by_sub:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
    m'=m \<and> ss'=ss"
  apply(cases"prog!(unat pc)",simp_all)
  subgoal for x91 
    apply(cases "eval_alu BPF_SUB dst (SOReg src) rs",simp_all)
    done
  done

lemma aluq_one_step_match_stack2:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow> xss=ss'"
  apply(cases"prog!(unat pc)",simp_all)
  subgoal for x91 
    apply(cases "eval_alu BPF_SUB dst (SOReg src) rs",simp_all)
    apply(unfold match_state_def,simp_all)
    done
  done

lemma subq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_SUB dst (SOReg src)" and
       a1:"per_jit_sub_reg64_1 dst src = Some (n, off, l_bin)" and
       a2:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m ss) = (SBPF_OK pc' rs' m' ss')" and
       a6:"match_state (SBPF_OK pc rs m ss) (pc,(Next spc reg xm xss)) " and
       a7:"prog!(unat pc) = bins"
     shows "match_state (SBPF_OK pc' rs' m' ss') (pc',exec_instr xins sz spc reg xm xss) "
proof -
    have b0:"xins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" 
      using x64_encode_decode_consistency per_jit_sub_reg64_1_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
  have "\<exists> spc' reg' xm' xss'. Next spc' reg' xm' xss'= exec_instr xins sz spc reg xm xss" using exec_instr_def b0 by simp
  then obtain spc' reg' xm' xss' where a5:"Next spc' reg' xm' xss' = exec_instr xins sz spc reg xm xss" by auto

  moreover have b1:"(\<forall> r. (rs r) = reg (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def by simp
    moreover have b2:"(rs src) = reg (IR (bpf_to_x64_reg src))" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (IR (bpf_to_x64_reg dst))" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg (IR (bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' (IR (bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg'" using stack_is_not_changed_by_sub a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using  mem_is_not_changed_by_sub match_state_def a6
      using a4 a5 b0 a0 a7 mem_and_stack_are_not_changed_by_sub a2 
      by (metis (no_types, lifting) outcome.simps(4) sbpf_state.simps(9) snd_conv)
    have "ss=xss" using match_state_def a6 by simp 
    moreover have "ss' = ss" using a0 a4 a2 a7 mem_and_stack_are_not_changed_by_sub by metis
    moreover have "xss' = xss" using b0 a5 by(unfold exec_instr_def,simp_all)
    ultimately have "ss' = xss'" by meson 
    thus ?thesis using b3 b7 match_state_def b8 b9 match_reg_def
      using a0 a1 a3 a4 a5 a6 a7
      by (smt (verit, del_insts) fst_conv outcome.simps(4) sbpf_state.simps(9) snd_conv)
  qed

lemma subq_one_step:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src)" 
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  apply simp

(* 1. as BPF_SUB generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_sub_reg64_1 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_sub_reg64_1 dst src) = (1, 0, x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))")
       prefer 2
      subgoal by (simp add: per_jit_sub_reg64_1_def)
      apply (subgoal_tac "(x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) !1 \<noteq> 0x39 \<and> 
        (x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) !0 \<noteq> 0xc3 \<and> 
        (x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) !0 \<noteq> 0xe8")
       prefer 2
      subgoal apply(unfold x64_encode_def) 
        apply(cases "Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)",simp_all)
        subgoal for x11 apply(unfold per_jit_sub_reg64_1_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def,simp_all)
          apply(cases "and (u8_of_ireg (bpf_to_x64_reg src)) (8::8 word) \<noteq> (0::8 word)",simp_all)
           apply(cases "and (u8_of_ireg x11) (8::8 word) \<noteq> (0::8 word)",simp_all)
          apply(cases "and (u8_of_ireg x11) (8::8 word) \<noteq> (0::8 word)",simp_all)
          done
        done
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to remove another case statement *)
        apply (subgoal_tac "x64_decode 0 (x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) = Some (3, Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "(x64_encode (Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))" in x64_encode_decode_consistency)
          subgoal by (rule list_in_list_prop)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        subgoal
          apply simp
          apply (erule subst)

(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
        apply (simp add: exec_instr_def)
        apply (rule conjI)
        subgoal
          using a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3 by metis

        unfolding a1 a2
        apply (simp add: match_state_def)
        apply (rule conjI)

(* 4.1  match_reg *)
        subgoal using subq_one_step_match_reg a0 a1 a2 a3 a4 a6 a8
          by simp

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using subq_one_step_match_mem a0 a1 a2 a3 a4 a6 a8  by simp
(* 4.2  match_stack *)
        subgoal using subq_one_step_match_stack a0 a1 a2 a3 a4 a6 a8 apply simp
          using aluq_one_step_match_stack2 a0 a1 a2 a3 a4 a6 a8 by (metis (no_types, lifting)) 
        done
        done
      done
    done       
  done      
          
(* Another way to prove it      
  
(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
        apply (simp add: exec_instr_def)
        apply (rule conjI)
        subgoal
          by (metis a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3)

        unfolding a1 a2          
          
          apply (rule conjI)
          subgoal
            using a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3 by metis
          subgoal
            unfolding a1 a2
            by (metis a0 a1 a2 a3 a4 a8 subq_subgoal_rr_generic list_in_list_prop match_state_eqiv per_jit_sub_reg64_1_def x64_encode_decode_consistency)
          done
        done
      done
    done
  done
*)
end