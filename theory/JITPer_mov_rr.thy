theory JITPer_mov_rr
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma movq_rr_one_step_match_reg:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_MOV dst (SOReg src) \<Longrightarrow>
    match_reg rs' (xrs(IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg src))))"
  apply (simp add: match_state_def match_reg_def eval_alu_def eval_reg_def)
  done

lemma movq_rr_one_step_match_mem:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_MOV dst (SOReg src) \<Longrightarrow>
   x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) ! Suc (0::nat) \<noteq> (57::8 word) \<Longrightarrow> match_mem m' xm"
  apply (simp add: match_state_def match_mem_def eval_alu_def eval_reg_def)
  done
  
lemma movq_rr_one_step_match_stack:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_MOV dst (SOReg src) \<Longrightarrow>
    x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) ! Suc (0::nat) \<noteq> (57::8 word) \<Longrightarrow>
    match_stack (xrs(IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg src))))"
  apply (simp add: match_state_def match_stack_def eval_alu_def eval_reg_def)
  done

lemma movq_rr_one_step:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_MOV dst (SOReg src)" 
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  apply simp

(* 1. as BPF_MOV generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_mov_reg64_1 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_mov_reg64_1 dst src) = (1, 0, x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))")
       prefer 2
      subgoal by (simp add: per_jit_mov_reg64_1_def)
      apply (subgoal_tac "(x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))!1 \<noteq> 0x39 \<and> 
              (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))!0 \<noteq> 0xc3\<and> 
              (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))!0 \<noteq> 0xe8 ")
       prefer 2
      subgoal apply(unfold x64_encode_def) 
        apply(cases "Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)",simp_all) 
        subgoal for x11 apply(unfold per_jit_mov_reg64_1_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def,simp_all)
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
        apply (subgoal_tac "x64_decode 0 (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))) = Some (3, Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "(x64_encode (Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))" in x64_encode_decode_consistency)
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
          by (metis a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3)

        unfolding a1 a2
        apply (simp add: match_state_def)
        apply (rule conjI)

(* 4.1  match_reg *)
        subgoal using movq_rr_one_step_match_reg a0 a1 a2 a3 a4 a6 a8
          by simp

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using movq_rr_one_step_match_mem a0 a1 a2 a3 a4 a6 a8 by simp
(* 4.2  match_stack *)
        subgoal using movq_rr_one_step_match_stack a0 a1 a2 a3 a4 a6 a8 apply simp 
        done
        done
      done
    done       
  done      
  done
end