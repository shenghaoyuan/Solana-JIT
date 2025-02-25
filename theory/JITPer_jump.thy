theory JITPer_jump
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma ja_subgoal_rr_generic:
  assumes a0:"bins = BPF_JA d" and
       a1:"per_jit_ja (scast d) = Some (n, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = exec_instr xins sz spc reg xm" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg xm) " and
       a7:"prog!(unat pc) = bins"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' xm') "
proof -
    have b0:"xins = Pjmp 0" 
      using x64_encode_decode_consistency per_jit_ja_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def match_reg_def by simp
    have b2:"\<forall> r. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 by (simp add: exec_instr_def)
    have b3:"\<forall> r. (rs' r) = (rs r)" using a0 a4 a7 
      by (metis (no_types, lifting) bpf_instruction.simps(375) sbpf_state.distinct(3) sbpf_state.inject(1) sbpf_step.simps(1))
    have b4:"(\<forall> r. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b2 b3 by presburger
    have b8:"match_stack reg' xm'" using a6 match_state_def a5 b0 by (simp add: exec_instr_def)
    have b9:"match_mem m' xm'" using match_state_def a6 a5 b0 apply (simp add: exec_instr_def) 
      using a4 mem_is_not_changed by blast
    thus ?thesis using b4  match_state_def b8 b9 match_reg_def by fastforce
  qed
      
end