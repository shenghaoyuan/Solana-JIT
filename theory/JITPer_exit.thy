theory JITPer_exit
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin
lemma exit_subgoal_rr_generic:
  assumes a0:"bins = BPF_EXIT" and
       a1:"per_jit_exit = Some (n, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (n, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = st'" and
       a5:"xst' = exec_instr xins sz spc reg m" and
       a6:"match_state (SBPF_OK pc rs m) (pc,(Next spc reg m)) " and
       a7:"prog!(unat pc) = bins" and
       a8:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0"
     shows "match_state st' (pc',xst')"
proof-
  have b0:"st' = SBPF_Success (rs BR0)" using a0 a4 a7 a8 by simp
  have b1:"xins = Pret" using x64_encode_decode_consistency per_jit_exit_def a0 a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) map_option_eq_Some option.inject prod.inject)
  moreover have b2:"(\<forall> r. (rs  r) = reg (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def by simp
  moreover have b3:"(rs BR0) = reg (IR (bpf_to_x64_reg BR0))" using a6 spec b2 by simp
  (*have b4:"Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) \<noteq> None" using match_state_def a6 match_stack_def by auto
  hence "\<exists> x. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = x \<and> x\<noteq> None" by simp
  hence "\<exists> v. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some v" by simp*)
  hence b5_1:"\<exists> v. Mem.loadv M64 m (Vlong ((reg (IR SP)) + (u64_of_memory_chunk M64))) = Some (Vlong v)" using match_state_def a6 match_stack_def by simp
  obtain v where b5_2:"Mem.loadv M64 m (Vlong ((reg (IR SP)) + (u64_of_memory_chunk M64))) = Some (Vlong v)" using b5_1 by blast    
  let "?reg'" = "(reg#(IR SP) <- ((reg (IR SP)) + (u64_of_memory_chunk M64)))"
  have b5_3:"xst' = Next v ?reg' m" using exec_instr_def exec_ret_def a5 b1 b5_2 by simp
  hence b5:"?reg' (IR (bpf_to_x64_reg BR0)) = reg (IR (bpf_to_x64_reg BR0))" by (simp add: bpf_to_x64_reg_def)
  thus ?thesis using exec_instr_def b3 b1 b0 a5 using b5_2 exec_ret_def match_state_def by force
qed

end