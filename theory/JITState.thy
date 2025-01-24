theory JITState
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler Proof1
  JIT_def
begin

record JitProgram =
page_size     :: usize
pc_section    :: "usize list"
text_section  :: "x64_bin"

record jit_state =
jit_result :: JitProgram 
offset_in_text_section :: usize 
jit_pc :: usize

abbreviation "REG_SCRATCH::ireg \<equiv> R11"

definition bpf_to_x64_reg:: "bpf_ireg \<Rightarrow> ireg" where
  "bpf_to_x64_reg br = (
  case br of
  BR0 \<Rightarrow> RAX |
  BR1 \<Rightarrow> RDI |
  BR2 \<Rightarrow> RSI |
  BR3 \<Rightarrow> RDX |
  BR4 \<Rightarrow> RCX |
  BR5 \<Rightarrow> R8  |
  BR6 \<Rightarrow> RBX |
  BR7 \<Rightarrow> R13 |
  BR8 \<Rightarrow> R14 |
  BR9 \<Rightarrow> R15 |
  BR10 \<Rightarrow> RBP
)"

lemma bpf_to_x64_reg_corr2[simp]:" bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2  \<longrightarrow> r1 \<noteq> r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(cases r1; cases r2; simp)
  done

lemma bpf_to_x64_reg_corr[simp]:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(cases r1; cases r2; simp)
  done

definition update_pc_section_aux ::"usize list \<Rightarrow> nat \<Rightarrow> usize \<Rightarrow> usize list" where
"update_pc_section_aux pc_sec pc x = list_update pc_sec pc x"

end