theory JITFix_prob
  imports JITFlattern JITFix_def
begin

lemma l_pc_index_corr:
  "l_pc \<noteq> [] \<Longrightarrow> 
  unat pc < length l_pc \<and> unat pc \<ge> 0 \<Longrightarrow> 
  nat (fst (l_pc!(unat pc))) = xpc \<Longrightarrow> 
  find_target_pc_in_l_pc2 l_pc (int xpc) 0 = Some (uint pc)"
  sorry

lemma x64_bin_is_sequential_x64_decode3:
  "jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  num = snd (l_pc!(unat pc)) \<Longrightarrow>
  (\<not> (\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)) \<and> 
   \<not> (\<exists> sz imm. x64_decode xpc l_bin0 = Some(sz, Pcall_i imm)) \<and> 
   \<not>(\<exists> sz. x64_decode xpc l_bin0 = Some(sz, Pret_anchor))) \<Longrightarrow>
  jitper insns = Some lt \<Longrightarrow>
  well_formed_prog lt \<Longrightarrow>
  x64_bin_is_sequential num l_bin0 xpc"
  sorry


lemma x64_bin_is_sequential_equivalence:
  "x64_bin_is_sequential num l_bin0 xpc \<Longrightarrow>
  xst = Next xpc xrs xm xss \<Longrightarrow>
  fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = xst1 \<Longrightarrow>
  xst2 = x64_sem num l_bin0 xst \<Longrightarrow> 
  xst1 = xst2"
  sorry


end