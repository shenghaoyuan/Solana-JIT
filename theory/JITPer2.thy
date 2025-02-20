theory JITPer2
  imports JITPer JITPer2Aux x64DecodeProofAux
begin

lemma mulq_match_mem_aux1:
  "sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m') \<Longrightarrow>
  bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
  prog!(unat pc) = bins \<Longrightarrow>
  m = m'"
  using mem_is_not_changed by blast

lemma mulq_match_mem_aux2_1: 
   "\<forall> x1 x2. x1 = x2 \<longrightarrow> match_mem x1 x2 " using match_mem_def by simp

lemma mulq_match_mem_aux2: 
  assumes a0:"xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]" and
  a1:"exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc xrs m   = Next xpc1 xrs1 m1" and
  a2:"exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2" and
  a3:"exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3" and
  a4:"exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4" and
  a5:"exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5" and
  a6:"exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) xpc5 xrs5 m5 = Next xpc6 xrs6 m6" 
shows "match_mem m  m6"
proof-
  have b1:"m1 = m" using  a0 exec_instr_def a1 by simp
  have c1:"xrs SP = xrs1 SP" using a0 exec_instr_def a1 by auto

  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 RAX)" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "(xrs1 SP)- (u64_of_memory_chunk M64)"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) \<noteq> None" 
    using a0 a1 exec_push_def apply(cases "storev M64 m ?addr (Vlong (xrs1 RAX))",simp_all)
    apply (metis (no_types, lifting) memory_chunk.simps(16) storev_def val.simps(29))    
    subgoal for a using b1 by blast
    done
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) = Some m2" 
    using b2_2 b2_1 exec_push_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
  have c2:"xrs2 RSP = ?addr" using b2_1 exec_push_def b2_2 b2_1
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all) 
 
  have b3:"m2=m3" using a0 exec_instr_def a3 by simp
  have c3:"xrs2 RSP = xrs3 RSP" using  a0 exec_instr_def a3 by auto

  have b4:"m3=m4" using  a0 exec_instr_def a4 by simp
  have c4:"xrs3 RSP = xrs4 RSP" using a0 exec_instr_def a4 by auto

  have b5:"m4=m5" using a0 exec_instr_def a5 by simp
  have c5:"xrs4 RSP = xrs5 RSP" using a0 exec_instr_def a5 by auto

  have b5_1:"Next xpc6 xrs6 m6 = exec_pop xpc5 1 M64 m5 xrs5 RAX" using a6 a0 exec_instr_def by simp
  have b5_2:"Mem.loadv M64 m5 ?addr \<noteq> None" using store_load_consistency b2 b3 b4 b5 by blast
  have b5_3:"Mem.loadv M64 m5 ?addr = Some (Vlong (xrs1 RAX))" using b2 b3 b4 b5 store_load_consistency by auto
  have b6:"m6 = m5" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 RAX)",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 c1 by force
    done
  have b7:"match_mem m1 m2" sorry
  thus ?thesis using b1 b3 b4 b5 b6 b7 mulq_match_mem_aux2_1 by blast
qed

lemma mulq_match_stack:
  assumes a0:"match_stack rs xm " and
  a1:"xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]" and
  a2:"exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) pc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6"
shows" match_stack rs6 m6"
  using mulq_subgoal_rr_aux1_3 mulq_match_mem_aux2 a0 a1 a2 match_stack_def match_mem_def by (smt (z3))


lemma mulq_match_mem:
  "match_mem m xm \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc reg m) = (SBPF_OK pc' reg' m') \<Longrightarrow>
  exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc rs xm = Next pc1 rs1 m1\<and>
  exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
  exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
  exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
  exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
  exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6 \<Longrightarrow>
  bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
  prog!(unat pc) = bins \<Longrightarrow>
  xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
  match_mem m' m6"
  using mulq_match_mem_aux1  mulq_match_mem_aux2 match_mem_def mulq_match_mem_aux2_1 
  by fastforce



lemma mulq_subgoal_rr_aux1_3:
  assumes a0:"xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]" and
  a1:"exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc xrs m   = Next xpc1 xrs1 m1" and
  a2:"exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2" and
  a3:"exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3" and
  a4:"exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4" and
  a5:"exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5" and
  a6:"exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) xpc5 xrs5 m5 = st" 
  shows "st \<noteq> Stuck"
proof-
  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 RAX)" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "(xrs1 SP)- (u64_of_memory_chunk M64)"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) \<noteq> None" 
    using a0 a1 exec_push_def apply(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
    using b2_1 by force
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) = Some m2" 
    using b2_2 b2_1 exec_push_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
  have c2:"xrs2 RSP = ?addr" using b2_1 exec_push_def b2_2 b2_1
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all) 
  
  have b3:"m2=m3" using a0 exec_instr_def a3 by simp
  have c3:"xrs2 RSP = xrs3 RSP" using  a0 exec_instr_def a3 by auto

  have b4:"m3=m4" using  a0 exec_instr_def a4 by simp
  have c4:"xrs3 RSP = xrs4 RSP" using a0 exec_instr_def a4 by auto

  have b5:"m4=m5" using a0 exec_instr_def a5 by simp
  have c5:"xrs4 RSP = xrs5 RSP" using a0 exec_instr_def a5 by auto

  have b5_1:"st = exec_pop xpc5 1 M64 m5 xrs5 RAX" using a6 a0 exec_instr_def by simp
  have b5_2:"Mem.loadv M64 m5 ?addr \<noteq> None" using store_load_consistency b2 b3 b4 b5 by blast
  have b5_3:"Mem.loadv M64 m5 ?addr = Some (Vlong (xrs1 RAX))" using b2 b3 b4 b5 store_load_consistency by auto
  have b5:"st \<noteq> Stuck" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 RAX)",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 by force
    done
  thus ?thesis by simp
qed

lemma unat_of_nat_trans_equiv:"unat ((of_nat (x::nat))::u64) = x"           
  using of_nat_def sorry

lemma of_nat_add:"x = x1 + x2 \<Longrightarrow> of_nat x = y \<longleftrightarrow> of_nat (x1+x2) = y"
  by simp

lemma demo1: 
  assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s xst" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a7:"xpc = 0"
shows "\<exists> xst'. let l = (x64_prog!(unat pc)) in x64_sem (fst l) (snd (snd l)) xst = xst' \<and> 
  match_state s' xst'"
(* \<and> snd xst' = unat (pc+1)*)
proof-
  let "?bpf_ins" = "prog!(unat pc)"
  have b0:"length prog \<noteq> 0" using a6 by blast
  have b1:"\<exists> src dst. ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using a0 a1 a2 a6 b0 aux1 by blast
  obtain src dst where b2:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using b1 by blast
  show ?thesis
  proof (cases "?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src)")
    case True
    let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
    have c0:"?l_bin = snd (snd (the (per_jit_add_reg64_1 dst src)))" using b2 True by fastforce
    have c1:"?l_bin = x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" using per_jit_add_reg64_1_def c0 by fastforce
    have c2:"snd (snd (x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
    let "?st" = "x64_sem (fst (x64_prog!(unat pc))) ?l_bin xst"
    have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
    then have "x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src)" using b2 True by simp
    then have c3_1:"(fst (x64_prog!(unat pc))) = 1" using per_jit_add_reg64_1_def by simp
    moreover have "list_in_list ?l_bin 0 ?l_bin" using  list_in_list_prop by simp
    hence "\<exists> xins2. x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) " 
      using x64_encode_decode_consistency a3 a7 c1 list_in_list_prop c3_1 by blast
    then obtain xins2 where c3:"x64_decode 0 ?l_bin = Some (length ?l_bin, xins2)" by auto
    have c4:"?st = exec_instr xins2 (of_nat (length ?l_bin)) xpc xrs xm" using c3 True a3 a7
      apply(cases xst,simp_all) apply(cases "prog ! unat pc",simp_all) by (simp add: calculation)
    have c5:"xins2 = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using Pair_inject c4 c3 c1 option.inject x64_encode_decode_consistency list_in_list_prop by metis
    have c6:"\<exists> xrs' xpc' xm'. ?st = Next xpc' xrs' xm'" using exec_instr_def spec c5 c4 by auto
    obtain xrs' xpc' xm' where c7:"?st = Next xpc' xrs' xm'" using c6 by auto
    have "match_state s' ?st" using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 per_jit_add_reg64_1_def b2 c4 c3 True by fastforce
    then show ?thesis using True b2 c2 by force                                        
  next
    case False
    have c0_1:"?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using False b2 by blast
    let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
    have c0:"?l_bin = snd (snd (the (per_jit_mul_reg64 dst src)))" using b2 False by fastforce
    let "?result" = "per_jit_mul_reg64 dst src"
    have c2:"(bpf_to_x64_reg dst) = RDX " sorry
    have c1:"?l_bin = (x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX RDX)) 
                  @ (x64_encode (Pmulq_r R11))@(x64_encode (Pmovq_rr RDX RAX))@(x64_encode (Ppopl RAX)))" 
      using c0 per_jit_mul_reg64_def c2 by auto


    let "?l_bin1" = "x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))"
    let "?l_bin2" = "x64_encode (Ppushl_r RAX)"
    let "?l_bin3" = "x64_encode (Pmovq_rr RAX RDX)"
    let "?l_bin4" = "x64_encode (Pmulq_r R11)"
    let "?l_bin5" = "x64_encode (Pmovq_rr RDX RAX)"
    let "?l_bin6" = "x64_encode (Ppopl RAX)"
    have d1:"list_in_list (?l_bin1@?l_bin2@?l_bin3@?l_bin4@?l_bin5@?l_bin6) (0::nat) ?l_bin " using c1 list_in_list_prop c1 by metis
    have d2:"list_in_list ?l_bin 0 ?l_bin = 
      (list_in_list ?l_bin1 0 ?l_bin \<and> list_in_list ?l_bin2 (0 + length ?l_bin1) ?l_bin \<and> 
       list_in_list ?l_bin3 (0 + length ?l_bin1+length ?l_bin2) ?l_bin \<and> 
       list_in_list ?l_bin4 (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3) ?l_bin \<and>
       list_in_list ?l_bin5 (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4) ?l_bin \<and> 
       list_in_list ?l_bin6 (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5) ?l_bin)" 
    using list_in_list_concat d1 c1 list_in_list_prop by (smt (verit, ccfv_SIG))

  have d0:"list_in_list ?l_bin1 0 ?l_bin" using c1 by simp
  have "\<exists> sz1 xins1. x64_decode 0 ?l_bin = Some (sz1,xins1)" using d0 x64_encode_decode_consistency by blast
  then obtain sz1 xins1 where d3_0:"x64_decode 0 ?l_bin = Some (sz1,xins1)" by auto
  hence d0_1:"(sz1,xins1) = (3, Pmovq_rr R11 (bpf_to_x64_reg src))" using d0 x64_encode_decode_consistency by fastforce
  have "\<exists> xpc1 xrs1 m1. exec_instr xins1 (of_nat sz1) xpc xrs xm = Next xpc1 xrs1 m1" 
    using d0_1 exec_instr_def by(cases xins1,simp_all)
  then obtain xpc1 xrs1 m1 where b3:"exec_instr xins1 (of_nat sz1) xpc xrs xm = Next xpc1 xrs1 m1" by blast

  have d3:"list_in_list ?l_bin2 (0 + length ?l_bin1) ?l_bin" using d1 d2 c1 by argo
  have "\<exists> sz2 xins2. x64_decode (0 + length ?l_bin1) ?l_bin = Some (sz2,xins2)" using  d0 c1 x64_encode_decode_consistency 
    using d3 by blast
  then obtain sz2 xins2 where d4_0:"x64_decode (0 + length ?l_bin1) ?l_bin = Some (sz2,xins2)" by auto
  hence d4_1:"(sz2,xins2) =(length ?l_bin2,Ppushl_r RAX)" using x64_encode_decode_consistency c1 Pair_inject add_0 d0 option.sel d3 by metis
  hence d4_2:"sz2 = 1 " apply(cases xins2,simp_all)using bitfield_insert_u8_def Let_def construct_rex_to_u8_def by simp
  have "\<exists> st2. exec_instr xins2 (of_nat sz2) xpc1 xrs1 m1 = st2" 
    using d4_1 d4_2 apply(unfold exec_instr_def) 
    by(cases xins2,simp_all)
  then obtain st2 where d4_3:"exec_instr xins2 (of_nat sz2) xpc1 xrs1 m1 = st2" by auto
  hence "\<exists> xpc2 xrs2 m2. Next xpc2 xrs2 m2 = st2"
    apply(unfold exec_instr_def) 
    apply(cases xins2,simp_all) using d4_1 d4_2
    apply(unfold exec_push_def Let_def,simp_all)
    apply(cases "storev M64 m1 (xrs1 SP - u64_of_memory_chunk M64) (Vlong (xrs1 RAX))",simp_all)
     apply(unfold storev_def) 
     apply(cases M64,simp_all)
     apply (meson option.simps(3))
    subgoal for a
      by blast
    done
  then obtain xpc2 xrs2 m2 where b4:"Next xpc2 xrs2 m2 = exec_instr xins2 (of_nat sz2) xpc1 xrs1 m1" using d4_3 by auto

  have d5:"list_in_list ?l_bin3 (0 + length ?l_bin1+length ?l_bin2) ?l_bin" using d1 c1 d2 by metis
  hence "\<exists> sz3 xins3. x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin = Some (sz3,xins3)" using c1 x64_encode_decode_consistency by blast
  then obtain sz3 xins3 where d5_1:"x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin = Some (sz3,xins3)" by auto
  have d6:"(sz3,xins3) = (length ?l_bin3, Pmovq_rr RAX RDX)" using x64_encode_decode_consistency c1 d3 option.sel d0 d5 d5_1 by metis
  hence d7:"sz3 = 3" by auto
  have "\<exists> xpc3 xrs3 m3. exec_instr xins3 (of_nat sz3) xpc2 xrs2 m2 = Next xpc3 xrs3 m3" 
    using d6 d7 apply(unfold exec_instr_def) 
    by(cases xins3,simp_all)  
  then obtain xpc3 xrs3 m3 where b5:"exec_instr xins3 (of_nat sz3) xpc2 xrs2 m2 = Next xpc3 xrs3 m3" by auto


  have d8:"list_in_list ?l_bin4 (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3) ?l_bin" using d1 d2 c1 by metis
  hence "\<exists> sz4 xins4. x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3) ?l_bin = Some (sz4,xins4)" 
    using c1 x64_encode_decode_consistency by blast
  then obtain sz4 xins4 where d8_1:"x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3) ?l_bin = Some (sz4,xins4)" by auto
  have d9:"(sz4,xins4) = (length ?l_bin4, Pmulq_r R11)" using x64_encode_decode_consistency c1 d3 option.sel d0 d5 d8 d8_1 by metis
  hence d10:"sz4 = 3" by auto
  have "\<exists> xpc4 xrs4 m4. exec_instr xins4 (of_nat sz4) xpc3 xrs3 m3 = Next xpc4 xrs4 m4" 
    using d9 d10 apply(unfold exec_instr_def)
    by(cases xins4,simp_all)  
  then obtain xpc4 xrs4 m4 where b6:"exec_instr xins4 (of_nat sz4) xpc3 xrs3 m3 = Next xpc4 xrs4 m4" by auto


  have d11:"list_in_list ?l_bin5 (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4) ?l_bin" using d1 d2 c1 by metis
  hence "\<exists> sz5 xins5. x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4) ?l_bin = Some (sz5,xins5)" 
    using c1 x64_encode_decode_consistency by blast
  then obtain sz5 xins5 where d11_1:"x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4) ?l_bin = Some (sz5,xins5)" by auto
  have d12:"(sz5,xins5) = (length ?l_bin5, Pmovq_rr RDX RAX)" using x64_encode_decode_consistency c1 d3 option.sel d0 d5 d8 d9 d11 d11_1 by metis
  hence d13:"sz5 = 3" by auto
  have "\<exists> xpc5 xrs5 m5. exec_instr xins5 (of_nat sz5) xpc4 xrs4 m4 = Next xpc5 xrs5 m5"
    using d12 d13 apply(unfold exec_instr_def)
    by(cases xins5,simp_all)  
  then obtain xpc5 xrs5 m5 where b7:"exec_instr xins5 (of_nat sz5) xpc4 xrs4 m4 = Next xpc5 xrs5 m5" by auto

 
  have d14:"list_in_list ?l_bin6 (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5) ?l_bin" using d1 d2 c1 by metis
  hence "\<exists> sz6 xins6. x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5) ?l_bin = Some (sz6,xins6)" 
    using c1 x64_encode_decode_consistency by blast
  then obtain sz6 xins6 where d14_1:"x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5) ?l_bin = Some (sz6,xins6)" by auto
  have d15:"(sz6,xins6) = (length ?l_bin6, Ppopl RAX)" using x64_encode_decode_consistency c1 d3 option.sel d0 d5 d8 d9 d11 d14 d14_1 by metis
  hence d16:"sz6 = 1" apply(cases xins6,simp_all)using bitfield_insert_u8_def Let_def construct_rex_to_u8_def by simp
  have "\<exists> st6. exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5 = st6"
    using d15 d16 by(cases xins6,simp_all) 
  then obtain st6 where b8_1:"exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5 = st6" by auto
  (*hence "\<exists> xpc6 xrs6 m6. st6 = Next xpc6 xrs6 m6"*)
  
  let "?xins" = "[(sz1,xins1)]@[(sz2,xins2)]@[(sz3,xins3)]@[(sz4,xins4)]@[(sz5,xins5)]@[(sz6,xins6)]"
  have c13:"?xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]"
    using d0 d0_1 d4_1 d4_2 d6 d7 d9 d10 d12 d13 d16 d15 by auto
  have c14_1:"exec_instr (snd(?xins!0)) (of_nat(fst(?xins!0))) xpc xrs xm = Next xpc1 xrs1 m1\<and>
    exec_instr (snd(?xins!1)) (of_nat(fst(?xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2 \<and>
    exec_instr (snd(?xins!2)) (of_nat(fst(?xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3 \<and>
    exec_instr (snd(?xins!3)) (of_nat(fst(?xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4 \<and>
    exec_instr (snd(?xins!4)) (of_nat(fst(?xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5 \<and> 
    exec_instr (snd(?xins!5)) (of_nat(fst(?xins!5))) xpc5 xrs5 m5 = st6 " 
    using b3 b4 b5 b6 b7 b8_1 by simp
    
  have b8_2:"st6\<noteq> Stuck" using mulq_subgoal_rr_aux1_3 c13 c14_1 by fast
  hence "\<exists> xpc6 xrs6 m6. st6 = Next xpc6 xrs6 m6 "by (meson outcome.exhaust)
  then obtain xpc6 xrs6 m6 where b8:"Next xpc6 xrs6 m6 = exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5" using b8_1 by auto

  have c14:"exec_instr (snd(?xins!0)) (of_nat(fst(?xins!0))) xpc xrs xm = Next xpc1 xrs1 m1\<and>
    exec_instr (snd(?xins!1)) (of_nat(fst(?xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2 \<and>
    exec_instr (snd(?xins!2)) (of_nat(fst(?xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3 \<and>
    exec_instr (snd(?xins!3)) (of_nat(fst(?xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4 \<and>
    exec_instr (snd(?xins!4)) (of_nat(fst(?xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5 \<and> 
    exec_instr (snd(?xins!5)) (of_nat(fst(?xins!5))) xpc5 xrs5 m5 = Next xpc6 xrs6 m6 " 
    using c14_1 b8 by simp
    
  
  let "?st'" = "x64_sem (fst (x64_prog!(unat pc))) ?l_bin xst" 
  have c16:"snd (snd (x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
  have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
  then have c5:"x64_prog!(unat pc) = the (per_jit_mul_reg64 dst src)" using b2 False by simp
  have c17:"(fst (x64_prog!(unat pc))) = length ?xins" using per_jit_mul_reg64_def c2
      apply(cases "(bpf_to_x64_reg dst)",simp_all) using c5 by force
   have c15:"(fst (x64_prog!(unat pc))) = (Suc(Suc(Suc(Suc(Suc(Suc 0))))))" using c17 by simp
  (*let "?st'" = "x64_sem (Suc(Suc(Suc(Suc(Suc(Suc 0)))))) ?l_bin xst" *)
   (*have cn:"?st' = Next xpc6 xrs6 m6" using c15 b3 b4 b5 b6 b7 b8  d3_0 d4_0 d5_1 d8_1 d11_1 d14_1 sorry*)
   have c3_1:"x64_decode (unat xpc) ?l_bin \<noteq> None" using a7 using d3_0 by simp
   hence c3_2:"?st' = (case x64_decode (unat xpc) ?l_bin of
                  None \<Rightarrow> Stuck |
                 Some (sz, ins) \<Rightarrow>
              x64_sem (Suc(Suc(Suc(Suc(Suc 0))))) ?l_bin (exec_instr ins (of_nat sz) xpc xrs xm))" 
      using a3 c0_1 c15 c0 d3_0 apply(cases xst,simp_all) 
      apply(cases "prog ! unat pc",simp_all)
      subgoal for x91 by(cases "x64_decode (unat xpc) ?l_bin",simp_all)
      done
    have c3:"?st' = x64_sem (Suc(Suc(Suc(Suc(Suc 0))))) ?l_bin (Next xpc1 xrs1 m1)" 
      using c3_1 c3_2 d3_0 b3 by (simp add: a7)

    have c4_0:"xpc1 = of_nat (length ?l_bin1)" using d0_1 a7 b3 exec_instr_def by(cases xins1,simp_all)
    have c4_4:"unat xpc1 = of_nat (0+length ?l_bin1)" using unat_of_nat_trans_equiv c4_0 by simp
    hence c4_1:"x64_decode (unat xpc1) ?l_bin \<noteq> None" using d4_0 a7 by simp     
    have c4_2:"?st' = (case x64_decode (unat xpc1) ?l_bin of
                  None \<Rightarrow> Stuck |
                 Some (sz, ins) \<Rightarrow>
              x64_sem (Suc(Suc(Suc(Suc 0)))) ?l_bin (exec_instr ins (of_nat sz) xpc1 xrs1 m1))" 
      using c3 a3 c0_1 c15 c0 c3_1 apply(cases "Next xpc1 xrs1 m1",simp_all) 
      apply(cases "prog ! unat pc",simp_all)
      subgoal for x91 by(cases "x64_decode (unat xpc1) ?l_bin",simp_all)
      done
    
    have c4:"?st' = x64_sem (Suc(Suc(Suc(Suc 0)))) ?l_bin (Next xpc2 xrs2 m2)" 
      using c4_2 d4_0 c4_4 b4 by simp  

    have c5_1:"xpc2 = xpc1 + of_nat(length ?l_bin2)" using b4 d4_1 d4_2
      apply(unfold exec_instr_def,simp_all)
      apply(cases xins2,simp_all)
      apply(unfold exec_push_def)
      apply(cases "storev M64 m1 (xrs1 SP - u64_of_memory_chunk M64) (Vlong (xrs1 RAX))",simp_all)
       apply (metis One_nat_def of_nat_1 outcome.simps(3))
      subgoal for a
        by (metis d4_2 of_nat_1 outcome.inject)
      done
    have c5_2:"xpc2 = of_nat(length ?l_bin1+length ?l_bin2)" using c5_1 c4_0 by simp
    have c5_3:"unat xpc2 = (0 + length ?l_bin1+length ?l_bin2)" using c5_2 unat_of_nat_trans_equiv by presburger
    have "\<exists> tempst'. x64_sem (Suc 0) ?l_bin (Next xpc2 xrs2 m2) = tempst' \<and>
    x64_sem (Suc(Suc(Suc 0))) ?l_bin tempst' = ?st'" using c4 x64_sem_add 
      using One_nat_def plus_1_eq_Suc by presburger
    then obtain tempst' where c5_4:"x64_sem (Suc 0) ?l_bin (Next xpc2 xrs2 m2) = tempst' \<and>
    x64_sem (Suc(Suc(Suc 0))) ?l_bin tempst' = ?st'" by auto
    have c5_5:"x64_decode (unat xpc2) ?l_bin \<noteq> None" using c5_3 d5_1 by simp
    have c5_6:"x64_sem (Suc 0) ?l_bin (Next xpc2 xrs2 m2) = tempst'" using c5_4 by auto
    have c5_7:"x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin = Some (sz3,xins3)" using d5_1 by simp
    have "tempst' =  (case x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
        x64_sem 0 ?l_bin (exec_instr ins (of_nat sz) xpc2 xrs2 m2))" using c5_3 c5_6
      by (metis x64_sem.simps(3))
    hence "tempst' = x64_sem 0 ?l_bin (exec_instr xins3 (of_nat sz3) xpc2 xrs2 m2)" using c5_7 d5_1 c0_1 
      apply(cases "x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin",simp_all)
      subgoal for a apply(cases "prog ! unat pc",simp_all) 
        subgoal for x91 by auto
        done
      done
    hence c5:"tempst' = Next xpc3 xrs3 m3" using b5 by simp

    have c6_0:" x64_sem (Suc(Suc(Suc 0))) ?l_bin tempst' = ?st'" using c5_4 by auto
    have c6_1:"xpc3 =  xpc2 + of_nat(length ?l_bin3)" using  b5 d6 
      by(unfold exec_instr_def,simp_all)
    have c6_2:"xpc3 = of_nat(length ?l_bin1+length ?l_bin2+length ?l_bin3)" using c6_1 c5_2 by auto
    have c6_3:"unat xpc3 = (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3)" using c6_2 unat_of_nat_trans_equiv by presburger
    have "\<exists> tempst'. x64_sem (Suc 0) ?l_bin (Next xpc3 xrs3 m3) = tempst' \<and>
    x64_sem ((Suc(Suc 0)))?l_bin tempst' = ?st'" using c4 x64_sem_add 
      using One_nat_def plus_1_eq_Suc c5 c6_0 by presburger
    then obtain tempst' where c6_4:"x64_sem (Suc 0) ?l_bin (Next xpc3 xrs3 m3) = tempst' \<and>
    x64_sem ((Suc(Suc 0))) ?l_bin tempst' = ?st'" by auto
    have c6_5:"x64_decode (unat xpc3) ?l_bin \<noteq> None" using c6_3 d8_1 by simp
    have c6_6:"x64_sem (Suc 0) ?l_bin (Next xpc3 xrs3 m3) = tempst'" using c6_4 by auto
    have "tempst' =  (case x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3) ?l_bin of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
        x64_sem 0 ?l_bin (exec_instr ins (of_nat sz) xpc3 xrs3 m3))" using c6_3 c6_6
      by (metis x64_sem.simps(3))
    hence "tempst' = x64_sem 0 ?l_bin (exec_instr xins4 (of_nat sz4) xpc3 xrs3 m3)" using  d8_1 c6_5
      by(cases "x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin",simp_all)
    hence c6:"tempst' = Next xpc4 xrs4 m4" using b6 by simp

    have c7_0:" x64_sem (Suc(Suc 0)) ?l_bin tempst' = ?st'" using c6_4 by auto
    have c7_1:"xpc4 =  xpc3 + of_nat(length ?l_bin3)" using b6 d9
      by(unfold exec_instr_def,simp_all)
    hence c7_2:"xpc4 = of_nat(length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4)" using c6_2 by auto
    hence c7_3:"unat xpc4 = (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4)" using unat_of_nat_trans_equiv by presburger
    have "\<exists> tempst'. x64_sem (Suc 0) ?l_bin (Next xpc4 xrs4 m4) = tempst' \<and>
    x64_sem (Suc 0) ?l_bin tempst' = ?st'" using x64_sem_add 
      using One_nat_def plus_1_eq_Suc c6 c7_0 by presburger
    then obtain tempst' where c7_4:"x64_sem (Suc 0) ?l_bin (Next xpc4 xrs4 m4) = tempst' \<and>
    x64_sem (Suc 0) ?l_bin tempst' = ?st'" by auto
    have c7_5:"x64_decode (unat xpc4) ?l_bin \<noteq> None" using c7_3 d11_1 by simp
    have c7_6:"x64_sem (Suc 0) ?l_bin (Next xpc4 xrs4 m4) = tempst'" using c7_4 by auto
    have "tempst' =  (case x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4) ?l_bin of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
        x64_sem 0 ?l_bin (exec_instr ins (of_nat sz) xpc4 xrs4 m4))" using c7_3 c7_6
      by (metis x64_sem.simps(3))
    hence "tempst' = x64_sem 0 ?l_bin (exec_instr xins5 (of_nat sz5) xpc4 xrs4 m4)" using d11_1
      by(cases "x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin",simp_all)
    hence c7:"tempst' = Next xpc5 xrs5 m5" using b7 by simp

    have c8_0:" x64_sem (Suc 0) ?l_bin tempst' = ?st'" using c7_4 by auto
    have c8_1:"xpc5 =  xpc4 + of_nat(length ?l_bin5)" using b7 d12
      by(unfold exec_instr_def,simp_all)
    hence c8_2:"xpc5 = of_nat(length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5)" using c7_2 by auto
    hence c8_3:"unat xpc5 = (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5)" using unat_of_nat_trans_equiv by presburger
    have "\<exists> tempst'. x64_sem (Suc 0) ?l_bin (Next xpc5 xrs5 m5) = tempst' \<and>
    x64_sem 0 ?l_bin tempst' = ?st'" using x64_sem_add 
      using One_nat_def plus_1_eq_Suc c7 c8_0 by auto
    then obtain tempst' where c8_4:"x64_sem (Suc 0) ?l_bin (Next xpc5 xrs5 m5) = tempst' \<and>
    x64_sem 0 ?l_bin tempst' = ?st'" by auto
    have c8_5:"x64_decode (unat xpc5) ?l_bin \<noteq> None" using c8_3 d14_1 by simp
    have c8_6:"x64_sem (Suc 0) ?l_bin (Next xpc5 xrs5 m5) = tempst'" using c8_4 by auto
    have "tempst' =  (case x64_decode (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5) ?l_bin of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
        x64_sem 0 ?l_bin (exec_instr ins (of_nat sz) xpc5 xrs5 m5))" using c8_3 c8_6
      by (metis x64_sem.simps(3))
    hence "tempst' = x64_sem 0 ?l_bin (exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5)" using d14_1 
      by(cases "x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin",simp_all)
    hence c8:"tempst' = Next xpc6 xrs6 m6" using b8 by simp
    have cn:"?st' = Next xpc6 xrs6 m6" using c8 c8_4 by simp

  have e1:"(\<forall> r. (rs r) = xrs (bpf_to_x64_reg r))" using a1 spec match_state_def match_reg_def a4 a3 by simp
  moreover have e2:"(rs src) = xrs (bpf_to_x64_reg src)" using spec e1 by simp
  moreover have e2_1:"(rs dst) = xrs (bpf_to_x64_reg dst)" using spec e1 by simp
  hence e3:"(rs' dst) = xrs6 (bpf_to_x64_reg dst)"            
    using mulq_subgoal_rr_aux1_2 c2 c0_1 a0 a1 a2 a3 e2 e2_1 c14 c13 by fastforce
  have " \<forall> r. bpf_to_x64_reg r \<notin> {RDX}\<longrightarrow> xrs6 (bpf_to_x64_reg r) = xrs (bpf_to_x64_reg r)" 
    using c13 c14 mulq_subgoal_rr_aux1_4 c2 bpf_to_x64_reg_corr by fastforce
  hence e4:" \<forall> r\<noteq>dst. xrs6 (bpf_to_x64_reg r) = xrs (bpf_to_x64_reg r)" 
    using bpf_to_x64_reg_corr bpf_to_x64_reg_corr2 c2  by (metis singletonD)
  have e5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using mulq_subgoal_rr_aux3 a0 a1 a2 c0_1 by blast
  have e7:"(\<forall> r \<noteq> dst. (rs' r) = xrs6 ((bpf_to_x64_reg r)))" using e1 e4 e5 by presburger
  have e8:"match_stack xrs6 m6" using mulq_match_stack match_state_def a4 c13 c14 a3 a1 by auto
  have e9:"match_mem m' m6" using mulq_match_mem match_state_def a4 c13 c14 a3 a1 a0 a1 a2 c0_1 by fastforce
  have "match_state s' ?st'" using e3 e7 match_state_def e8 e9 match_reg_def cn a2 by fastforce
  thus ?thesis using c16 by simp
qed
qed


lemma match_s_not_stuck:"match_state s xst \<Longrightarrow> xst \<noteq> Stuck"
  apply(cases s, simp_all)
  apply(unfold match_state_def)
  subgoal for x11 x12 x13 by auto
  subgoal for x2 by auto
  by simp

lemma x64_sem1_induct_aux1:"x64_sem1 (Suc n) pc x64_prog (Next xpc xrs m) = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs m) = xst1 \<Longrightarrow> 
  x64_sem1 n (pc+off) x64_prog xst1 = xst'"
 apply(induct n arbitrary:pc x64_prog xpc xrs m xst' num off l)
 apply simp 
  by simp

lemma x64_sem1_induct_aux2:"x64_sem1 n pc x64_prog (Next xpc xrs xm) = x64_sem1 n pc x64_prog (Next 0 xrs xm)"
proof(cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
    thus ?thesis using Suc by fastforce
qed
 
lemma x64_sem1_induct_aux3:"
  xst = (Next xpc xrs m) \<Longrightarrow>
  x64_sem1 (Suc n) pc x64_prog xst = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs m) = xst1 \<Longrightarrow> 
  xst1 = Next xpc1 xrs1 m1 \<Longrightarrow>
  x64_sem1 n (pc+off) x64_prog (Next 0 xrs1 m1) = xst'"
  using x64_sem1_induct_aux2 x64_sem1_induct_aux1 by metis

lemma pc_scope_aux:"\<lbrakk> sbpf_sem n prog s = s'; s = (SBPF_OK pc rs m); s' = (SBPF_OK pc' rs' m'); prog \<noteq> []; n>0\<rbrakk> \<Longrightarrow> 
  unat pc < length prog \<and> unat pc \<ge> 0"
  by (metis (no_types, opaque_lifting) err_is_still_err linorder_not_less not_gr_zero sbpf_sem.elims sbpf_state.simps(6) sbpf_step.simps(1))

(*
lemma num_is_1_aux:"jitper prog = Some x64_prog \<Longrightarrow> prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc \<Longrightarrow> 
  fst (x64_prog!(unat pc)) = 1"
proof (induction prog arbitrary:x64_prog pc)
  case Nil
  then show ?case by blast
next
  case (Cons a prog)
  then show ?case 
  proof-
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
    obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
    then have b2:"\<exists> res. jitper prog = Some res" using Cons(1) apply (cases "jitper prog"; auto) 
      using Cons.prems(1) by simp
    obtain res where b3:"jitper prog = Some res"  using b2 by blast
    have b4:"x64_prog = x # res" using Cons(1) b3 b1 Cons by force
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have b5:"unat pc = 0" using True a0 by simp
      have b6:"fst (the (per_jit_ins a)) = 1"  
        apply(cases "per_jit_ins a",simp_all)
        using b1 apply fastforce
        subgoal for aa apply(cases a,simp_all)
          subgoal for x91 x92 x93
            apply(cases x91, simp_all)
            apply(cases x93,simp_all)
            subgoal for x2 
              apply(unfold per_jit_add_reg64_1_def Let_def,simp_all) 
              using b5 by auto
            done
          apply(unfold per_jit_exit_def,simp_all)
          using b5 by auto
        done
      have b7:"the (per_jit_ins a) = x64_prog!(unat pc)" using b5 b1 b4 by auto
      then show ?thesis using b6 b7 by auto
    next
      case False
      have c0:" Some (x # res) = Some x64_prog" using b4 by blast
      have c1:"unat pc \<ge> 1" using a0 False by blast
      let "?pc'" = "unat pc -1"
      have c2:"0 \<le> ?pc' \<and> ?pc' < length prog \<and> prog \<noteq> []" using Cons 
        by (metis False One_nat_def c1 length_Cons less_diff_conv2 less_one list.size(3) list.size(4) zero_le)
      hence "fst (x64_prog ! unat pc) = 1" using c2 Cons False b3
        by (metis (no_types, lifting) b4 nth_Cons' unat_minus_one unsigned_eq_0_iff)
      then show ?thesis by blast
    qed
  qed
qed
*)

lemma corr_pc_aux1:"jitper prog = Some x64_prog \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  off=1"
proof (induction prog arbitrary: x64_prog pc num off l)
  case Nil
  then show ?case by simp
next
  case (Cons a prog)
  then show ?case
  proof-
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have b0_1:"unat pc = 0" using True a0 by simp
      have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
      have b1_1:"(num,off,l) = x" using b0_1 b1 True Cons
        by (smt (verit) jitper.simps(2) nth_Cons_0 old.prod.case option.case_eq_if option.discI option.sel prod_cases3)
      have bn:"off = 1" 
        using b1 apply(cases "per_jit_ins a", simp_all) 
        subgoal for aa 
         apply(cases a,simp_all)
        subgoal for x91 x92 x93
          apply(cases x91,simp_all)
          apply(cases x93,simp_all)
          subgoal for x1 using b1 b1_1 per_jit_add_reg64_1_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x2 using b1 b1_1 per_jit_mul_reg64_def Let_def by auto
          done
        apply(unfold per_jit_exit_def Let_def, simp_all) using b1 b1_1 by blast
      done
      then show ?thesis using bn by blast
    next
      case False
      have "\<exists> res. jitper prog = Some res" using Cons 
        apply (cases "jitper prog"; simp_all) 
        apply(cases a, simp_all) 
        subgoal for x91 x92 x93 apply(cases x91,simp_all) 
          apply(cases x93,simp_all)
          subgoal for x2 apply(cases "per_jit_add_reg64_1 x92 x2",simp_all) 
            done 
          apply(cases x93,simp_all) 
          subgoal for x2 apply(cases "per_jit_mul_reg64 x92 x2",simp_all) 
            done
          done
        apply(unfold per_jit_exit_def) 
        apply(cases per_jit_exit,simp_all) 
        done
      then obtain res where b0:"jitper prog = Some res" by auto
      have b1:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b2:"per_jit_ins a = Some x" using b1 by auto
      have c0:" Some (x # res) = Some x64_prog" using b0 b2 Cons by auto
      have c1:"unat pc \<ge> 1" using a0 False by blast
      have c2:"x64_prog ! unat pc = (num,off,l)" using c0 Cons by simp
      let "?pc'" = "unat pc -1"
      have c3:"(num,off,l) = res! ?pc'" using c0 False c2 by auto
      have c4:"0 \<le> ?pc' \<and> ?pc' < length prog \<and> prog \<noteq> [] " using Cons c0 c1 by auto
      have c5:"off=1" using c3 c4 
        by (metis Cons.IH False b0 unat_minus_one unsigned_eq_0_iff)
      then show ?thesis by blast
    qed
  qed
qed


lemma corr_pc_aux2:
  "jitper prog = Some x64_prog \<Longrightarrow> prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  s =  SBPF_OK pc rs m \<Longrightarrow>
  s' = sbpf_step prog s \<Longrightarrow> s' = SBPF_OK pc' rs' m' \<Longrightarrow> 
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  pc' = pc+off"
proof-
  assume assm0:"s' = sbpf_step prog s"  and
         assm1:"s' = SBPF_OK pc' rs' m'" and
         assm2:"jitper prog = Some x64_prog" and
         assm3:"prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog" and
         assm4:"s = SBPF_OK pc rs m" and
         assm5:"(num,off,l) = x64_prog!(unat pc)"
  have "\<exists> src dst. prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src), BPF_EXIT}" 
    using assm0 assm1 assm3 assm4 aux2 length_0_conv sbpf_state.simps(6) by (smt (verit, del_insts) insert_commute)
  then obtain src dst where c0:"prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src), BPF_EXIT}" by blast
  have c1:"pc' = pc+1" using c0 assm0 assm1 apply(cases "prog!(unat pc)",simp_all)
    prefer 2 using assm4 assm3 apply simp
    subgoal for x91 x92 x93 apply(erule disjE)
      using assm4 assm3 eval_alu_def apply simp 
      using assm4 assm3 eval_alu_def by simp
    done
  have "off=1" 
    using assm2 assm3 assm5 corr_pc_aux1 by blast
  thus ?thesis using c1 by simp
qed
  (*have "x64_prog!(unat pc) = the (per_jit_ins (prog!(unat pc)))" using aux5 assm2 assm3 assm5 by blast
  hence c2:"x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src) \<or> x64_prog!(unat pc) = the per_jit_exit" using c0 by auto
  hence c3:"off = (fst(snd(the (per_jit_add_reg64_1 dst src)))) \<or> off = (fst(snd(the (per_jit_exit))))" using assm5 by (metis split_pairs)
  thus ?thesis
  proof(cases "off = (fst(snd(the (per_jit_exit))))")
    case True
    have "off = 1" using per_jit_add_reg64_1_def True by auto
    then show ?thesis using c1 by simp
  next
    case True
    have "off = (fst(snd(the (per_jit_exit))))" using True c3 by blast
    hence "off = 1" using per_jit_exit_def Let_def try
    then show ?thesis using c1 by simp
  qed                                                   
qed*)

lemma demo2_aux:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m');
   xst = (Next xpc xrs xm);
   match_state s xst;
   jitper prog = Some x64_prog;
   prog \<noteq> [];
   xpc = 0;
   x64_sem1 n pc x64_prog xst = xst' \<rbrakk> \<Longrightarrow>
   match_state s' xst'"
(* \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"*)
proof (induction n arbitrary: prog s s' pc rs m pc' rs' m' xst' xst xpc xrs xm x64_prog xst')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume 
       assm1: "sbpf_sem (Suc n) prog s = s'" and
       assm2:"s = SBPF_OK pc rs m" and
       assm3:"s' = SBPF_OK pc' rs' m'" and
       assm4:"xst = Next xpc xrs xm" and
       assm5:"match_state s xst" and
       assm6:"jitper prog = Some x64_prog" and
       assm7:"prog \<noteq> [] " and
       assm8:"xpc = 0" and
       assm9:"x64_sem1 (Suc n) pc x64_prog xst = xst'"
  then obtain s1 where s1_eq: "s1 = sbpf_step prog s" by simp
  have n_step_def:"sbpf_sem n prog s1 = s'" using s1_eq assm1 sbpf_sem_induct
    by (metis sbpf_sem.simps(2))
  have a0:"unat pc < length prog \<and> unat pc \<ge> 0" using assm1 assm3 
    using Suc.prems(2) assm7 pc_scope_aux by blast
  moreover have a1:"\<exists> pc1 rs1 m1. s1 = (SBPF_OK pc1 rs1 m1)"
    by (metis Suc.prems(3) bot_nat_0.not_eq_extremum intermediate_step_is_ok n_step_def sbpf_sem.simps(1) sbpf_state.simps(6))
  obtain pc1 rs1 m1 where a2:"s1 = (SBPF_OK pc1 rs1 m1)" using a1 by auto
  have a3:"m1 = m" using mem_is_not_changed s1_eq assm2 a2 by blast
  let "?num" = "(fst(x64_prog!(unat pc)))"
  have "\<exists> xst1. x64_sem (fst(x64_prog!(unat pc))) (snd (snd ((x64_prog!(unat pc)))))(Next xpc xrs xm) = xst1 \<and> match_state s1 xst1"
    using s1_eq assm2 a2 assm4 assm5 assm6 assm7 assm8 assm8 demo1 by (metis (mono_tags, lifting) calculation)
  then obtain xst1 where a4:"x64_sem ?num (snd (snd ((x64_prog!(unat pc)))))(Next 0 xrs xm) = xst1 \<and> match_state s1 xst1" using assm8 by auto
  hence a4_1:"x64_sem ?num (snd (snd ((x64_prog!(unat pc)))))(Next 0 xrs xm) = xst1" by auto
  have an:"\<exists> xpc1 xrs1 xm1. xst1 = Next xpc1 xrs1 xm1" using a4 by (metis match_s_not_stuck outcome.exhaust)
  then obtain xpc1 xrs1 xm1 where a10:"xst1 = Next xpc1 xrs1 xm1" by auto
  let "?xst1" = "Next 0 xrs1 xm1"
  have a5:"match_state s1 ?xst1" using an match_state_def
    using a10 a2 a4 by fastforce
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where a6:"x64_prog!(unat pc) = (num,off,l)" by auto
  have a7:"l = (snd (snd ((x64_prog!(unat pc)))))" using a6 by simp
  let "?pc" = "pc+off"
  have a9:"x64_sem1 n ?pc x64_prog ?xst1 = xst'" using x64_sem1_induct_aux3 assm4 assm9 a7 a6 a4_1 a10 by (metis fst_conv)
  have a13:"?pc = pc1" using corr_pc_aux2 assm6 a0 s1_eq a6 a2 assm7 assm2 by auto
  from Suc.IH have " sbpf_sem n prog s = s' \<Longrightarrow>
           s = SBPF_OK pc rs m \<Longrightarrow>
           s' = SBPF_OK pc' rs' m' \<Longrightarrow>
           xst = Next xpc xrs xm \<Longrightarrow>
           match_state s xst \<Longrightarrow>
           jitper prog = Some x64_prog \<Longrightarrow>
           prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc \<Longrightarrow> 
           xpc = 0 \<Longrightarrow> 
           x64_sem1 n pc x64_prog xst = xst' \<Longrightarrow> 
           match_state s' xst'" by blast
  have "x64_sem1 n pc1 x64_prog (Next 0 xrs1 xm1) = xst' \<and> match_state s' xst'" using n_step_def a2 assm3 a10 a5 assm6 assm7 assm8 a9 Suc a13 by blast
  hence an:"match_state s' xst'" by blast
  then show ?case using an by auto
qed


lemma demo2:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m);
   xst = (Next xpc xrs m);
   match_state s xst;
   jitper prog = Some x64_prog;
   prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0;
   xpc = 0 \<rbrakk> \<Longrightarrow>
   \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"
  using demo2_aux by blast





end
