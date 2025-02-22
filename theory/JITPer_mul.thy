theory JITPer_mul
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin
lemma mulq_subgoal_rr_aux1_1:
  "xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
    exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) pc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6  \<Longrightarrow>
   \<forall> r. bpf_to_x64_reg r \<notin> {RDX, RAX} \<longrightarrow> rs (bpf_to_x64_reg r) = rs6 (bpf_to_x64_reg r) "
  apply(unfold exec_instr_def)
  apply(cases "Pmulq_r (bpf_to_x64_reg src)",simp_all)
  subgoal for x6
    apply(unfold exec_push_def exec_pop_def exec_ret_def  Let_def) 
    using store_load_consistency sp_block_def
    apply(cases "storev M64 m1 (Vptr 1 (rs1 SP - u64_of_memory_chunk M64)) (Vlong (rs1 RAX))",simp_all)
    apply(cases "loadv M64 m5 (Vptr (Suc 0) (rs5 SP))", simp_all)
    subgoal for a apply(cases a,simp_all)
      subgoal for x5 
        apply(cases M64,simp_all)
        using store_load_consistency reg_r11_consist reg_rsp_consist by auto
      done
    done
  done

lemma mulq_subgoal_rr_aux1_2:
     "(bpf_to_x64_reg dst) = RDX \<Longrightarrow>
     bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc reg m) = (SBPF_OK pc' reg' m')  \<Longrightarrow>
     xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
    exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6 \<Longrightarrow>
     rs (bpf_to_x64_reg dst) = reg dst \<Longrightarrow>
     rs (bpf_to_x64_reg src) = reg src \<Longrightarrow>
     rs6 (bpf_to_x64_reg dst) = (reg' dst)"
    apply (unfold exec_instr_def step) 
    apply(cases "snd (xins ! 0)",simp_all)
    subgoal for x51
      apply(unfold exec_push_def exec_pop_def exec_ret_def  Let_def eval_alu_def  eval_reg_def) 
      apply(split if_splits,simp_all)
      apply(cases " prog ! unat pc ",simp_all)
      subgoal for x91 apply(split if_splits,simp_all)
        using store_load_consistency sp_block_def
        apply(cases "storev M64 m1 (Vptr (Suc 0) (rs1 SP - u64_of_memory_chunk M64)) (Vlong (rs1 RAX))",simp_all)
        apply(cases "loadv M64 m5 (Vptr (Suc 0) (rs5 SP))", simp_all)
    subgoal for a apply(cases a,simp_all)
      subgoal for x5 
        apply(cases M64,simp_all)
       by auto
      done
    done
  done
  done

lemma mulq_subgoal_rr_aux1_3:
  assumes a0:"xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]" and
  a1:"exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc xrs m   = Next xpc1 xrs1 m1" and
  a2:"exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2" and
  a3:"exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3" and
  a4:"exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4" and
  a5:"exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5" and
  a6:"exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) xpc5 xrs5 m5 = Next xpc6 xrs6 m6" 
  shows "xrs6 RAX = xrs RAX \<and> xrs6 RSP = xrs RSP"
proof-
  have b1:"m1 = m" using  a0 exec_instr_def a1 by simp
  have c1:"xrs SP = xrs1 SP" using a0 exec_instr_def a1 by auto
  have d1:"xrs RAX = xrs1 RAX" using a0 exec_instr_def a1 by auto

  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 RAX)" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "Vptr 1  ((xrs1 SP)- (u64_of_memory_chunk M64))"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) \<noteq> None" 
    using a0 a1 exec_push_def storev_def apply(cases "storev M64 m ?addr (Vlong (xrs1 RAX))",simp_all)
    apply (metis (no_types, lifting))    
    subgoal for a using b1 by blast
    done
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) = Some m2" 
    using b2_2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
  have c2:"xrs2 RSP = (xrs1 SP)- (u64_of_memory_chunk M64)" using b2_1 exec_push_def b2_2 b2_1 sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all) 
  have d2:"xrs2 RAX = xrs1 RAX" using a0 exec_instr_def a2 b2_1 exec_push_def sp_block_def
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
  have b5:"m6 = m5 \<and> xrs6 RSP = xrs RSP" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 RAX)",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 c1 sp_block_def by force
    done
  have d5:"xrs6 RAX = xrs RAX" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 RAX)",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 d1 d2 sp_block_def by force
    done
  thus ?thesis using d5 b5 by simp
qed

lemma mulq_subgoal_rr_aux1_4:
  "xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
    exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) pc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6 \<Longrightarrow>
  \<forall> r. bpf_to_x64_reg r \<notin> {RDX} \<longrightarrow> rs (bpf_to_x64_reg r) = rs6 (bpf_to_x64_reg r) "
  using mulq_subgoal_rr_aux1_3 mulq_subgoal_rr_aux1_1 reg_r11_consist reg_rsp_consist 
  by (smt (z3) insert_iff)


lemma mulq_subgoal_rr_aux2_1:
  "xins = Pmulq_r (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r. r \<notin> {RAX, RDX} \<longrightarrow> reg' r = reg r"
  by (simp add: exec_instr_def)


lemma mulq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m') \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow>
  \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases bins,simp_all)
  apply(cases "prog ! unat pc", simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done


lemma mulq_match_mem_aux1:
  "sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m') \<Longrightarrow>
  bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
  prog!(unat pc) = bins \<Longrightarrow>
  m = m'"
  using mem_is_not_changed by blast

lemma mulq_match_mem_aux2_1: 
   "\<forall> x1 x2. x1 = x2 \<longrightarrow> match_mem x1 x2 " using match_mem_def by simp

(*Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

"*)

lemma store_load_other:"storev M64 m (Vptr 1 off) x = Some m' \<Longrightarrow>
  loadv mc m (Vlong place) = Some v \<Longrightarrow> loadv mc m' (Vlong place) = Some v"
  using store_load_consistency 
  apply(unfold storev_def loadv_def)
  apply(cases "(Vptr 1 off)",simp_all)
  subgoal for x61
    apply(cases x,simp_all)
    subgoal for x5
      apply(cases mc,simp_all) 
         apply (smt (z3) n_not_Suc_n option.inject)
      prefer 2  apply (smt (z3) One_nat_def option.inject zero_neq_one)
       prefer 2 apply (smt (z3) One_nat_def option.inject zero_neq_one)
      by (smt (z3) One_nat_def option.inject zero_neq_one)
    done
  done

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
  let "?addr" = "Vptr 1 ((xrs1 SP)- (u64_of_memory_chunk M64))"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) \<noteq> None" 
    using a0 a1 exec_push_def storev_def  apply(cases "storev M64 m ?addr (Vlong (xrs1 RAX))",simp_all)
    apply (metis (no_types, lifting))    
    subgoal for a using b1 by blast
    done
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) = Some m2" 
    using b2_2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
  have c2:"xrs2 RSP = (xrs1 SP)- (u64_of_memory_chunk M64)" using b2_1 exec_push_def b2_2 b2_1 sp_block_def
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
      using b5_1 b5_3 c2 c3 c4 c5 c1 sp_block_def by force
    done
  have b7:"match_mem m1 m2" using store_load_other b2 match_mem_def by simp
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



lemma mulq_subgoal_rr_aux4:
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
  let "?addr" = "Vptr 1 ((xrs1 SP)- (u64_of_memory_chunk M64))"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) \<noteq> None" 
    using a0 a1 exec_push_def apply(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
    using b2_1 sp_block_def by force
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) = Some m2" 
    using b2_2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
  have c2:"xrs2 RSP = (xrs1 SP)- (u64_of_memory_chunk M64)" using b2_1 exec_push_def b2_2 b2_1 sp_block_def
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
      using b5_1 b5_3 c2 c3 c4 c5 sp_block_def by force
    done
  thus ?thesis by simp
qed





end