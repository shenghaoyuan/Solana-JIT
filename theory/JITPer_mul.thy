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
   \<forall> r. bpf_to_x64_reg r \<notin> {RDX, RAX} \<longrightarrow> rs (IR(bpf_to_x64_reg r)) = rs6 (IR(bpf_to_x64_reg r)) "
  apply(unfold exec_instr_def)
  apply(cases "Pmulq_r (bpf_to_x64_reg src)",simp_all)
  subgoal for x6
    apply(unfold exec_push_def exec_pop_def exec_ret_def  Let_def) 
    using store_load_consistency sp_block_def
    apply(cases "storev M64 m1 (Vptr 1 (rs1(IR SP) - u64_of_memory_chunk M64)) (Vlong (rs1 (IR RAX)))",simp_all)
    apply(cases "loadv M64 m5 (Vptr (Suc 0) (rs5(IR SP)))", simp_all)
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
     rs (IR (bpf_to_x64_reg dst)) = reg dst \<Longrightarrow>
     rs (IR (bpf_to_x64_reg src)) = reg src \<Longrightarrow>
     rs6 (IR (bpf_to_x64_reg dst)) = (reg' dst)"
    apply (unfold exec_instr_def step) 
    apply(cases "snd (xins ! 0)",simp_all)
    subgoal for x51
      apply(unfold exec_push_def exec_pop_def exec_ret_def  Let_def eval_alu_def  eval_reg_def) 
      apply(split if_splits,simp_all)
      apply(cases " prog ! unat pc ",simp_all)
      subgoal for x91 apply(split if_splits,simp_all)
        using store_load_consistency sp_block_def
        apply(cases "storev M64 m1 (Vptr (Suc 0) (rs1(IR SP) - u64_of_memory_chunk M64)) (Vlong (rs1 (IR RAX)))",simp_all)
        apply(cases "loadv M64 m5 (Vptr (Suc 0) (rs5(IR SP)))", simp_all)
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
  shows "xrs6 (IR RAX) = xrs (IR RAX) \<and> xrs6 (IR RSP) = xrs (IR RSP)"
proof-
  have b1:"m1 = m" using  a0 exec_instr_def a1 by simp
  have c1:"xrs(IR SP) = xrs1(IR SP)" using a0 exec_instr_def a1 by auto
  have d1:"xrs (IR RAX) = xrs1 (IR RAX)" using a0 exec_instr_def a1 by auto

  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 (IR RAX))" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "Vptr 1  ((xrs1(IR SP))- (u64_of_memory_chunk M64))"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 (IR RAX))) \<noteq> None" 
    using a0 a1 exec_push_def storev_def apply(cases "storev M64 m ?addr (Vlong (xrs1 (IR RAX)))",simp_all)
    apply (metis (no_types, lifting))    
    subgoal for a using b1 by blast
    done
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 (IR RAX))) = Some m2" 
    using b2_2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all)
  have c2:"xrs2 (IR RSP) = (xrs1(IR SP))- (u64_of_memory_chunk M64)" using b2_1 exec_push_def b2_2 b2_1 sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all) 
  have d2:"xrs2 (IR RAX) = xrs1 (IR RAX)" using a0 exec_instr_def a2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all) 
  
  have b3:"m2=m3" using a0 exec_instr_def a3 by simp
  have c3:"xrs2 (IR RSP) = xrs3 (IR RSP)" using  a0 exec_instr_def a3 by auto

  have b4:"m3=m4" using  a0 exec_instr_def a4 by simp
  have c4:"xrs3 (IR RSP) = xrs4 (IR RSP)" using a0 exec_instr_def a4 by auto

  have b5:"m4=m5" using a0 exec_instr_def a5 by simp
  have c5:"xrs4 (IR RSP) = xrs5 (IR RSP)" using a0 exec_instr_def a5 by auto

  have b5_1:"Next xpc6 xrs6 m6 = exec_pop xpc5 1 M64 m5 xrs5 RAX" using a6 a0 exec_instr_def by simp
  have b5_2:"Mem.loadv M64 m5 ?addr \<noteq> None" using store_load_consistency b2 b3 b4 b5 by blast
  have b5_3:"Mem.loadv M64 m5 ?addr = Some (Vlong (xrs1 (IR RAX)))" using b2 b3 b4 b5 store_load_consistency by auto
  have b5:"m6 = m5 \<and> xrs6 (IR RSP) = xrs (IR RSP)" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 (IR RAX))",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 c1 sp_block_def by force
    done
  have d5:"xrs6 (IR RAX) = xrs (IR RAX)" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 (IR RAX))",simp_all)
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
  \<forall> r. bpf_to_x64_reg r \<notin> {RDX} \<longrightarrow> rs (IR(bpf_to_x64_reg r)) = rs6 (IR(bpf_to_x64_reg r)) "
  using mulq_subgoal_rr_aux1_3 mulq_subgoal_rr_aux1_1 reg_r11_consist reg_rsp_consist 
  by (smt (z3) insert_iff)


lemma mulq_subgoal_rr_aux2_1:
  "xins = Pmulq_r (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r. r \<notin> {RAX, RDX} \<longrightarrow> reg' (IR r) = reg (IR r)"
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
  have c1:"xrs(IR SP) = xrs1(IR SP)" using a0 exec_instr_def a1 by auto

  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 (IR RAX))" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "Vptr 1 ((xrs1(IR SP))- (u64_of_memory_chunk M64))"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 (IR RAX))) \<noteq> None" 
    using a0 a1 exec_push_def storev_def  apply(cases "storev M64 m ?addr (Vlong (xrs1 (IR RAX)))",simp_all)
    apply (metis (no_types, lifting))    
    subgoal for a using b1 by blast
    done
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 (IR RAX))) = Some m2" 
    using b2_2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all)
  have c2:"xrs2 (IR RSP) = (xrs1(IR SP))- (u64_of_memory_chunk M64)" using b2_1 exec_push_def b2_2 b2_1 sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all) 
 
  have b3:"m2=m3" using a0 exec_instr_def a3 by simp
  have c3:"xrs2 (IR RSP) = xrs3 (IR RSP)" using  a0 exec_instr_def a3 by auto

  have b4:"m3=m4" using  a0 exec_instr_def a4 by simp
  have c4:"xrs3 (IR RSP) = xrs4 (IR RSP)" using a0 exec_instr_def a4 by auto

  have b5:"m4=m5" using a0 exec_instr_def a5 by simp
  have c5:"xrs4 (IR RSP) = xrs5 (IR RSP)" using a0 exec_instr_def a5 by auto

  have b5_1:"Next xpc6 xrs6 m6 = exec_pop xpc5 1 M64 m5 xrs5 RAX" using a6 a0 exec_instr_def by simp
  have b5_2:"Mem.loadv M64 m5 ?addr \<noteq> None" using store_load_consistency b2 b3 b4 b5 by blast
  have b5_3:"Mem.loadv M64 m5 ?addr = Some (Vlong (xrs1 (IR RAX)))" using b2 b3 b4 b5 store_load_consistency by auto
  have b6:"m6 = m5" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 (IR RAX))",simp_all)
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
  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 (IR RAX))" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "Vptr 1 ((xrs1(IR SP))- (u64_of_memory_chunk M64))"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 (IR RAX))) \<noteq> None" 
    using a0 a1 exec_push_def apply(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all)
    using b2_1 sp_block_def by force
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 (IR RAX))) = Some m2" 
    using b2_2 b2_1 exec_push_def sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all)
  have c2:"xrs2 (IR RSP) = (xrs1(IR SP))- (u64_of_memory_chunk M64)" using b2_1 exec_push_def b2_2 b2_1 sp_block_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 (IR RAX)))",simp_all) 
  
  have b3:"m2=m3" using a0 exec_instr_def a3 by simp
  have c3:"xrs2 (IR RSP) = xrs3 (IR RSP)" using  a0 exec_instr_def a3 by auto

  have b4:"m3=m4" using  a0 exec_instr_def a4 by simp
  have c4:"xrs3 (IR RSP) = xrs4 (IR RSP)" using a0 exec_instr_def a4 by auto

  have b5:"m4=m5" using a0 exec_instr_def a5 by simp
  have c5:"xrs4 (IR RSP) = xrs5 (IR RSP)" using a0 exec_instr_def a5 by auto

  have b5_1:"st = exec_pop xpc5 1 M64 m5 xrs5 RAX" using a6 a0 exec_instr_def by simp
  have b5_2:"Mem.loadv M64 m5 ?addr \<noteq> None" using store_load_consistency b2 b3 b4 b5 by blast
  have b5_3:"Mem.loadv M64 m5 ?addr = Some (Vlong (xrs1 (IR RAX)))" using b2 b3 b4 b5 store_load_consistency by auto
  have b5:"st \<noteq> Stuck" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 (IR RAX))",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 sp_block_def by force
    done
  thus ?thesis by simp
qed


lemma mulq_one_step:
assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src)" and
  a9:"(bpf_to_x64_reg dst) = RDX "
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
proof-
  let "?bpf_ins" = "prog!(unat pc)"
  let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
  have c0:"?l_bin = snd (snd (the (per_jit_mul_reg64 dst src)))" using a8 per_jit_ins_def by simp
  let "?result" = "per_jit_mul_reg64 dst src"
  have c2_0:"(bpf_to_x64_reg dst) = RDX \<or> (bpf_to_x64_reg dst) = RAX \<or> (bpf_to_x64_reg dst) \<notin> {RAX, RDX}" by blast
  have c1:"?l_bin = (x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX RDX))
                  @ (x64_encode (Pmulq_r R11))@(x64_encode (Pmovq_rr RDX RAX))@(x64_encode (Ppopl RAX)))" 
      using c0 per_jit_mul_reg64_def a9 by auto


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
  have "\<exists> xpc1 xrs1 m1. exec_instr xins1 (of_nat sz1) 0 xrs xm = Next xpc1 xrs1 m1" 
    using d0_1 exec_instr_def by(cases xins1,simp_all)
  then obtain xpc1 xrs1 m1 where b3:"exec_instr xins1 (of_nat sz1) 0 xrs xm = Next xpc1 xrs1 m1" by blast
  have f0:"3 = length ?l_bin1" using d0_1 by simp

  have d3:"list_in_list ?l_bin2 (0 + length ?l_bin1) ?l_bin" using d1 d2 c1 by argo
  have "\<exists> sz2 xins2. x64_decode (0 + length ?l_bin1) ?l_bin = Some (sz2,xins2)" using  d0 c1 x64_encode_decode_consistency 
    using d3 by blast
  then obtain sz2 xins2 where d4_0:"x64_decode (0 + length ?l_bin1) ?l_bin = Some (sz2,xins2)" by auto
  hence d4_1:"(sz2,xins2) =(length ?l_bin2,Ppushl_r RAX)" using x64_encode_decode_consistency c1 d0 option.sel d3 by metis
  hence d4_2:"sz2 = 1 " apply(cases xins2,simp_all)using bitfield_insert_u8_def Let_def construct_rex_to_u8_def by simp
  have f1:"1 = length ?l_bin2" using d4_2 d4_1 by blast
  let "?len" = "length (let rex = construct_rex_to_u8 False False False False; op = bitfield_insert_u8 0 3 80 0 in if rex = 64 then [op] else [rex, op])" 
  have fn:"?len = 1" by(unfold Let_def construct_rex_to_u8_def bitfield_insert_u8_def,simp_all)
  have "\<exists> st2. exec_instr xins2 (of_nat sz2) xpc1 xrs1 m1 = st2" 
    using d4_1 d4_2 apply(unfold exec_instr_def) 
    by(cases xins2,simp_all)
  then obtain st2 where d4_3:"exec_instr xins2 (of_nat sz2) xpc1 xrs1 m1 = st2" by auto
  hence "\<exists> xpc2 xrs2 m2. Next xpc2 xrs2 m2 = st2"
    apply(unfold exec_instr_def) 
    apply(cases xins2,simp_all) using d4_1 d4_2 d4_3 fn
         apply(unfold exec_push_def Let_def,simp_all)
    apply(cases "storev M64 m1 (Vptr ?len (xrs1 (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs1 (IR RAX)))",simp_all)
    subgoal for x3 
      apply(unfold storev_def,simp_all)
      by (meson option.simps(3))
    subgoal for x3 a 
      apply(unfold storev_def sp_block_def,simp_all)
      by blast
    done
  then obtain xpc2 xrs2 m2 where b4:"Next xpc2 xrs2 m2 = exec_instr xins2 (of_nat sz2) xpc1 xrs1 m1" using d4_3 by auto

  have d5:"list_in_list ?l_bin3 (0 + length ?l_bin1+length ?l_bin2) ?l_bin" using d1 c1 d2 by metis
  hence "\<exists> sz3 xins3. x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin = Some (sz3,xins3)" using c1 x64_encode_decode_consistency by blast
  then obtain sz3 xins3 where d5_1:"x64_decode (0 + length ?l_bin1+length ?l_bin2) ?l_bin = Some (sz3,xins3)" by auto
  have d6:"(sz3,xins3) = (length ?l_bin3, Pmovq_rr RAX RDX)" using x64_encode_decode_consistency c1 d3 option.sel d0 d5 d5_1 by metis
  hence d7:"sz3 = 3" by auto
  have f2:"length ?l_bin3 = 3" using d6 d7 by simp
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
  have f3:"length ?l_bin5 = 3" using d10 d8_1 by simp
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
  have f4:"length ?l_bin5 = 3" using d13 d11_1 by simp
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
  have f5:"length ?l_bin6 = 1" using d16 d14_1 by (metis d15 prod.inject)
  have "\<exists> st6. exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5 = st6"
    using d15 d16 by(cases xins6,simp_all) 
  then obtain st6 where b8_1:"exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5 = st6" by auto
  (*hence "\<exists> xpc6 xrs6 m6. st6 = Next xpc6 xrs6 m6"*)
  
  let "?xins" = "[(sz1,xins1)]@[(sz2,xins2)]@[(sz3,xins3)]@[(sz4,xins4)]@[(sz5,xins5)]@[(sz6,xins6)]"
  have c13:"?xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]"
    using d0 d0_1 d4_1 d4_2 d6 d7 d9 d10 d12 d13 d16 d15 by auto
  have c14_1:"exec_instr (snd(?xins!0)) (of_nat(fst(?xins!0))) 0 xrs xm = Next xpc1 xrs1 m1\<and>
    exec_instr (snd(?xins!1)) (of_nat(fst(?xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2 \<and>
    exec_instr (snd(?xins!2)) (of_nat(fst(?xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3 \<and>
    exec_instr (snd(?xins!3)) (of_nat(fst(?xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4 \<and>
    exec_instr (snd(?xins!4)) (of_nat(fst(?xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5 \<and> 
    exec_instr (snd(?xins!5)) (of_nat(fst(?xins!5))) xpc5 xrs5 m5 = st6 " 
    using b3 b4 b5 b6 b7 b8_1 by simp
    
  have b8_2:"st6\<noteq> Stuck" using mulq_subgoal_rr_aux4 c13 c14_1 by fast
  hence "\<exists> xpc6 xrs6 m6. st6 = Next xpc6 xrs6 m6 "by (meson outcome.exhaust)
  then obtain xpc6 xrs6 m6 where b8:"Next xpc6 xrs6 m6 = exec_instr xins6 (of_nat sz6) xpc5 xrs5 m5" using b8_1 by auto

  have c14:"exec_instr (snd(?xins!0)) (of_nat(fst(?xins!0))) 0 xrs xm = Next xpc1 xrs1 m1\<and>
    exec_instr (snd(?xins!1)) (of_nat(fst(?xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2 \<and>
    exec_instr (snd(?xins!2)) (of_nat(fst(?xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3 \<and>
    exec_instr (snd(?xins!3)) (of_nat(fst(?xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4 \<and>
    exec_instr (snd(?xins!4)) (of_nat(fst(?xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5 \<and> 
    exec_instr (snd(?xins!5)) (of_nat(fst(?xins!5))) xpc5 xrs5 m5 = Next xpc6 xrs6 m6 " 
    using c14_1 b8 by simp
    
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto

  
  
  let "?one_step" = "x64_sem1 1 x64_prog (pc,xst)"
  let "?st'" = "snd ?one_step"
  have c15_1:"?st' = snd (one_step x64_prog (pc,xst))" 
    by (metis One_nat_def prod.collapse x64_sem1.simps(1) x64_sem1.simps(2))
  have c15_2:"off = 0" using c_aux corr_pc_aux1_1 a5 a6 a8 by fastforce
  have c15_3:"?st' = x64_sem num l (Next 0 xrs xm)" using c15_2 a3 c15_1 by (simp add: c_aux one_step_def)
  
  have c16:"l = ?l_bin" using a6 c0 a5 aux5 c_aux by fastforce
  have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
  then have c5:"x64_prog!(unat pc) = the (per_jit_mul_reg64 dst src)" using a8 per_jit_ins_def by simp
  have c17:"num = length ?xins" using per_jit_mul_reg64_def a9
      apply(cases "(bpf_to_x64_reg dst)",simp_all) using c5 c_aux by force
   have c15:"num = (Suc(Suc(Suc(Suc(Suc(Suc 0))))))" using c17 by simp
  (*let "?st'" = "x64_sem (Suc(Suc(Suc(Suc(Suc(Suc 0)))))) ?l_bin xst" *)
   (*have cn:"?st' = Next xpc6 xrs6 m6" using c15 b3 b4 b5 b6 b7 b8  d3_0 d4_0 d5_1 d8_1 d11_1 d14_1 sorry*)
   have c3_1:"x64_decode 0 ?l_bin \<noteq> None" using d3_0 by simp
   hence c3_2:"?st' = (case x64_decode 0 ?l_bin of
                  None \<Rightarrow> Stuck |
                 Some (sz, ins) \<Rightarrow>
              x64_sem (Suc(Suc(Suc(Suc(Suc 0))))) ?l_bin (exec_instr ins (of_nat sz) 0 xrs xm))" 
      using a3 a8 c15 c0 d3_0 c16  c15_3 by(cases "Next 0 xrs xm",simp_all) 
    have c3:"?st' = x64_sem (Suc(Suc(Suc(Suc(Suc 0))))) ?l_bin (Next xpc1 xrs1 m1)" 
      using c3_1 c3_2 d3_0 b3 by auto

    have c4_0:"xpc1 = of_nat (length ?l_bin1)" using d0_1 b3 exec_instr_def by(cases xins1,simp_all)
    have c4_4:"unat xpc1 = of_nat (0+length ?l_bin1)" using d3_0 of_nat_def c4_0 by simp
    hence c4_1:"x64_decode (unat xpc1) ?l_bin \<noteq> None" using d4_0 by simp     
    have c4_2:"?st' = (case x64_decode (unat xpc1) ?l_bin of
                  None \<Rightarrow> Stuck |
                 Some (sz, ins) \<Rightarrow>
              x64_sem (Suc(Suc(Suc(Suc 0)))) ?l_bin (exec_instr ins (of_nat sz) xpc1 xrs1 m1))" 
      using c3 a3 a8 c15 c0 c3_1 apply(cases "Next xpc1 xrs1 m1",simp_all) 
      apply(cases "prog ! unat pc",simp_all)
      subgoal for x91 by(cases "x64_decode (unat xpc1) ?l_bin",simp_all)
      done
    
    have c4:"?st' = x64_sem (Suc(Suc(Suc(Suc 0)))) ?l_bin (Next xpc2 xrs2 m2)" 
      using c4_2 d4_0 c4_4 b4 by simp  

    have c5_1:"xpc2 = xpc1 + of_nat(length ?l_bin2)" using b4 d4_1 d4_2
      apply(unfold exec_instr_def,simp_all)
      apply(cases xins2,simp_all)
      apply(unfold exec_push_def sp_block_def)
      apply(cases "storev M64 m1 (Vptr 1 (xrs1 (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs1 (IR RAX)))",simp_all)
       apply (metis One_nat_def of_nat_1 outcome.simps(3))
      subgoal for a
        by (metis d4_2 of_nat_1 outcome.inject)
      done
    have c5_2:"xpc2 = of_nat(length ?l_bin1+length ?l_bin2)" using c5_1 c4_0 by simp
    have "length ?l_bin1+length ?l_bin2 = 4" using f0 f1 by simp 
    hence c5_3:"unat xpc2 = (0 + length ?l_bin1+length ?l_bin2)" using c5_2 of_nat_def by auto
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
    hence "tempst' = x64_sem 0 ?l_bin (exec_instr xins3 (of_nat sz3) xpc2 xrs2 m2)" using c5_7 d5_1 a8 
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
    have "length ?l_bin1+length ?l_bin2+length ?l_bin3=7" using f0 f1 f2 by linarith
    hence c6_3:"unat xpc3 = (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3)" using c6_2 of_nat_def by auto
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
    have "length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4 = 10" using f0 f1 f2 f3 by simp
    hence c7_3:"unat xpc4 = (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4)" using of_nat_def c7_2 by auto
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
    have "length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5 = 13" using  f0 f1 f2 f3 f4 by simp
    hence c8_3:"unat xpc5 = (0 + length ?l_bin1+length ?l_bin2+length ?l_bin3+length ?l_bin4+length ?l_bin5)" using of_nat_def c8_2 by auto
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

  have e1:"(\<forall> r. (rs r) = xrs (IR (bpf_to_x64_reg r)))" using a1 spec match_state_def match_reg_def a4 a3 by simp
  moreover have e2:"(rs src) = xrs (IR (bpf_to_x64_reg src))" using spec e1 by simp
  moreover have e2_1:"(rs dst) = xrs (IR (bpf_to_x64_reg dst))" using spec e1 by simp
  hence e3:"(rs' dst) = xrs6 (IR (bpf_to_x64_reg dst))"            
    using mulq_subgoal_rr_aux1_2 a9 a8 a0 a1 a2 a3 e2 e2_1 c14 c13 by fastforce
  have " \<forall> r. bpf_to_x64_reg r \<notin> {RDX}\<longrightarrow> xrs6 (IR (bpf_to_x64_reg r)) = xrs (IR (bpf_to_x64_reg r))" 
    using c13 c14 mulq_subgoal_rr_aux1_4 a9 bpf_to_x64_reg_corr by fastforce
  hence e4:" \<forall> r\<noteq>dst. xrs6 (IR (bpf_to_x64_reg r)) = xrs (IR (bpf_to_x64_reg r))" 
    using bpf_to_x64_reg_corr bpf_to_x64_reg_corr2 a9  by (metis singletonD)
  have e5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using mulq_subgoal_rr_aux3 a0 a1 a2 a8 by blast
  have e7:"(\<forall> r \<noteq> dst. (rs' r) = xrs6 (IR (bpf_to_x64_reg r)))" using e1 e4 e5 by presburger
  have e8:"match_stack xrs6 m6" using mulq_match_stack match_state_def a4 c13 c14 a3 a1 by auto
  have e9:"match_mem m' m6" using mulq_match_mem match_state_def a4 c13 c14 a3 a1 a0 a1 a2 a8 by fastforce
  have "match_state s' (pc',?st')" using e3 e7 match_state_def e8 e9 match_reg_def cn a2 by fastforce
  hence e10:"x64_sem num l (Next 0 xrs xm) = ?st' \<and> match_state s' (pc',?st')"  using c16 c15_3 by auto
    (*have c8:"match_state s' (pc',?st)" using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 per_jit_add_reg64_1_def b2 c4 c3 True by fastforce*)
  
  have e11: "1 + pc = pc'" using corr_pc_aux2 a5 a6 a8 a0 a2 a2 a3 c_aux a1
    by (metis add.commute insertCI)
  have "x64_sem1 1 x64_prog (pc,xst) = (pc',(Next xpc6 xrs6 m6)) \<and> match_state s' (pc', Next xpc6 xrs6 m6)" 
      using a8 e11 c15_2 e10 a0 a1 a2 a3 a5 a6 x64_sem1_pc_aux1 c7 c8 c_aux match_state_eqiv cn  by (simp add: add.commute one_step_def)
  then show ?thesis by blast 
qed

end