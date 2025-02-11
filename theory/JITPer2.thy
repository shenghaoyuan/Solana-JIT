theory JITPer2
  imports JITPer
begin
  
lemma push_pop_subgoal_rr_aux1:
  assumes a0:"hd xins = Ppushl_r tmpreg" and 
          a1:"result = (exec_instr (hd xins) sz pc rs m)" and
          a2:"tmpreg \<in> {RDX, RAX, RCX}" and
          a3:"addr = (rs SP) - (u64_of_memory_chunk M32)"
        shows "result = Next (pc+sz) rs' m' \<longrightarrow> storev M32 m addr (Vlong (rs tmpreg)) \<noteq> None"
proof (rule ccontr)
  assume a2:"\<not> (result = Next (pc+sz) rs' m' \<longrightarrow> storev M32 m addr (Vlong (rs tmpreg)) \<noteq> None)"
  let ?tmp = "storev M32 m addr (Vlong (rs tmpreg)) "
  let ?res_ok = "Next (pc+sz) rs' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> (?tmp \<noteq> None))" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = None" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = None" using a4 conjE by simp
     have b2: "exec_push pc sz M32 m rs (rs tmpreg) = Stuck"using a0 exec_instr_def 
       using b0 exec_push_def 
       by (smt (verit, ccfv_threshold) assms(4) option.simps(4) val.simps(29))
     thus "False" using b2 
       using a1 a4 a2 a0 by (simp add: exec_instr_def)
   qed
 qed

lemma push_pop_subgoal_rr_aux2_1_1:"
    storev M32 m addr (Vlong (rs tmpreg)) = Some m' \<Longrightarrow>
    xins = Ppushl_r tmpreg \<Longrightarrow> 
    Next pc' reg' m' = (exec_instr xins sz pc rs m) \<Longrightarrow> 
    reg' SP = (rs SP)-(u64_of_memory_chunk M32)"
 apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  apply(unfold exec_push_def Let_def)
  apply(cases "storev M32 m (rs SP - u64_of_memory_chunk M32) (Vlong (rs tmpreg))",simp_all)
  done

lemma push_pop_subgoal_rr_aux2_1_2:"reg SP = (reg SP)-(u64_of_memory_chunk M32) \<Longrightarrow>
    loadv M32 m (reg SP) = Some (Vlong (reg tmpreg)) \<Longrightarrow>
    xins = Ppopl tmpreg \<Longrightarrow> 
    Next pc' reg' m' = (exec_instr xins sz pc reg m) \<Longrightarrow> 
    reg' tmpreg = reg tmpreg"
 apply(unfold exec_instr_def )
  apply(cases xins, simp_all)
  subgoal for x64
    apply(unfold exec_pop_def Let_def sub64_def vlong_of_memory_chunk_def add64_def)
    apply(cases "loadv M32 m (reg SP)",simp_all)
      done
    done

lemma push_pop_subgoal_rr_aux2_1:
  assumes a0:"xins = [Ppushl_r tmpreg, Ppopl tmpreg]" and 
    a1:"Next pc' reg' m' = (exec_instr (xins!0) sz pc reg m)" and
    a2:"Next pc'' reg'' m'' = (exec_instr (xins!1) sz' pc' reg' m') " and 
    a3:"tmpreg \<in> {RDX, RAX, RCX}" 
  shows "reg'' tmpreg = reg tmpreg"
proof -
  have b0:"Next pc' reg' m' = exec_push pc sz M32 m reg (reg tmpreg)" using exec_instr_def by (simp add: a0 a1)
  let "?xins" = "(xins!0)"
  let "?addr"= "((reg SP) - (u64_of_memory_chunk M32))"  
  have b2_1:"(exec_instr ?xins sz pc reg m) = Next pc' reg' m' \<longrightarrow> storev M32 m ?addr (Vlong (reg tmpreg)) \<noteq> None" 
    by (metis b0 exec_push_def option.case(1) outcome.simps(3))
  have b2_2:"storev M32 m ?addr (Vlong (reg tmpreg)) \<noteq> None" using b2_1 a1 by simp
  have b2:"storev M32 m ?addr (Vlong (reg tmpreg)) = Some m'" using b0 b2_2 by (simp add: storev_def)
  have c0:"Next pc'' reg'' m'' = exec_pop pc' sz' M32 m' reg' tmpreg" using exec_instr_def by (simp add: a0 a2)
  let "?xins2" = "(xins!1)"
  have c1:"?xins2 = Ppopl tmpreg" using a0 by auto
  have c2:"loadv M32 m' ?addr = Some (Vlong (reg tmpreg))" using b2 store_load_consistency by simp
  have c3:"Some (Vlong (reg'' tmpreg)) = loadv M32 m'?addr" using exec_pop_def c1 b2_2 storev_def by auto
  have c4:"reg'' tmpreg = reg tmpreg" using c3 c2 by simp
  thus ?thesis using c4 by simp
qed


lemma push_pop_subgoal_rr_aux2_2:
 assumes a0:"xins = [Ppushl_r tmpreg, Ppopl tmpreg]" and 
    a1:"Next pc'' reg'' m'' = interp3 xins (Next pc reg m)" and
    a2:"tmpreg \<in> {RDX, RAX, RCX}"
  shows "reg'' tmpreg = reg tmpreg"
proof-
  have b0:"length xins = (2::nat)" using a0 by simp
  have b1:"\<exists> n2.  n2 = reg SP - (u64_of_memory_chunk M32)"
    by (metis (no_types, lifting) memory_chunk.simps(15) val.simps(29) vlong_of_memory_chunk_def)
  thus ?thesis using b0 a0 a1 push_pop_subgoal_rr_aux2_1 a2 
    sorry
qed


lemma push_pop_subgoal_rr_aux2_3:
  assumes a0:"hd xins = Ppushl_r tmpreg" and 
          a1:"last xins = Ppopl tmpreg"and
          a2:"interp3 (butlast(tl xins)) (Next pc' reg' m') = Next pc' reg2 m'"and
          a3:"Next pc'' reg'' m'' = (exec_instr (last xins) 1 pc reg2 m') " and
          a5:"Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m) " and
          a6:"reg' SP =  reg2 SP" and
          a7:"tmpreg \<in> {x64Syntax.RDX, x64Syntax.RAX, x64Syntax.RCX}" and
          a8:"n1 = reg SP"
        shows "reg'' tmpreg = reg tmpreg"
  sorry
(*proof-
  let ?midlist = "butlast(tl xins)"
  have b0_1_0:"xins \<noteq> []" using a0
    by (metis a1 hd_Nil_eq_last instruction.distinct(5945))
  have b0_1_1:"xins = [hd xins]@?midlist@[last xins]" using b0_1_0
    by (metis a0 a1 append_Cons append_Nil append_butlast_last_id instruction.distinct(5945) last_ConsL last_tl list.collapse)
  have b0_1:"xins = [Ppushl_r tmpreg]@?midlist@[Ppopl tmpreg]" using a0 a1 b0_1_1 by metis
  have b0_2:"\<exists> reg' m'. Next reg' m' = (exec_instr (xins!0) 1 reg m)" using a0 a1 
    interp3_list_aux1 a5 by blast
  have b0:"Next reg' m' = exec_push 1 M32 m reg (reg (IR tmpreg))" using exec_instr_def a0 b0_2
    using exec_push_def a5 a0 a5 
    by (smt (z3) a1 hd_Nil_eq_last hd_conv_nth instruction.distinct(5945) instruction.simps(6455))
  have b0_2:"\<exists> addr. Vlong addr = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" using a3 sub64_def
  using a3 sub64_def a8
    by (metis (no_types, lifting) memory_chunk.simps(15) val.simps(29) vlong_of_memory_chunk_def)
  then obtain addr where b0_3:"Vlong addr = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" by auto
  have b1:"Next reg' m' =
    (case sub64 (reg (IR SP)) (vlong_of_memory_chunk M32) of
     Vlong (addr::64 word) \<Rightarrow> (
       case storev M32 m addr (reg (IR tmpreg)) of None \<Rightarrow> Stuck
       | Some (x::64 word \<Rightarrow> 8 word option) \<Rightarrow>
           Next
            ((undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))))
             (RIP := add64 (undef_regs [CR ZF, CR CF, CR PF, CR SF, CR OF] (reg(IR SP := sub64 (reg (IR SP)) (vlong_of_memory_chunk M32))) RIP) (Vlong ((1::64 word) + (1::64 word)))))
            x)
     | _ \<Rightarrow> Stuck) " using b0 nextinstr_nf_def nextinstr_def exec_push_def by metis
  hence b3_1:"hd xins = (xins!0)" using a0 List.hd_conv_nth b0_1_0 by blast
  have b2_1:"(exec_instr (xins!0) 1 reg m) = Next reg' m' \<longrightarrow> storev M32 m addr (reg (IR tmpreg)) \<noteq> None" using push_pop_subgoal_rr_aux1 a0 a1
     b1 a3  b0_3 a0 b3_1 by (metis a7)                                 
  have b2_2:"storev M32 m addr (reg (IR tmpreg)) \<noteq> None" using b2_1 a5 by simp
  have b2:"storev M32 m addr (reg (IR tmpreg)) = Some m'" using b1 b2_2 b0_3 
    by (smt (verit, ccfv_threshold) option.case_eq_if option.distinct(1) option.expand option.sel outcome.inject val.simps(29))
  have b3:"reg' (IR SP) = sub64 (reg (IR SP)) (vlong_of_memory_chunk M32)" using b2 b0_3 push_pop_subgoal_rr_aux2_1_1 a5 a0 b3_1 by auto
  let "?sp" = "reg' (IR SP)"
  have b4_2:" Vlong addr = (reg2 (IR SP))" using a6 b3 b0_3 by auto
  have b5:"interp3 (butlast(xins)) (Next reg m) = Next reg2 m'" using a2 a5 b0_1 a0
    using append_Cons append_Nil butlast.simps(1) butlast.simps(2) interp3.simps(2) list.sel(3) list.simps(3) nth_Cons_0 outcome.case(1) by metis
  have b6:"(exec_instr (last xins) 1 reg2 m') = Next reg'' m''" using a5 a1 a2 a3 b5 by simp
  have c0:"Next reg'' m'' = exec_pop (1::64 word) M32 m' reg2 (IR tmpreg)" using exec_instr_def using b6 a1 by simp
  have c1:"loadv M32 m' addr = Some (reg (IR tmpreg))" using store_load_consistency b4_2 b2 b0_3 by blast
  let "?v" = " (reg (IR tmpreg))"
  have c4:"reg''(IR tmpreg) = ?v" using exec_pop_def b4_2 b3 a3 a6 push_pop_subgoal_rr_aux2_1_2 c1 a1 by simp
  thus ?thesis using c4 by simp
qed
*)

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)




end
