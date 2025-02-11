theory JITPer2Aux
imports JITPer
begin
  subsection   \<open> BPF_ALU64 list auxs\<close>

lemma interp3_list_aux1:
  assumes a0:"xins\<noteq>[]" and 
          a1:"result = interp3 xins (Next pc reg m)"
        shows "result = Next pc' reg' m' \<longrightarrow> (exec_instr (xins!0) 1 pc reg m) \<noteq> Stuck"
proof (rule ccontr)                             
  assume a2:"\<not> (result = Next pc' reg' m' \<longrightarrow> (exec_instr (xins!0) 1 pc reg m) \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!0) 1 pc reg m) "
  let ?res_ok = "Next pc' reg' m'"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b2: "interp3 xins (Next pc reg m) = Stuck"using a0 b0 exec_instr_def 
     by (metis (no_types, lifting) interp3.elims nth_Cons_0 outcome.case(2) outcome.simps(4))
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_list_aux2:
  assumes a0:"length xins = (2::nat)" and 
          a1:"result = interp3 xins (Next pc reg m)" and
          a2:"Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m)"
        shows "result = Next pc'' reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 pc' reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next pc'' reg'' m'' \<longrightarrow> (exec_instr (xins!1) 1 pc' reg' m') \<noteq> Stuck)"
  let ?tmp = "(exec_instr (xins!1) 1 pc' reg' m') "
  let ?res_ok = "Next pc'' reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2:"interp3 (drop 1 xins) (Next pc' reg' m') = (exec_instr (xins!1) 1 pc' reg' m')" using a0 a1 a2 b0 b1 
       by (metis One_nat_def Suc_1 diff_Suc_1 drop_0 drop_Suc_Cons interp3_list_aux1 length_drop list.size(3) nth_Cons_Suc outcome.exhaust x64_encodes_aux.cases)
     have b3: "interp3 (drop 1 xins) (Next pc' reg' m') = Stuck"using a0 b0 b1 exec_instr_def a2
       using nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp3 xins (Next pc reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       by (smt (verit, ccfv_SIG) One_nat_def assms(3) b1 drop0 drop_Suc interp3.elims list.sel(3) nth_Cons_0 outcome.simps(4))
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed


lemma interp3_list_aux3:"interp3 [] (Next pc reg m) = Next pc reg m"
  by simp

lemma interp3_length2_aux1: assumes a0:"Next pc2 reg2 m2 = interp3 xins (Next pc reg m)" and
  a1:"length xins = (2::nat)"
shows" \<exists> pc' reg' m'. Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc' reg' m')  "
proof-
  from a0 a1 have "\<exists> pc' reg' m'. Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m)" 
    by (metis interp3_list_aux1 length_0_conv outcome.exhaust zero_neq_numeral)
  then obtain pc' reg' m' where b0:"Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m)" by blast
  have "\<exists> pc'' reg'' m''. Next pc'' reg'' m'' = (exec_instr (xins!1) 1 pc' reg' m')" 
    using b0 exec_instr_def
    by (metis (no_types, opaque_lifting) a0 a1 interp3_list_aux2 outcome.exhaust)
  then obtain pc'' reg'' m'' where b1:" Next pc'' reg'' m'' = (exec_instr (xins!1) 1 pc' reg' m')"
    by auto
  have b4:"Next pc'' reg'' m'' = Next pc2 reg2 m2" using  a1 interp3_list_aux3 b1 exec_instr_def
    by (smt (verit) Cons_nth_drop_Suc One_nat_def Suc_1 a0 b0 diff_Suc_1' drop0 drop_Suc_Cons interp3.elims length_0_conv length_drop lessI nth_Cons_0 outcome.simps(4) zero_neq_numeral)
  show ?thesis using a0 a1 b1 b0 b4 by blast
  qed

lemma interp3_length2_aux2:"Next pc'' reg'' m'' = interp3 xins (Next pc reg m) \<Longrightarrow> length xins = (2::nat) \<Longrightarrow> 
  \<exists> pc' reg' m'. Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc'' reg'' m'' = (exec_instr (xins!1) 1 pc' reg' m')  "
  using interp3_length2_aux1 by simp

lemma interp3_length4_aux1:
  assumes a0:"xins\<noteq>[]" and 
          a1:"result = interp3 xins (Next pc reg m)" and
          a2:"Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m)"
        shows "result = Next pc'' reg'' m'' \<longrightarrow> interp3 (tl xins) (Next pc' reg' m') \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next pc'' reg'' m'' \<longrightarrow> interp3 (tl xins) (Next pc' reg' m') \<noteq> Stuck)"
  let ?tmp = "interp3 (tl xins) (Next pc' reg' m') "
  let ?res_ok = "Next pc'' reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"xins\<noteq>[]" using a0 by auto
     have b2:"interp3 (tl xins) (Next pc' reg' m') = interp3 (xins) (Next pc reg m)" using a0 a1 a2 b0 b1 
       using assms(3) interp3.elims by force
     have b3: "interp3 (tl xins) (Next pc' reg' m') = Stuck"using a0 b0 b1 exec_instr_def a2
       using  nth_Cons_0 outcome.case(2) outcome.simps(4) using b2 by simp
     have b4: "interp3 xins (Next pc reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_length4_aux2:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next pc reg m)" and
          a2:"Next pc2 reg2 m2 = interp3 (take 2 xins) (Next pc reg m)"
        shows "result = Next pc'' reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next pc2 reg2 m2) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next pc'' reg'' m'' \<longrightarrow> interp3 (drop 2 xins) (Next pc2 reg2 m2) \<noteq> Stuck)"
  let ?tmp = "interp3 (drop 2 xins) (Next pc2 reg2 m2) "
  let ?res_ok = "Next pc'' reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1:"(take 2 xins) @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     let ?tmplist = "take 2 xins"
     have b2_1:"?tmplist = [(xins!0)]@[(xins!1)]" 
       by (metis One_nat_def Suc_1 a0 append_Nil less_1_mult less_2_cases_iff numeral_Bit0_eq_double take_0 take_Suc_conv_app_nth zero_less_numeral)
     have b2_2:"length ?tmplist = (2::nat)" 
       by (simp add: b2_1)
     have b2_3:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1 )" using a2 b2_2 b2_1 interp3_length2_aux1 
       by (metis Cons_eq_appendI One_nat_def append_Nil assms(3) nth_Cons_0 nth_Cons_Suc)
     then obtain pc1 reg1 m1 where b2_4:"Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1 )" by auto
     have b2_5:"Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m)" using b2_3 using b2_4 by blast
     have b2_6:" Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1 )" using b2_3 using b2_4 by blast
     have b2_7:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b2:"interp3 (drop 2 xins) (Next pc2 reg2 m2) = interp3 (xins) (Next pc reg m)" using a0 a1 a2 a3 b0 b2_5 b2_6 b2_7
       by (metis (no_types, lifting) append_Cons append_Nil interp3.simps(2) outcome.simps(4))
     have b3: "interp3 (drop 2 xins) (Next pc2 reg2 m2) = Stuck"using a0 b0 b1 exec_instr_def a2
       using nth_Cons_0 outcome.case(2) outcome.simps(4) by auto
     have b4: "interp3 xins (Next pc reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_length4_aux3:
  assumes a0:"length xins = (4::nat)" and 
          a1:"result = interp3 xins (Next pc reg m)" and
          a2:"Next pc3 reg3 m3 = interp3 (butlast xins) (Next pc reg m)"
        shows "result = Next pc'' reg'' m'' \<longrightarrow> (exec_instr (last xins) 1 pc3 reg3 m3) \<noteq> Stuck"
proof (rule ccontr)
  assume a2:"\<not> (result = Next pc'' reg'' m'' \<longrightarrow> (exec_instr (last xins) 1 pc3 reg3 m3) \<noteq> Stuck)"
  let ?tmp = "(exec_instr (last xins) 1 pc3 reg3 m3) "
  let ?res_ok = "Next pc'' reg'' m''"
  have a3:"\<not> (\<not> result = ?res_ok \<or> ?tmp \<noteq> Stuck)" using imp_conv_disj a2 by blast
  have a4:"result = ?res_ok \<and> ?tmp = Stuck" using a3 by simp
   then show "False"
   proof
     have b0:"?tmp = Stuck" using a4 conjE by simp
     have b1_1:"(last xins) = (xins!3)" using a0 
       by (metis One_nat_def diff_numeral_Suc diff_zero last_conv_nth length_0_conv pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) zero_neq_numeral)
     have b1_2: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using b1_1 a0 
       using  One_nat_def append_Cons append_Nil 
       by (smt (verit, del_insts) BitM_inc_eq Suc_1 Suc_less_eq add_One append_butlast_last_id append_eq_append_conv diff_Suc_1' eval_nat_numeral(2) id_take_nth_drop length_0_conv length_append_singleton length_butlast numeral_3_eq_3 semiring_norm(2) take0 take_Suc_conv_app_nth zero_less_numeral)
     have b1_3:"length xins >0" using a0 by simp
     let ?tmplist = "(butlast xins)"
     have b2_1:"?tmplist = [(?tmplist!0)]@(tl ?tmplist)" using b1_2 by simp
     have b2_2:"length ?tmplist > 0" using b2_1 by fastforce
     have b2_3:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m)" using b1_3 interp3_list_aux1 
       by (metis a1 a4 bot_nat_0.extremum_strict list.size(3) outcome.exhaust)
     have b2_4:"(?tmplist!0) = (xins!0)" using b2_2 nth_butlast by blast
     have b2_5:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (?tmplist!0) 1 pc reg m) \<and> Next pc3 reg3 m3 = interp3 (tl ?tmplist) (Next pc1 reg1 m1) " 
       using b2_4 a1 a2 b2_2 b2_1  
       by (metis (no_types, lifting) assms(3) b2_3 hd_conv_nth interp3.simps(2) length_0_conv list.exhaust_sel not_gr_zero outcome.simps(4))
     then obtain pc1 reg1 m1 where b2_4:" Next pc1 reg1 m1 = (exec_instr (?tmplist!0) 1 pc reg m) \<and> Next pc3 reg3 m3 = interp3 (tl ?tmplist) (Next pc1 reg1 m1)" by auto
     let ?tmplist2 = "[xins!1]@[xins!2]"
     have b3_0:"length ?tmplist2 = (2::nat)" by simp
     have b3_1:"?tmplist2 = tl ?tmplist" by (simp add: b1_2)
     have b3_2:"Next pc3 reg3 m3 = interp3 (?tmplist2) (Next pc1 reg1 m1)" using b2_4 b3_1 by simp
     have b3_3:"\<exists> pc2 reg2 m2. Next pc2 reg2 m2 = (exec_instr (?tmplist2!0) 1 pc1 reg1 m1) \<and> Next pc3 reg3 m3 = (exec_instr (?tmplist2!1) 1 pc2 reg2 m2)" 
       using a2 b2_2 b2_1 interp3_length2_aux1 b3_1 b3_2 b3_0 by blast
     have b2:"(exec_instr (last xins) 1 pc3 reg3 m3)  = interp3 (xins) (Next pc reg m)" using a0 a1 a2 a3 b0 
       by (smt (z3) Suc_eq_plus1 add_2_eq_Suc append_Cons append_Nil b1_2 b2_4 b3_0 b3_1 diff_Suc_1' interp3.simps(2) interp3_list_aux2 interp3_length2_aux1 last_conv_nth last_tl length_0_conv length_Suc_conv list.sel(3) list.simps(3) list.size(3) nth_Cons_0 outcome.case(1) outcome.inject zero_neq_numeral)
     have b3: "(exec_instr (last xins) 1 pc3 reg3 m3)  = Stuck"using a0 b0 exec_instr_def a2
       using nth_Cons_0 outcome.case(2) outcome.simps(4) by auto
     have b4: "interp3 xins (Next pc reg m) = Stuck" using a0 a1 b3 exec_instr_def a2 
       using b2 by argo
     thus "False" using b2 
       using a1 a4 by (simp add: a0 exec_instr_def)
   qed
 qed

lemma interp3_length4_aux4:
  assumes a0:"length xins = (4::nat)" and 
          a1:"Next pc'' reg'' m''= interp3 xins (Next pc reg m)" 
        shows "\<exists> pc' reg' m'. Next pc' reg' m' = interp3 (take 2 xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = interp3 (drop 2 xins) (Next pc' reg' m')"
proof-
     have b1_1:"(last xins) = (xins!3)" using a0 
        by (metis diff_Suc_1 last_conv_nth length_0_conv one_plus_numeral plus_1_eq_Suc semiring_norm(2) semiring_norm(4) zero_neq_numeral)
     have b1_2: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using b1_1 a0 
       using  One_nat_def append_Cons append_Nil 
       by (smt (verit, del_insts) BitM_inc_eq Suc_1 Suc_less_eq add_One append_butlast_last_id append_eq_append_conv diff_Suc_1' eval_nat_numeral(2) id_take_nth_drop length_0_conv length_append_singleton length_butlast numeral_3_eq_3 semiring_norm(2) take0 take_Suc_conv_app_nth zero_less_numeral)
     have b1_3:"length xins >0" using a0 by simp
     have b2_3:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m)" using b1_3 interp3_list_aux1 
       by (metis a1 bot_nat_0.extremum_strict list.size(3) outcome.exhaust)
     have b2_5:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc'' reg'' m'' = interp3 (tl xins) (Next pc1 reg1 m1) " 
       using a1
        by (metis (no_types, lifting) b1_3 b2_3 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.simps(4))
     then obtain pc1 reg1 m1 where b2_6:" Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc'' reg'' m'' = interp3 (tl xins) (Next pc1 reg1 m1)" by auto
     have b3_3:"\<exists> pc2 reg2 m2. Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1)"using exec_instr_def a0 
       by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc One_nat_def append_Nil b1_3 b2_6 drop0 interp3_list_aux1 length_append_singleton list.sel(3) list.size(3) nth_Cons_Suc one_eq_numeral_iff outcome.exhaust semiring_norm(85))
     then obtain pc2 reg2 m2 where b3_4:"Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1)" by auto
     have b4_1:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
     have b4:"Next pc2 reg2 m2 = interp3 (take 2 xins) (Next pc reg m)" using a0 b3_4 b4_1 b2_6 
       by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
     have b5_1:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b5_2:"interp3 (drop 2 xins) (Next pc2 reg2 m2) = interp3 (xins) (Next pc reg m)" using a0 a1 b5_1 b4
       using append_Cons append_Nil interp3.simps(2) outcome.simps(4) by (metis b2_6 b3_4)
     have b5:"\<exists> pc2 reg2 m2. Next pc2 reg2 m2 = interp3 (take 2 xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = interp3 (drop 2 xins) (Next pc2 reg2 m2)" 
       using b5_2 b4 using a1 by force
     thus ?thesis by fastforce
   qed


lemma interp3_length4_aux6:
  assumes a0:"length xins = (4::nat)" and 
          a1:"Next pc'' reg'' m''= interp3 xins (Next pc reg m)" 
        shows "\<exists> pc' reg' m'. Next pc' reg' m' = interp3 (butlast xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = (exec_instr (last xins) 1 pc' reg' m')"
proof-
     have b1_1:"(last xins) = (xins!3)" using a0 
       by (metis diff_Suc_1 last_conv_nth length_0_conv one_plus_numeral plus_1_eq_Suc semiring_norm(2) semiring_norm(4) zero_neq_numeral)
     have b1_2: "(butlast xins) = [xins!0]@[xins!1]@[xins!2]" using b1_1 a0 
       using  One_nat_def append_Cons append_Nil 
       by (smt (verit, del_insts) BitM_inc_eq Suc_1 Suc_less_eq add_One append_butlast_last_id append_eq_append_conv diff_Suc_1' eval_nat_numeral(2) id_take_nth_drop length_0_conv length_append_singleton length_butlast numeral_3_eq_3 semiring_norm(2) take0 take_Suc_conv_app_nth zero_less_numeral)
     have b1_3:"length xins >0" using a0 by simp
     have b2_3:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m)" using b1_3 interp3_list_aux1 
       by (metis a1 bot_nat_0.extremum_strict list.size(3) outcome.exhaust)
     have b2_5:"\<exists> pc1 reg1 m1. Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc'' reg'' m'' = interp3 (tl xins) (Next pc1 reg1 m1) " 
       using a1
       by (metis (no_types, lifting) b1_3 b2_3 interp3.elims length_greater_0_conv list.sel(3) nth_Cons_0 outcome.simps(4))
     then obtain pc1 reg1 m1 where b2_6:" Next pc1 reg1 m1 = (exec_instr (xins!0) 1 pc reg m) \<and> Next pc'' reg'' m'' = interp3 (tl xins) (Next pc1 reg1 m1)" by auto
     have b3_3:"\<exists> pc2 reg2 m2. Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1)"using exec_instr_def a0 
       by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc One_nat_def append_Cons b1_2 b1_3 b2_6 butlast.simps(2) drop_0 interp3_list_aux1 list.sel(3) list.simps(3) nth_Cons_Suc outcome.exhaust)
     then obtain pc2 reg2 m2 where b3_4:"Next pc2 reg2 m2 = (exec_instr (xins!1) 1 pc1 reg1 m1)" by auto
     have b4_1:"take 2 xins = [xins!0]@[xins!1]" by (simp add: a0 numeral_2_eq_2 take_Suc_conv_app_nth)
     have b4:"Next pc2 reg2 m2 = interp3 (take 2 xins) (Next pc reg m)" using a0 b3_4 b4_1 b2_6 
       by (metis append_Cons append_Nil interp3.simps(2) interp3_list_aux3 outcome.case(1))
     have b5_1:"[xins!0]@[xins!1] @ (drop 2 xins)= xins" using a0
       by (simp add: Cons_nth_drop_Suc numeral_3_eq_3 numeral_nat(2))
     have b5_2:"interp3 (drop 2 xins) (Next pc2 reg2 m2) = interp3 (xins) (Next pc reg m)" using a0 a1 b5_1 b4
       using append_Cons append_Nil interp3.simps(2) outcome.simps(4) by (metis b2_6 b3_4)
     have b5_3:"\<exists> reg2 m2. Next pc2 reg2 m2 = interp3 (take 2 xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = interp3 (drop 2 xins) (Next pc2 reg2 m2)" 
       using b5_2 b4 using a1 by force
     then obtain pc2 reg2 m2 where b5:"Next pc2 reg2 m2 = interp3 (take 2 xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = interp3 (drop 2 xins) (Next pc2 reg2 m2)" by auto
     have b6_1:"\<exists> pc3 reg3 m3. Next pc3 reg3 m3 = (exec_instr (xins!2) 1 pc2 reg2 m2) " using b5 a0 a1 
       by (metis One_nat_def Suc_1 append_Cons append_Nil b1_2 b5_1 butlast.simps(2) interp3_list_aux1 list.simps(3) nth_Cons_Suc outcome.exhaust)
     then obtain pc3 reg3 m3 where b6_2:"Next pc3 reg3 m3 = (exec_instr (xins!2) 1 pc2 reg2 m2)" by auto
     have b6_3:"take 3 xins = [xins!0]@[xins!1]@[xins!2]" using a0 
       by (simp add: add_One numeral_3_eq_3 numeral_nat(2) take_Suc_conv_app_nth)
     have b6_3:"Next pc3 reg3 m3 = interp3 (take 3 xins) (Next pc reg m)" using a0 b5 b6_2 b6_3 
       by (metis (no_types, lifting) append_Cons append_Nil b2_6 b3_4 b4 interp3.simps(2) interp3_list_aux3 outcome.case(1))
     have b6_4:"[xins!0]@[xins!1]@[xins!2]@[last xins] = xins"
       using append_butlast_last_id b1_2 b1_3 by fastforce
     have b6_5:"butlast xins = take 3 xins" using a0
       by (metis Suc_length_conv append_Cons append_Nil b1_2 butlast_conv_take length_butlast list.size(3) numeral_3_eq_3)
     have b6:"Next pc3 reg3 m3 = interp3 (take 3 xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = (exec_instr (last xins) 1 pc3 reg3 m3)" using a0 b6_3 b6_4 b5 b5_1 b6_2 
       by (smt (verit, ccfv_threshold) One_nat_def Suc_eq_plus1 butlast_snoc interp3_length2_aux2 length_append_singleton list.size(3) list.size(4) nth_Cons_0 nth_append_length nth_butlast numeral_2_eq_2 numerals(1) outcome.inject same_append_eq zero_less_numeral)
     thus ?thesis using b6 b6_5 by auto
   qed

lemma interp3_length4_aux5:
  assumes a0:"length xins = (4::nat)" and 
    a1:"Next pc'' reg'' m'' = interp3 xins (Next pc reg m)" and
    a2:"Next pc' reg' m' = (exec_instr (xins!0) 1 pc reg m)"
  shows "\<exists> pc2 reg2 m2. interp3 (butlast(tl xins)) (Next pc' reg' m') = Next pc2 reg2 m2"
proof -
  have b0:"xins\<noteq>[]" using a0 by auto
  then obtain pc3 reg3 m3 where b1_1:"Next pc3 reg3 m3 = interp3 (butlast xins) (Next pc reg m) \<and> Next pc'' reg'' m'' = (exec_instr (last xins) 1 pc3 reg3 m3)" sorry
  let ?tmplist = "butlast xins"
  have b1_3:"(xins!0) = ?tmplist!0" using a0 
    by (simp add: nth_butlast numeral_3_eq_3)
  have b1_2:"Next pc3 reg3 m3 = interp3 ?tmplist (Next pc reg m)" using b1_1 by auto
  have b1_3:"interp3 (tl ?tmplist) (Next pc' reg' m') \<noteq> Stuck" using interp3_length4_aux1 b0 a2 b1_2 b1_3
    by (metis interp3_list_aux3 list.sel(2) outcome.distinct(1))
  have b1:"\<exists> pc2 reg2 m2. interp3 (tl ?tmplist) (Next pc' reg' m') = Next pc2 reg2 m2" using b1_3
    by (meson outcome.exhaust)
  have b2:"butlast(tl xins) = tl ?tmplist" using List.butlast_tl a0 by blast
  thus ?thesis using b2 b1 by simp
  qed

end