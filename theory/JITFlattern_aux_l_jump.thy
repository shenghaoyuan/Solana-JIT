theory JITFlattern_aux_l_jump
  imports JITFlattern_def Proof1 JITFlattern_aux
begin

lemma search_l_jump:"distinct (map fst l_jump) \<Longrightarrow>
  find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow>
  (pc,npc) \<in> set l_jump"
proof(induct l_jump arbitrary: pc npc)
  case Nil
  then show ?case by auto
next
  case (Cons a l_jump)
  assume a0:"find_target_pc_in_l_pc (a # l_jump) pc = Some npc" and
    c0:"distinct (map fst (a#l_jump))"

  have c1:"distinct (map fst l_jump)" using c0 by auto
  
  have c2:"distinct (map fst l_jump) \<Longrightarrow> find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow> (pc, npc) \<in> set l_jump" using Cons by blast

  have a1:"fst a = pc \<or> fst a \<noteq> pc"
    using word_coorder.extremum word_le_sub1 by blast 
  thus ?case
  proof(cases "fst a = pc")
    case True
    have "snd a = npc"  by (metis True a0 find_target_pc_in_l_pc.simps(2) fst_conv option.inject snd_conv surj_pair) 
    then show ?thesis using True by (metis list.set_intros(1) prod.collapse)  
  next
    case False
    have "fst a \<noteq> pc" using False a1 by simp
    hence "\<exists> x. x \<in> set l_jump \<and> fst x = pc" using a0 c1 c0
      by (smt (verit, best) Cons.hyps eq_fst_iff find_target_pc_in_l_pc.elims list.distinct(1) list.inject) 
    then obtain x where b0:"x \<in> set l_jump \<and> fst x = pc" by auto
    hence "snd x = npc" using a0 c1 c0 c2
      by (metis False eq_key_imp_eq_value find_target_pc_in_l_pc.simps(2) fstI sndI surj_pair) 
    then show ?thesis using c1 b0 by (metis list.set_intros(2) prod.collapse) 
  qed
qed

(* \<and> fst (lt!idx2)< length l_pc*)
definition is_increase_list::" ((int\<times>u64) list) \<Rightarrow> (int \<times> nat) list \<Rightarrow> bool" where 
  "is_increase_list lt lt2 \<equiv> (\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length lt \<longrightarrow> fst (lt!idx1) < fst (lt!idx2)) \<and> 
    (\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> nat (fst (lt!idx)) <  (length lt2))"

lemma is_increase_list_empty:                              
  "is_increase_list [] []"
  apply(unfold is_increase_list_def) by simp

lemma l_jump_elem_increases:
  "jitflat_bpf lt (l1, l_pc1, l_jump1) = (l, l_pc, l_jump) \<Longrightarrow> 
  is_increase_list l_jump1 l_pc1  \<Longrightarrow>
  is_increase_list l_jump l_pc"
proof(induct lt arbitrary: l1 l_pc1 l_jump1 l l_pc l_jump)
    case Nil
    then show ?case by force
  next
    case (Cons a lt)
    assume assm0:"is_increase_list l_jump1 l_pc1" and
      assm1:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l, l_pc, l_jump)" 
      (*and assm2:"(a#lt) \<noteq> []"*)
    have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and>  jitflat_bpf lt (l2',l_pc2',l_jump2') = (l,l_pc,l_jump)"
      using jitflat_bpf_induct assm1 by blast 
    then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf lt (l2',l_pc2',l_jump2') = (l,l_pc,l_jump)" by auto

    hence "l_jump2' = update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims by force 
    hence b1:"l_jump2' = (let (num,off,l_bin0) = a in  if (\<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst)) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)] else l_jump1)" using update_l_jump_def by simp
    thus ?case
    proof(cases "\<not>(\<exists> src dst. x64_decode 0 (snd (snd a)) = Some(3, Pcmpq_rr src dst))")
      case True
      have b2_1:"l_jump2' = l_jump1" using b1 True  by (smt (verit, best) case_prod_conv split_pairs)
      have b2_2:"length l_pc2' = length l_pc1 + 1" using b0 l_pc_length_prop by force 
      hence "\<forall> x. x < length l_pc1 \<longrightarrow> x < length l_pc2'" by auto
      hence "is_increase_list l_jump2' l_pc2'" using assm0 is_increase_list_def b2_1 by simp
      hence "is_increase_list l_jump l_pc" using b0 Cons.hyps by blast 
      then show ?thesis by simp
    next
      case False
      have b2_0:"l_jump2' = l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + (fst (snd a)))]" 
        using False b1 by (smt (verit, ccfv_threshold) old.prod.case prod.collapse) 
      hence b3:"\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_jump1 \<longrightarrow> fst (l_jump2'!idx1) < fst (l_jump2'!idx2)" using b2_0 assm0
        by (simp add: is_increase_list_def nth_append)  
      have b4:"nat (fst (l_jump2'!(length l_jump1))) = (length l_pc1)" using b2_0 by simp
      have b5:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> nat (fst (l_jump1!idx)) < (length l_pc1))"
        using assm0 is_increase_list_def by blast 
      hence "(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> (fst (l_jump1!idx)) < (fst (l_jump2'!(length l_jump1))))"
        using b4 b5 by (metis zless_nat_conj) 
      hence b7_1:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> (fst (l_jump2'!idx)) < (fst (l_jump2'!(length l_jump1))))" by (simp add: b2_0 nth_append) 
      hence b7:"(\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_jump2' \<longrightarrow> fst (l_jump2'!idx1) < fst (l_jump2'!idx2))" 
        using b7_1 by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 b2_0 b3 length_append less_SucE list.size(3) list.size(4)) 

      have "(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> nat (fst (l_jump1!idx)) < (length l_pc2'))"
        using b5 by (metis b0 l_pc_length_prop trans_less_add2) 
      hence b6:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump2' \<longrightarrow> nat (fst (l_jump2'!idx)) < (length l_pc2'))"
        by (smt (verit, ccfv_SIG) One_nat_def add.commute b0 b2_0 b4 l_pc_length_prop length_append less_Suc_eq list.size(3) list.size(4) nth_append plus_1_eq_Suc) 
          
      hence "is_increase_list l_jump2' l_pc2'"
        using b6 b7 is_increase_list_def by simp
      then show ?thesis using b0 Cons by blast
    qed
  qed

lemma l_jump_is_distinct:"is_increase_list l_jump1 l_pc1 \<Longrightarrow> jitflat_bpf lt (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow> distinct (map fst l_jump1) \<Longrightarrow> distinct (map fst l_jump)"
proof(induct lt arbitrary: l1 l_pc1 l_jump1 l_bin l_pc l_jump)
  case Nil
  then show ?case by simp
next
  case (Cons a lt)
  assume a0:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump)" and 
  a1:"distinct (map fst l_jump1)" and
  a3:"is_increase_list l_jump1 l_pc1"
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" using jitflat_bpf_induct a0 by simp
  then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" by auto
  hence "l_jump2' = update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims by force 
  hence b1:"l_jump2' = (let (num,off,l_bin0) = a in  if (\<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst)) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)] else l_jump1)" using update_l_jump_def by simp
  thus ?case
  proof(cases "\<not>(\<exists> src dst. x64_decode 0 (snd (snd a)) = Some(3, Pcmpq_rr src dst))")
    case True
    have b2_1:"l_jump2' = l_jump1" using b1 True  by (smt (verit, best) case_prod_conv split_pairs)
    hence b2:"distinct (map fst l_jump2')" using a1 by simp
    have "is_increase_list l_jump2' l_pc2'" using  l_jump_elem_increases a3 b0 by blast
    hence "distinct (map fst l_jump)" using b0 b1 b2 Cons b2_1 by blast
    then show ?thesis using a1 by simp
  next
    case False
    have b2_0:"l_jump2' = l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + (fst (snd a)))]" 
      using False b1 by (smt (verit, ccfv_threshold) old.prod.case prod.collapse) 
    hence " (\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> nat (fst (l_jump1!idx)) <  (length l_pc1))" using b0 False a3 l_jump_elem_increases a3 b0 is_increase_list_def by blast
    hence b2_1:" (\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> nat (fst (l_jump1!idx)) \<noteq>  (length l_pc1))" by fastforce
    have b2_2:"nat(of_nat (length l_pc1)) = (length l_pc1)" by auto
    hence "\<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 \<noteq> of_nat (length l_pc1)" using b2_1 b2_2
      by (metis eq_fst_iff in_set_conv_nth le0) 
    hence "\<forall> elem1. elem1 \<in> set (map fst l_jump1) \<longrightarrow> elem1 \<noteq> of_nat (length l_pc1)" by auto
    
    hence "distinct ((map fst l_jump1) @ [of_nat (length l_pc1)])" using Cons.prems(3) by auto 
    hence b2:"distinct (map fst l_jump2')" using b2_0 by simp
    then show ?thesis using Cons b2 b0 l_jump_elem_increases by blast 
  qed
qed


lemma flattern_jump_index_easy:
  "jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  find_target_pc_in_l_pc l_jump (of_nat(length(l_pc1))+uint pc) = Some npc \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow>
  pc = 0 \<Longrightarrow>
  distinct (map fst l_jump1) \<Longrightarrow>
  is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  npc = off + (of_nat(length(l_pc1))+pc)"
proof-
  assume a0:"jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump)" and
  a1:"lt!(unat pc) = (num,off,l)" and
  a2:"find_target_pc_in_l_pc l_jump (int(length(l_pc1))+uint pc) = Some npc" and
  a3:"lt \<noteq> []" and
  a4:"pc = 0" and
  a5:"distinct (map fst l_jump1)" and
  a6:"is_increase_list l_jump1 l_pc1"
  let "?xs" = "tl lt"
  let "?len" = "(length(l_pc1))"
  have a7:"(num,off,l)#?xs = lt" using a1 a3 a4
    by (metis list.collapse nth_Cons_0 unat_0) 
  have b0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
  let curr_pc = of_nat (length l1) in 
  let l_jump' = update_l_jump (num,off,l) l_pc1 l_jump1 in
      jitflat_bpf ?xs (
        l1@l,
        l_pc1@[(curr_pc,num)],
        l_jump'))" using a0 a4 by auto 
  have b1_1:"l_jump \<noteq> []" using a2 by force 
  have b1:"distinct (map fst l_jump)" using l_jump_is_distinct a0 a5 a6 by blast
  have "int ?len = (int(length(l_pc1))+uint pc)" using a4 by simp
  hence b2:"(int ?len,npc) \<in> set l_jump" using a2 a4 b1 search_l_jump by auto 
   (* by (metis bot_nat_0.extremum_strict in_set_conv_nth list.size(3) list_in_list.simps(1) list_in_list.simps(2) list_in_list_implies_set_relation) *)
  have b3:"update_l_jump (num,off,l) l_pc l_jump = (
  if (\<exists> src dst. x64_decode 0 l = Some(3, Pcmpq_rr src dst)) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
  else l_jump)" 
    apply(unfold update_l_jump_def Let_def,simp_all) done
  have b4:"l_jump \<noteq> []" using a2 by auto
  thus ?thesis
  proof(cases "(\<exists> src dst. x64_decode 0 l = Some(3, Pcmpq_rr src dst)) ")
    case True
    have c0_0:"update_l_jump (num,off,l) l_pc1 l_jump1 = l_jump1@[(int ?len, of_nat ?len+off)]" using True b0 update_l_jump_def by simp 
    hence c0_1:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
        jitflat_bpf ?xs (l1@l,l_pc1@[(of_nat (length l1),num)],l_jump1@[(int ?len, of_nat ?len+off)]))" 
      using b0 by presburger  
    have "\<exists> l1' l_pc1' l_jump1'. jitflat_bpf [(num,off,l)] (l1,l_pc1,l_jump1) = (l1',l_pc1',l_jump1') \<and> jitflat_bpf ?xs (l1',l_pc1',l_jump1') = (l_bin,l_pc,l_jump)" 
      using jitflat_bpf_induct a0 a7 by presburger 
    then obtain l1' l_pc1' l_jump1' where c0:"jitflat_bpf [(num,off,l)] (l1,l_pc1,l_jump1) = (l1',l_pc1',l_jump1') \<and> jitflat_bpf ?xs (l1',l_pc1',l_jump1') = (l_bin,l_pc,l_jump)" by auto
    hence c1:"l_jump1' = l_jump1@[(int ?len, of_nat ?len+off)]" using c0 c0_1 c0_0 by simp
    hence "list_in_list (l_jump1@[(int ?len, of_nat ?len+off)]) 0 l_jump" using a0 a7 not_change_prefix_l_jump b1_1 c1 c0 by blast
    hence "list_in_list [(int ?len, of_nat ?len+off)] (length l_jump1) l_jump" by (simp add: list_in_list_concat) 
    hence "(int ?len, of_nat ?len+off) \<in> set l_jump" sorry (*using list_in_list_implies_set_relation by metis*)
    hence "npc = off + of_nat ?len+pc" using a4 a2 b1 b2 eq_key_imp_eq_value by (metis add.commute add.right_neutral) 
    then show ?thesis by simp
  next
    case False
    have "update_l_jump (num,off,l) l_pc1 l_jump1 = l_jump1" using False b0 update_l_jump_def by simp
    hence "jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = jitflat_bpf ?xs (l1@l,l_pc1@[(of_nat (length l1),num)],l_jump1)"  using b0 init_second_layer_def by fastforce
    hence "\<not>(\<exists> x. x \<in> set l_jump \<and> fst x = (int ?len+uint pc))" using b4 a3 a0 l_jump_elem_increases a3 a6 is_increase_list_def a6 sorry
    hence "find_target_pc_in_l_pc l_jump (int ?len+uint pc) = None" using a4 b2 by auto
    then show ?thesis using a2 by fastforce 
  qed
qed

lemma flattern_jump_index:
  "jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  distinct (map fst l_jump1) \<Longrightarrow>
  unat pc < length lt \<and> unat pc \<ge> 0  \<Longrightarrow>
  is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  find_target_pc_in_l_pc l_jump (of_nat (length l_pc1) + uint pc) = Some npc \<longrightarrow> npc = off + (of_nat (length l_pc1) + pc)"
  proof(induct lt arbitrary: l1 l_pc1 l_jump1 l_bin l_pc l_jump pc num off l npc)
    case Nil
    then show ?case by simp
  next
    case (Cons a lt)
    assume assm0:"jitflat_bpf (a#lt) (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump)" and
      assm1:"(a#lt)!(unat pc) = (num,off,l)" and
      assm2:"distinct (map fst l_jump1)" and
      assm3:"unat pc < length (a#lt) \<and> unat pc \<ge> 0" and
      assm5:"is_increase_list l_jump1 l_pc1"
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
      show ?case
      proof(cases "unat pc = 0")
        case True
        then show ?thesis 
          using flattern_jump_index_easy True assm0 assm1 assm2 assm3 unat_eq_zero init_second_layer_def
          using Cons.prems(3) assm0 assm1 flattern_jump_index_easy unat_eq_zero assm5 by blast
      next
        case False
        have a1:"pc \<ge>1" using False a0 linorder_le_less_linear by force 
        let "?pc" = "pc -1"
        have b1:"unat ?pc < length lt \<and> (0::nat) \<le> unat ?pc" using assm3 a1 False unat_sub by fastforce 
        let "?x" = "tl lt"
        have b2:"lt ! (unat ?pc) = (num, off, l)" using assm1 False by (simp add: a1 unat_sub)      

        have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf lt (l2',l_pc2',l_jump2') = (l_bin,l_pc,l_jump)" 
          using jitflat_bpf_induct assm0 by blast 
        then obtain l2' l_pc2' l_jump2' where b3_1:"jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf lt (l2',l_pc2',l_jump2') = (l_bin,l_pc,l_jump)" by auto
        
        have "jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin, l_pc, l_jump) \<Longrightarrow> lt ! unat pc = (num, off, l) \<Longrightarrow> distinct (map fst l_jump1) \<Longrightarrow>
        unat pc < length lt \<and> (0::nat) \<le> unat pc \<Longrightarrow> find_target_pc_in_l_pc l_jump (of_nat (length l_pc1)+ uint pc) = Some npc \<Longrightarrow> npc = off + (of_nat (length l_pc1) + pc)" using Cons by blast
        have "distinct (map fst l_jump2')" using l_jump_is_distinct b3_1 assm0 assm2  assm5 by blast
        hence b4:"find_target_pc_in_l_pc l_jump ((of_nat (length l_pc2'))+uint ?pc) = Some npc \<longrightarrow> npc = off + ((of_nat (length l_pc2'))+?pc)" using Cons b1 b2 b3_1 l_jump_elem_increases by blast 
        have b5:"length l_pc2' = length l_pc1 + 1" using b3_1 l_pc_length_prop by force
        
        have "find_target_pc_in_l_pc l_jump ((of_nat (length l_pc1))+uint pc) = Some npc \<longrightarrow> npc = off +  ((of_nat (length l_pc1))+pc)" 
          using b4 b5 by (smt (verit, best) a1 add.commute diff_add_cancel group_cancel.add2 of_nat_1 of_nat_add uint_sub_lem unsigned_1 word_less_eq_iff_unsigned) 
        then show ?thesis by force 
      qed
    qed

end