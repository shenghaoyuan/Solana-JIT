theory JITFlattern

imports JITFlattern_aux JITFlattern_prob
begin

(*
lemma 
  assumes a0:"\<forall> x y x' y'. (x,y) \<in> set l_jump \<and> (x',y') \<in> set l_jump \<and> x = x'" and
  a1:"find_target_pc_in_l_pc l_jump pc = Some npc" and
  a2:"l_jump \<noteq> []"
  shows"(pc,npc) \<in> set l_jump"
proof-
  have "\<exists> item. item \<in> set l_jump \<and> fst item = pc" using a1 *)


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
    hence b1:"l_jump2' = (let (num,off,l_bin0) = a in  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)] else l_jump1)" using update_l_jump_def by simp
    thus ?case
    proof(cases "(snd (snd a))!1 \<noteq> (0x39::u8)")
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

lemma l_jump_upperbound_aux:
  "\<exists> lt. jitflat_bpf lt init_second_layer = init_second_layer"
  apply(unfold init_second_layer_def)
  using jitflat_bpf.simps(1) by blast 

lemma l_jump_is_distinct:"is_increase_list l_jump1 l_pc1 \<Longrightarrow> \<exists> somelt. jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1) \<Longrightarrow> jitflat_bpf lt (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow> distinct (map fst l_jump1) \<Longrightarrow> distinct (map fst l_jump)"
proof(induct lt arbitrary: l1 l_pc1 l_jump1 l_bin l_pc l_jump)
  case Nil
  then show ?case by simp
next
  case (Cons a lt)
  assume a0:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump)" and 
  a1:"distinct (map fst l_jump1)" and
  a2:"\<exists> somelt. jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)" and
  a3:"is_increase_list l_jump1 l_pc1"
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" using jitflat_bpf_induct a0 by simp
  then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" by auto
  hence "l_jump2' = update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims by force 
  hence b1:"l_jump2' = (let (num,off,l_bin0) = a in  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)] else l_jump1)" using update_l_jump_def by simp
  obtain somelt where "jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)" using a2 by auto
    hence "jitflat_bpf (somelt@[a]) init_second_layer = (l2', l_pc2', l_jump2')"
       using jitflat_bpf_induct3 b0 by (metis (no_types, opaque_lifting) prod_cases3) 
    hence b3:"\<exists> somelt. jitflat_bpf somelt init_second_layer = (l2', l_pc2', l_jump2')" by auto
  thus ?case
  proof(cases "(snd (snd a))!1 \<noteq> (0x39::u8)")
    case True
    have b2_1:"l_jump2' = l_jump1" using b1 True  by (smt (verit, best) case_prod_conv split_pairs)
    hence b2:"distinct (map fst l_jump2')" using a1 by simp
    have "is_increase_list l_jump2' l_pc2'" using  l_jump_elem_increases a3 b0 by blast
    hence "distinct (map fst l_jump)" using b0 b1 b2 Cons a2 b3 b2_1 by simp
    then show ?thesis using a1 by simp
  next
    case False
    have b2_0:"l_jump2' = l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + (fst (snd a)))]" 
      using False b1 by (smt (verit, ccfv_threshold) old.prod.case prod.collapse) 
    hence " (\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> nat (fst (l_jump1!idx)) <  (length l_pc1))" using a2 b0 False a3 l_jump_elem_increases a3 b0 is_increase_list_def by blast
    hence b2_1:" (\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> nat (fst (l_jump1!idx)) \<noteq>  (length l_pc1))" by fastforce
    have b2_2:"nat(of_nat (length l_pc1)) = (length l_pc1)" by auto
    hence "\<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 \<noteq> of_nat (length l_pc1)" using b2_1 b2_2
      by (metis eq_fst_iff in_set_conv_nth le0) 
    hence "\<forall> elem1. elem1 \<in> set (map fst l_jump1) \<longrightarrow> elem1 \<noteq> of_nat (length l_pc1)" by auto
    
    hence "distinct ((map fst l_jump1) @ [of_nat (length l_pc1)])" using Cons.prems(3)  Cons.prems(4) by auto 
    hence b2:"distinct (map fst l_jump2')" using b2_0 by simp
    then show ?thesis using Cons b2 b0 b3 l_jump_elem_increases by blast 
  qed
qed

(*
lemma l_jump_elem_increases:
  "jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow> 
  lt \<noteq> [] \<Longrightarrow> 
  l_jump \<noteq> [] \<Longrightarrow> 
  \<forall> idx1 idx2. idx1 \<ge>0 \<and> idx1 < length l_jump \<and> idx1 < idx2 \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!idx2)"
  sorry
*)

lemma flattern_jump_index_easy:
  "jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  find_target_pc_in_l_pc l_jump (of_nat(length(l_pc1))+uint pc) = Some npc \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow>
  pc = 0 \<Longrightarrow>
  distinct (map fst l_jump1) \<Longrightarrow>
  jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1) \<Longrightarrow>
  is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  npc = off + (of_nat(length(l_pc1))+pc)"
proof-
  assume a0:"jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump)" and
  a1:"lt!(unat pc) = (num,off,l)" and
  a2:"find_target_pc_in_l_pc l_jump (int(length(l_pc1))+uint pc) = Some npc" and
  a3:"lt \<noteq> []" and
  a4:"pc = 0" and
  a5:"distinct (map fst l_jump1)" and
  a6:"jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)" and
  a6_1:"is_increase_list l_jump1 l_pc1"
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
  have b1:"distinct (map fst l_jump)" using l_jump_is_distinct a0 a5 a6 a6_1 by blast
  have "int ?len = (int(length(l_pc1))+uint pc)" using a4 by simp
  hence b2:"(int ?len,npc) \<in> set l_jump" using a2 a4 b1 search_l_jump by auto 
   (* by (metis bot_nat_0.extremum_strict in_set_conv_nth list.size(3) list_in_list.simps(1) list_in_list.simps(2) list_in_list_implies_set_relation) *)
  have b3:"update_l_jump (num,off,l) l_pc l_jump = (
  if l!1 = (0x39::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
  else l_jump)" 
    apply(unfold update_l_jump_def Let_def,simp_all) done
  have b4:"l_jump \<noteq> []" using a2 by auto

  have "l!1 = (0x39::u8) \<or> l!1 \<noteq> (0x39::u8)" by auto
  thus ?thesis
  proof(cases "l!1 = (0x39::u8)")
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
    hence "\<not>(\<exists> x. x \<in> set l_jump \<and> fst x = (int ?len+uint pc))" using b4 a3 a0 l_jump_elem_increases a3 a6 is_increase_list_def a6_1 sorry
    hence "find_target_pc_in_l_pc l_jump (int ?len+uint pc) = None" using a4 b2 by auto

    then show ?thesis using a2 by fastforce 
  qed
qed

lemma flattern_jump_index:
  "jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  distinct (map fst l_jump1) \<Longrightarrow>
  jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1) \<Longrightarrow>
  unat pc < length lt \<and> unat pc \<ge> 0  \<Longrightarrow>
  is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  find_target_pc_in_l_pc l_jump (of_nat (length l_pc1) + uint pc) = Some npc \<longrightarrow> npc = off + (of_nat (length l_pc1) + pc)"
  proof(induct lt arbitrary: l1 l_pc1 l_jump1 l_bin l_pc l_jump pc num off l somelt npc)
    case Nil
    then show ?case by simp
  next
    case (Cons a lt)
    assume assm0:"jitflat_bpf (a#lt) (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump)" and
      assm1:"(a#lt)!(unat pc) = (num,off,l)" and
      assm2:"distinct (map fst l_jump1)" and
      assm3:"unat pc < length (a#lt) \<and> unat pc \<ge> 0" and
      assm4:"jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)" and
      assm5:"is_increase_list l_jump1 l_pc1"
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
      show ?case
      proof(cases "unat pc = 0")
        case True
        then show ?thesis 
          using flattern_jump_index_easy True assm0 assm1 assm2 assm3 unat_eq_zero init_second_layer_def
          using Cons.prems(3) assm0 assm1 flattern_jump_index_easy unat_eq_zero assm4 assm5 by blast
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

        have b4_0:"jitflat_bpf (somelt@[a]) init_second_layer = (l2',l_pc2',l_jump2')" 
          using assm4 b3_1 by (metis (no_types, opaque_lifting) jitflat_bpf_induct3 prod_cases3) 
        have "distinct (map fst l_jump2')" using l_jump_is_distinct b3_1 assm0 assm2 assm4 assm5 by blast
        hence b4:"find_target_pc_in_l_pc l_jump ((of_nat (length l_pc2'))+uint ?pc) = Some npc \<longrightarrow> npc = off + ((of_nat (length l_pc2'))+?pc)" using Cons b1 b2 b3_1 b4_0 l_jump_elem_increases by blast 
        have b5:"length l_pc2' = length l_pc1 + 1" using b3_1 l_pc_length_prop by force
        
        have "find_target_pc_in_l_pc l_jump ((of_nat (length l_pc1))+uint pc) = Some npc \<longrightarrow> npc = off +  ((of_nat (length l_pc1))+pc)" 
          using b4 b5 by (smt (verit, best) a1 add.commute diff_add_cancel group_cancel.add2 of_nat_1 of_nat_add uint_sub_lem unsigned_1 word_less_eq_iff_unsigned) 
        then show ?thesis by force 
      qed
    qed

lemma one_step_equiv_layer1:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, fxst) = fxst'" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xxst) = xxst'" and
   a3:"xxst = Next xpc xrs xm xss" and
   a4:"lt \<noteq> []" and
   a5:"match_state (pc, xxst) (pc, fxst)" and
   a6:"snd xxst' \<noteq> Stuck" and
   a7:"unat pc < length lt \<and> unat pc \<ge> 0" and 
   a8:"well_formed_prog lt" and
   a9:"snd fxst' \<noteq> Stuck"
  shows"match_state xxst' fxst'"
proof-
  have "\<exists> xpc1. fxst = Next xpc1 xrs xm xss" using a3 a5 
    apply(unfold match_state_def match_state1_def) 
    apply(cases fxst,simp_all)
    done
  then obtain xpc1 where a10:"fxst = Next xpc1 xrs xm xss" by auto

  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst (lt!(unat pc))"
  let "?off" = "fst (snd (lt!(unat pc)))"
  let "?l" = "snd (snd (lt!(unat pc)))"
  (*have "\<exists> num off l. (num, off, l) = lt!(unat pc)" using a4 a7 by (metis prod.exhaust_sel) 
  then obtain num off l where b0_0:"(num, off, l) = lt!(unat pc)" by auto*)
  have b0:"(?num, ?off, ?l) = lt!(unat pc)" by simp
 
  let "?xpc" = "fst (l_pc ! (unat pc))"
  have c0:"list_in_list ?l (nat ?xpc) l_bin" 
    using flattern_l_bin0 init_second_layer_def a1 b0 a4 a7 a8 by metis
  let "?prefix" = "take (unat pc) lt"
  let "?suffix" = "drop (unat pc+1) lt"
  have "?prefix@[(?num,?off,?l)]@?suffix= lt" using append_take_drop_id init_second_layer_def
    by (simp add: Cons_nth_drop_Suc a7) 
  hence "?prefix@((?num,?off,?l)#?suffix)= lt" by simp


  have "fxst' = flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, Next xpc1 xrs xm xss)" using a0 a10
    by (metis One_nat_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) old.prod.exhaust) 
  hence c2:"fxst' = (
  if unat pc \<ge> length l_pc \<or> unat pc < 0 then (pc,Stuck) else 
  let num = snd (l_pc!(unat pc)) in 
  let old_xpc = nat (fst (l_pc!(unat pc))) in 
        if xpc1 \<noteq> old_xpc then (pc, Stuck) else 
        if l_bin!(xpc1+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem num l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, Next xpc1 rs1 m1 ss1)
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))" 
    apply(unfold flat_bpf_one_step_def Let_def) 
    using a3 a10 apply(cases "Next xpc1 xrs xm xss",simp_all)
    (*subgoal for x11 by meson *)
    done

 (* hence "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf ?prefix init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf ((?num,?off,?l)#?suffix) (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" 
    using init_second_layer_def jitflat_bpf_induct3 by (metis a1) 

  then obtain l2' l_pc2' l_jump2' where e0:"jitflat_bpf ?prefix init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf ((?num,?off,?l)#?suffix) (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" by auto

  have e1:"jitflat_bpf ((?num,?off,?l)#?suffix) (l2', l_pc2', l_jump2') = (
    let l_jump' = update_l_jump (?num,?off,?l) l_pc2' l_jump2' in
        jitflat_bpf ?suffix (
          l2'@?l,
          l_pc2'@[(of_nat(length l2'),?num)],
          l_jump')
  )" using a1 init_second_layer_def of_nat_def using jitflat_bpf.simps(2) by presburger   

  have e2:"list_in_list l_pc2' 0 l_pc" using not_change_prefix_l_pc e0 e1 by blast

  have e3:"fst (l_pc ! (unat pc)) = of_nat(length l2')" using e2 l_pc_length_prop a1 a7 b0 e0 e1 a4 init_second_layer_def not_change_prefix_l_pc sorry*)

  have c1:"nat ?xpc= xpc1" using a8 c2 a9 by (smt (verit, ccfv_SIG) snd_conv) 

  have "xxst' = perir_step lt (pc,xxst)" using a2 by (metis One_nat_def perir_sem.simps(1) perir_sem.simps(2) split_pairs)

  hence b1:"xxst' = (let (num,off,l) = lt!(unat pc) in 
       if l!0 = 0xc3 then
          let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss')
      else if (l!0 = 0xe8) then 
        let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (off, Next xpc rs' xm ra))
      else if l!1 = (0x39::u8)  then
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck)      
      else
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          (pc+1, xst'))" using perir_step_def b0 a2 a3 apply(cases xxst,simp_all)
    done

  thus ?thesis
  proof(cases "?l!0 = 0xc3")
    case True
    have "xxst' = (let (num,off,l) = lt!(unat pc) in (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss')))"
      using b1 True by (smt (z3) b0 case_prod_conv)
    then show ?thesis sorry
  next
    case False
    have b2:"?l!0 \<noteq> 0xc3" using False by simp
    then show ?thesis   
    proof(cases "?l!0 = 0xe8")
      case True
      have b3:"?l!0 = 0xe8" using True by simp
      have "xxst' = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (?off, Next xpc rs' xm ra)))" using True b1 b0
        by (smt (z3) False case_prod_conv option.case_eq_if) 
      then show ?thesis sorry
    next
      case False
      have b5:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3" using False b2 by simp
      hence bn_1:"?l \<noteq> []" using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
      have bn_2:"?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 

      have c3_0:"list_in_list ?l xpc1 l_bin" using c0 c1 by simp         
      have c3:"l_bin!xpc1 = ?l!0" using c3_0 bn_1 by (metis list.collapse list_in_list.simps(2) nth_Cons_0)
      then show ?thesis      
      proof(cases "?l!1 = (0x39::u8)")
        
        case True
        hence d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (?off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck) )" using True b1 b0 b5
          by (smt (z3) case_prod_conv outcome.exhaust outcome.simps(4) outcome.simps(5))  

        have "l_bin!(xpc1+1) = ?l!1" using c3 c3_0 sorry
        hence d1:"fxst' = (case x64_sem (snd (l_pc!(unat pc))) l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, Next xpc1 rs1 m1 ss1)
          )) " using True a0 c2 a7 c1 a9 by auto    
                
          have "\<exists> fxst1. fxst1 = x64_sem ?num l_bin (Next xpc1 xrs xm xss)" by fastforce
          then obtain fxst1 where d2_0:"fxst1 = x64_sem ?num l_bin (Next xpc1 xrs xm xss)" by auto
          have "\<exists> xxst1. xxst1 = x64_sem ?num ?l (Next 0 xrs xm xss)" by fastforce
          then obtain xxst1 where d2_1:"xxst1 = x64_sem ?num ?l (Next 0 xrs xm xss)" by auto
          have d2:"match_state1 fxst1 xxst1" using d2_0 d2_1 sorry
          have d3:"\<exists> xpc' xrs1 xm1 xss1. Next xpc' xrs1 xm1 xss1 = fxst1" 
            using d2 match_state1_def by (smt (verit, ccfv_threshold) outcome.exhaust outcome.simps(5)) 
          then obtain xpc' xrs1 xm1 xss1 where d4_0:"Next xpc' xrs1 xm1 xss1 = fxst1" by auto
          have "\<exists> xpc''. Next xpc'' xrs1 xm1 xss1 = xxst1" 
            using d3 match_state1_def d4_0 by (smt (verit, ccfv_SIG) d2 outcome.exhaust outcome.simps(4) outcome.simps(5))
          then obtain xpc'' where d4_1:"Next xpc'' xrs1 xm1 xss1 = xxst1" by auto
          have d4:"(snd (l_pc!(unat pc))) = ?num"
            by (metis (mono_tags, lifting) a1 a7 b0 flattern_num) 
          thus ?thesis
          proof(cases "xrs1 (CR ZF) = 1")
            case True
            have d5_0: "xrs1 (CR ZF) = 1" using True by auto
            thus ?thesis
            proof(cases "find_target_pc_in_l_pc l_jump (uint pc) \<noteq> None")
              case True
                have "\<exists> npc. find_target_pc_in_l_pc l_jump (uint pc) = Some npc" using True by simp
                then obtain npc where d5_1:"find_target_pc_in_l_pc l_jump (uint pc) = Some npc" by auto
                hence d5:"npc = ?off+pc" using a1 a4 b0 a7 flattern_jump_index init_second_layer_def l_jump_upperbound_aux is_increase_list_empty
                  by (metis (mono_tags, lifting) add_cancel_left_left distinct.simps(1) list.size(3) map_is_Nil_conv of_nat_unat unsigned_0)                  
                  
                have d6_0:"fxst' =  (npc, (Next (nat (fst (l_pc!(unat npc)))) xrs1 xm1 xss1))" 
                  using d5_0 d5_1 True d4_0 d1 d2_0 d4 by (smt (verit, best) option.simps(5) outcome.simps(4))
                have d6_1:"xxst' = (?off+pc, xxst1)"
                  by (smt (verit, ccfv_threshold) d0 d2_1 d4_1 d5_0 outcome.simps(4)) 

                have "match_state fxst' xxst'" 
                  using d6_0 d6_1 match_state_def d4_1 d5 match_state1_def by auto
                then show ?thesis using match_state_def d6_0 d6_1 match_state1_def \<open>\<And>thesis::bool. (\<And>xpc''::nat. Next xpc'' (xrs1::preg \<Rightarrow> 64 word) (xm1::nat \<Rightarrow> int \<Rightarrow> 8 word option) (xss1::stack_state) = (xxst1::outcome) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by fastforce 
               next
                 case False
                 have "find_target_pc_in_l_pc l_jump (uint pc) = None" using False by simp
                 hence "fxst' = (pc,Stuck)" using a9
                   by (smt (verit, ccfv_SIG) d1 d2_0 d4 d4_0 d5_0 option.case_eq_if outcome.simps(4)) 
                then show ?thesis using a9 by auto
              qed
            next
              case False
              have d5_0:"xrs1 (CR ZF) \<noteq> 1" using False by simp
              have d5_1:"xxst' = (pc+1, xxst1)" by (smt (verit) d0 d2_1 d4_1 d5_0 outcome.simps(4)) 
              have d5_2:"fxst' = (pc+1, fxst1)" 
                using d5_0 by (smt (verit, ccfv_threshold) d1 d2_0 d4 d4_0 outcome.simps(4)) 
            then show ?thesis using d5_1 d5_2 match_state_def d2 d3 d4_1 by force 
        qed

        (*hence bn_0:"x64_decode 0 ?l \<noteq> None" using a6 apply(cases "x64_decode 0 ?l",simp_all) using bn_2
          by (metis (no_types, lifting) Suc_diff_1 option.simps(4) outcome.simps(5) prod.collapse prod.inject x64_sem.simps(3)) 
        have bn_3:"x64_decode 0 ?l \<noteq> Some(1,Pret)" using is_ret_insn bn_0 bn_1 
          by (metis Pair_inject True add_0 is_cmp_insn numeral_eq_one_iff option.sel semiring_norm(86))

        have bn_4:"\<forall> d. x64_decode 0 ?l \<noteq> Some(5, Pcall_i d)"  using is_call_insn bn_0 bn_1 b5 
          using True is_cmp_insn by fastforce *)
       
      next
        case False
          have b6:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3 \<and> ?l!1 \<noteq> (0x39::u8)" using b5 False by blast
          have d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          (pc+1, xst'))" using b6 by (smt (verit) b0 b1 case_prod_conv)
          
          hence bn_0:"x64_decode 0 ?l \<noteq> None" using d0 a6 bn_2 apply(cases "x64_decode 0 ?l",simp_all)
            by (smt (verit) Suc_diff_1 option.simps(4) x64_sem.simps(3))
          hence "x64_decode 0 ?l \<noteq> Some(1,Pret) \<and> (\<forall> d. x64_decode 0 ?l \<noteq> Some(5, Pcall_i d)) \<and> (\<forall> src dst. x64_decode 0 ?l \<noteq> Some(3, Pcmpq_rr src dst))"
            using not_ret_insn not_call_insn not_cmp_insn bn_1 b6 by simp

          (*have bn_3:"x64_decode 0 ?l \<noteq> Some(1,Pret)" using is_ret_insn bn_0 bn_1 b6          

          have bn_4:"\<forall> d. x64_decode 0 ?l \<noteq> Some(5, Pcall_i d)"  using is_call_insn bn_0 bn_1 b5
          using True is_cmp_insn by fastforce *)
                   
        
          have c3_2:"l_bin!(xpc1+1) \<noteq> (0x39::u8)" using c3 c3_0 sorry
          
          have c4:"fxst' = (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))"
            using c2 b6 c3_2 a1 a7 add.right_neutral c1 init_second_layer_def l_pc_length_prop a9 by force 
          have c5_1:"l_pc \<noteq> []"  using a1 a4 apply(unfold init_second_layer_def) using num_corr by fastforce 

          have c5:"fxst' = (pc+1, x64_sem ?num l_bin (Next xpc1 xrs xm xss))"using b0 c5_1 a1 init_second_layer_def c4 a6 a7
            by (metis (mono_tags, lifting) flattern_num)
            

          have cn:"match_state1 (snd xxst') (snd fxst')" using c5 d0 c3_0 list_in_list_prop3
            by (metis add.right_neutral assms(7) snd_conv)
            

          have "fst fxst' = pc+1" using c5 by auto
          moreover have d2:"fst xxst' = pc+1" using d0 by auto
          hence "fst xxst' = fst fxst'" using calculation by presburger 
          hence "match_state xxst' fxst'" using cn match_state_def match_state1_def 
            apply(cases "snd xxst'",simp_all)
            apply(cases "snd fxst'",simp_all)
            by (simp add: case_prod_beta') 
                   
          then show ?thesis by (simp add: c5 d0) 
      qed
    qed
  qed
qed

lemma flat_bpf_sem_induct_aux1:
 "flat_bpf_sem (m+n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem m x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
 apply(induct m arbitrary: n x64_prog xst xst' )
   apply auto[1]
  subgoal for m n x64_prog xst xst'
    apply (simp add: Let_def)
    apply(cases xst;simp)
    done
  done

lemma flat_bpf_sem_induct_aux2:
"flat_bpf_sem (Suc n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem 1 x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
  using flat_bpf_sem_induct_aux1 by simp


lemma err_is_still_err:"perir_sem n lt (pc,Stuck) = (pc',s') \<Longrightarrow> s' = Stuck "
  apply(induct n, simp)
  using perir_step_def
  by auto

lemma intermediate_step_is_ok:"perir_sem n lt (pc,s) = s' \<Longrightarrow> n \<ge> 0 \<Longrightarrow> snd s' \<noteq> Stuck \<Longrightarrow> 
  \<exists> xpc xrs xm xss. s = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: lt pc s s')
  apply simp 
  using err_is_still_err
  apply (meson outcome.exhaust)
  by (metis JITFlattern.err_is_still_err outcome.exhaust prod.collapse) 


lemma n_steps_equiv_layer1:
  "flat_bpf_sem n prog (pc,fxst) = fxst' \<Longrightarrow>
  jitflat_bpf lt init_second_layer = prog \<Longrightarrow>
  perir_sem n lt (pc,xxst) = xxst' \<Longrightarrow>
  xxst = Next xpc xrs xm xss \<Longrightarrow>
  snd xxst' = Next xpc' xrs' xm' xss' \<Longrightarrow>
  match_state (pc,xxst) (pc,fxst) \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow> 
  well_formed_prog lt \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  match_state xxst' fxst'"
proof(induct n arbitrary: prog pc fxst fxst' lt xxst xxst' xpc xrs xm xss xxst' xpc' xrs' xm' xss' xpc'' xrs'' xm'' xss'')
  case 0
  then show ?case apply(unfold match_state_def,simp_all) 
    done
    
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) prog (pc,fxst) = fxst'" and 
  assm1:"jitflat_bpf lt init_second_layer = prog" and
  assm2:"perir_sem (Suc n) lt (pc,xxst) = xxst'" and
  assm3:"xxst = Next xpc xrs xm xss" and
  assm4:"snd xxst' = Next xpc' xrs' xm' xss'" and
  assm5:"lt \<noteq> []" and
  assm6:"match_state (pc,xxst) (pc,fxst)" and
(*  assm7:"unat pc < length lt \<and> unat pc \<ge> 0" and*)
  assm7:"well_formed_prog lt" and
  assm8:"snd fxst' = Next xpc'' xrs'' xm'' xss''"
 
  have "\<exists> next_s. next_s = perir_sem 1 lt (pc,xxst)" by simp
  then obtain next_s pc' where b0:"next_s = perir_sem 1 lt (pc,xxst)" by auto
  have "\<exists> next_f. flat_bpf_sem 1 prog (pc,fxst) = next_f" by blast
  then obtain next_f where b1:"flat_bpf_sem 1 prog (pc,fxst) = next_f" by simp
  (*have b2:"xrs1 = xrs \<and> xm = xm1 \<and> xss = xss1" using match_state_def assm3 assm7 assm6
    apply(cases "fxst",simp_all)
    done*)
  have a0:"perir_sem n lt next_s = xxst'" using x64_sem1_induct_aux3 assm2 b0
    using Suc.prems(3) by presburger 
  have "\<exists> pc' xrs1 xpc1 m1 xss1. (pc', Next xrs1 xpc1 m1 xss1) = next_s" using assm4 a0 intermediate_step_is_ok
    by (metis outcome.exhaust prod.collapse zero_le) 
  then obtain pc' xrs1 xpc1 m1 xss1 where a1:"(pc', Next xrs1 xpc1 m1 xss1) = next_s" by auto
                                                                                                            
  (*have "\<exists> pc'' xrs1' xpc1' m1' xss1'. (pc'', Next xrs1' xpc1' m1' xss1') = next_f" using assm8 intermediate_step_is_ok3 b1
    by (metis Suc.prems(9) assm0 bot_nat_0.extremum flat_bpf_sem_induct_aux2 outcome.distinct(1) prod.exhaust_sel) *)
  have c0_1:"snd next_f \<noteq> Stuck" using assm8 intermediate_step_is_ok3 b1
    by (metis assm0 bot_nat_0.extremum flat_bpf_sem_induct_aux2 outcome.distinct(1) prod.exhaust_sel) 

  hence"(unat pc < length (fst(snd prog)) \<and> unat pc \<ge> 0)" using b1 assm8
    by (smt (z3) One_nat_def case_prod_conv flat_bpf_one_step_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) 
        intermediate_step_is_ok3 linorder_not_less outcome.simps(4) prod.collapse split_pairs zero_order(1)) 

  hence c0:"(unat pc < length lt \<and> unat pc \<ge> 0)" using l_pc_length_prop  init_second_layer_def assm1
    by (metis add.right_neutral list.size(3) prod.collapse) 
  have bn:"match_state next_s next_f"
    using one_step_equiv_layer1 b1 assm1 b0 assm3 assm5 assm6 a1 c0 assm8 c0_1 assm7
    by (metis outcome.distinct(1) prod.collapse snd_conv) 

  have a2:"(pc', snd next_f) = next_f" using bn match_state_def a1 b0 b1
    apply(cases "Next xrs1 xpc1 m1 xss1",simp_all)
    apply(cases "snd next_f",simp_all)
    subgoal for x11 x11a x12 x13 x14 by force
    subgoal for x11 by force
    done

  have c1:"flat_bpf_sem n prog next_f = fxst'" using flat_bpf_sem_induct_aux2 assm0 b1 by blast

  hence "match_state xxst' fxst'" 
    using a0 a1 a2 Suc bn c1 assm5 assm4 by metis
  then show ?case by simp
qed

  

end