theory JITFlattern_aux
  imports JITFlattern_def
begin
lemma jitflat_bpf_induct:
  "jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> 
   \<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)"
  by (smt (verit) fst_conv jitflat_bpf.elims list.distinct(1) list.sel(3) nth_Cons_0 snd_conv)

lemma jitflat_bpf_induct2:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2) \<Longrightarrow> jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)"
  using jitflat_bpf.elims by force


lemma jitflat_bpf_induct3:
  "jitflat_bpf (xs1@xs2) (l1,l_pc1,l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> 
   \<exists> l2' l_pc2' l_jump2'. jitflat_bpf xs1 (l1,l_pc1,l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf xs2 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)"
proof(induct xs1 arbitrary: xs2 l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case by simp
next
  case (Cons a xs1)
  assume a0:"jitflat_bpf ((a#xs1)@xs2) (l1,l_pc1,l_jump1)= (l2, l_pc2, l_jump2)" 
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2', l_pc2', l_jump2')  \<and> jitflat_bpf (xs1@xs2) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" 
    using jitflat_bpf_induct a0 by (metis append_Cons) 
  then obtain l2' l_pc2' l_jump2' where a1:"jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2', l_pc2', l_jump2')  \<and> jitflat_bpf (xs1@xs2) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" by auto
  hence "jitflat_bpf (xs1@xs2) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" apply rule by simp
  hence a2:"\<exists> l2'' l_pc2'' l_jump2''. jitflat_bpf xs1 (l2', l_pc2', l_jump2')  = (l2'', l_pc2'', l_jump2'') \<and> 
         jitflat_bpf xs2 (l2'', l_pc2'', l_jump2'') = (l2, l_pc2, l_jump2) " using Cons by blast
  then obtain l2'' l_pc2'' l_jump2'' where a3:"jitflat_bpf xs1 (l2', l_pc2', l_jump2')  = (l2'', l_pc2'', l_jump2'') \<and> 
         jitflat_bpf xs2 (l2'', l_pc2'', l_jump2'') = (l2, l_pc2, l_jump2) " by auto
  then show ?case using a0 a1 a2 a3 jitflat_bpf_induct2 
    by (smt (verit) jitflat_bpf.elims jitflat_bpf.simps(1) jitflat_bpf.simps(2) list.sel(3) nth_Cons_0) 
qed




(*
lemma list_in_list_prop1:"list_in_list l2 (length l1) (l1@l2@l3) \<Longrightarrow> 
  list_in_list (l1@l2@l3) (length l1') (l1'@((l1@l2@l3))@l3') \<Longrightarrow>
  list_in_list l2 (length l1+length l1') (l1'@((l1@l2@l3))@l3')"
  sorry*)

(*lemma "list_in_list l xpc l_bin \<Longrightarrow> length l = len \<Longrightarrow> l  \<noteq> [] \<Longrightarrow> 
  idx \<ge>0 \<and> idx < len \<Longrightarrow> l!idx = l_bin!(xpc+idx)"
  apply(induction l arbitrary:xpc l_bin len idx)
   apply simp
  subgoal for a l xpc l_bin len idx 
    sorry
  done
*)
value "take 0 [1::nat,2]"
(*value "take 0 ([]::nat)"*)
value "list_in_list [] 0 [1::nat,2]"
(*\<forall> idx. idx \<ge>0 \<and> idx < len \<longrightarrow> l!idx = l_bin!(xpc+idx)   l  \<noteq> [] *)
(*lemma list_in_list_prop4:"list_in_list l 0 l_bin \<Longrightarrow> l_bin \<noteq> [] \<Longrightarrow> take (length l) l_bin = l"
  sorry*)

(*value "x64_decode 0 []"*)

(*lemma list_in_list_prop2:"l_bin \<noteq> [] \<Longrightarrow>list_in_list l xpc l_bin \<Longrightarrow> x64_decode x l = x64_decode (xpc+x) l_bin"
  sorry*)


lemma list_in_list_prop2:"list_in_list l xpc l_bin \<Longrightarrow> x64_decode x l = Some v \<Longrightarrow> x64_decode (xpc+x) l_bin = Some v"
  sorry


lemma not_change_prefix_l_bin:
  "jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> list_in_list l1 0 l2"
proof(induction l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case using list_in_list_prop
    by fastforce 
next
  case (Cons a l_bin0)
  have assm1:"jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)" using Cons by blast
  have assm2:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> list_in_list l1 (0::nat) l2"
    using Cons by simp

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')"  by (meson prod_cases3)
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')" by auto

  let "?num" = "fst a"
  let "?off" = "fst (snd a)"
  let "?l_bin0" = "snd (snd a)"
  have a3:"jitflat_bpf [(?num,?off,?l_bin0)] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"  
    using jitflat_bpf.simps(2) by blast
  have a4:"l1@?l_bin0 = l2'" using a3
    by (smt (verit) a0 jitflat_bpf.simps(1) split_pairs) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  have a5:"list_in_list l1 (0::nat) l2'" using a4 list_in_list_concat list_in_list_prop by blast
  have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis

  have a7:"list_in_list l2' 0 l2" using a6 by (simp add: Cons.IH) 
  have a6:"list_in_list l1 (0::nat) l2" using a7 a4 list_in_list_concat by blast 
  then show ?case by simp
qed


lemma not_change_prefix_l_pc:
  "jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> list_in_list l_pc1 0 l_pc2"
  proof(induction l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case using list_in_list_prop
    by fastforce 
next
  case (Cons a l_bin0)
  have assm1:"jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)" using Cons by blast
  have assm2:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> list_in_list l_pc1 0 l_pc2"
    using Cons by simp

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')"  by (meson prod_cases3)
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')" by auto

  let "?num" = "fst a"
  let "?off" = "fst (snd a)"
  let "?l_bin0" = "snd (snd a)"
  have a3:"jitflat_bpf [(?num,?off,?l_bin0)] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"  using jitflat_bpf.simps(2) by blast
  have a4:"l_pc1@[(of_nat (length l1),?num)] = l_pc2'" using a3
    by (smt (verit) a0 jitflat_bpf.simps(1) split_pairs) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  have a5:"list_in_list l_pc1 0 l_pc2'" using a4 list_in_list_concat list_in_list_prop by blast
  have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis

  have a7:"list_in_list l_pc2' 0 l_pc2" using a6 a5 by (simp add: Cons.IH)  
  have a6:"list_in_list l_pc1 (0::nat) l_pc2" using a7 a4 list_in_list_concat by blast 
  then show ?case by simp
qed

lemma l_pc_length_prop:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> length l_pc2 = length l_bin0 + length l_pc1"
proof(induct l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case by simp
next
  case (Cons a l_bin0)
  assume assm0:"jitflat_bpf (a#l_bin0)  (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)"
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf l_bin0 (l2',l_pc2',l_jump2') = (l2,l_pc2,l_jump2)" using jitflat_bpf_induct assm0 by simp
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf l_bin0 (l2',l_pc2',l_jump2') = (l2,l_pc2,l_jump2)" by auto
  hence a1:"length l_pc2 = length l_bin0 + length l_pc2'" using Cons by blast
  have a2:"length l_pc2' = 1 + length l_pc1" using a0
    by (smt (verit) One_nat_def add.commute fst_conv jitflat_bpf.elims length_append list.distinct(1) list.sel(3) list.size(3) list.size(4) plus_1_eq_Suc snd_conv) 
  hence "length l_pc2 = length(a#l_bin0 )+length l_pc1" using a1 a2 by simp
  then show ?case by simp
qed

lemma num_corr:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> map snd (drop (length l_pc1) l_pc2) = map fst l_bin0"
proof(induction l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case by simp
next
  case (Cons a l_bin0)
  have assms1:"jitflat_bpf (a#l_bin0) (l1, l_pc1, l_jump1) = (l2,l_pc2,l_jump2)" using Cons by simp

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" 
    using jitflat_bpf_induct assms1 by (simp add: init_second_layer_def) 
  then obtain l2' l_pc2' l_jump2' where b4:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" by auto
 
  have b5:"list_in_list l_pc1 0 l_pc2" using not_change_prefix_l_pc assms1 by blast
  have b5_1:"list_in_list l_pc2' 0 l_pc2" using not_change_prefix_l_pc b4 by blast

  have b6:"(list_in_list (drop (length l_pc1) l_pc2) (length l_pc1) l_pc2)"
    using b5 list_in_list_concat list_in_list_prop
    using list_in_list.simps(1)
    by (metis (no_types, lifting) append.right_neutral append_take_drop_id drop_eq_Nil2 gen_length_def gen_length_def length_code length_code length_take min.commute nat_le_linear) 

  have b7:"map snd (drop (length l_pc2') l_pc2) = map fst l_bin0" using b4 Cons by blast

  have "jitflat_bpf [a] (l1, l_pc1, l_jump1) = (
      jitflat_bpf [] (
        l1@(snd(snd a)),
        l_pc1@[(of_nat(length l1), fst a)],
        update_l_jump a l_pc1 l_jump1))" using b4
    by (metis jitflat_bpf.simps(2) prod.collapse) 

  hence b8:"l_pc2' = l_pc1@[(of_nat(length l1), fst a)]" using b4 by force
  hence "drop (length l_pc1) l_pc2' = [(of_nat(length l1), fst a)]" by auto

  have "length l_pc1 + 1 = length l_pc2'" using b8 by simp
  hence b10:"(drop (length l_pc1) l_pc2) = (of_nat(length l1), fst a) # (drop (length l_pc2') l_pc2) "
    using b8 b5_1 l_pc_length_prop
    by (metis (no_types, lifting) Cons_nth_drop_Suc ab_semigroup_add_class.add_ac(1) add.right_neutral 
        add_Suc_right assms1 gen_length_def length_Cons length_code less_add_Suc2 list_in_list.simps(2) list_in_list_concat plus_1_eq_Suc) 
    
  hence"map snd (drop (length l_pc1) l_pc2) = fst a # map fst l_bin0" using b7 b8 by force 
  hence " map snd (drop (length l_pc1) l_pc2) = map fst (a # l_bin0)" by simp

  then show ?case by simp
qed

lemma not_change_prefix_l_jump:
  "jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> list_in_list l_jump1 0 l_jump2"
proof(induction l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case using list_in_list_prop
    by fastforce 
next
  case (Cons a l_bin0)
  have assm1:"jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)" using Cons by blast
  have assm2:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> list_in_list l_jump1 0 l_jump2"
    using Cons by simp

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')"  by (meson prod_cases3)
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')" by auto

  let "?num" = "fst a"
  let "?off" = "fst (snd a)"
  let "?l_bin0" = "snd (snd a)"
  have a3:"jitflat_bpf [(?num,?off,?l_bin0)] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"  using jitflat_bpf.simps(2) by blast
  have a4:"l_jump2' = (let (num,off,l_bin0) = a in  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)]
  else l_jump1)" using a3 a0 update_l_jump_def by auto
  hence a4:"l_jump2' = (if ?l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + ?off)]
  else l_jump1)" by (smt (verit) case_prod_conv prod.collapse) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  thus ?case
  proof(cases " ?l_bin0!1 = (0x39::u8)")
    case True
    have "l_jump2' = l_jump1@[(of_nat (length l_pc1), of_nat (length l_pc1) + ?off)]" using True a4 by simp
    hence a5:"list_in_list l_jump1 0 l_jump2'" using list_in_list_concat list_in_list_prop by blast 
    have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis
  
    have a7:"list_in_list l_jump2' 0 l_jump2" using a6 a5 by (simp add: Cons.IH)  
    have "list_in_list l_jump1 (0::nat) l_jump2" using a7 a4 list_in_list_concat by metis
    then show ?thesis by simp
  next
    case False
    have "l_jump2' = l_jump1" using False a4 by simp
    hence a5:"list_in_list l_jump1 0 l_jump2'" using  list_in_list_prop by blast
    have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis
  
    have a7:"list_in_list l_jump2' 0 l_jump2" using a6 a5 by (simp add: Cons.IH)  
    have "list_in_list l_jump1 (0::nat) l_jump2" using a7 a4 list_in_list_concat by metis
    then show ?thesis by simp
  qed
qed


lemma nat_of_nat_trans:"x < u64_MAX \<Longrightarrow> of_nat(unat x) = (x::u64)"
  using u64_MAX_def of_nat_def by simp

lemma "x\<ge>0 \<and> y\<ge>0  \<Longrightarrow> ((of_nat x) ::int) = ((of_nat y) ::int)  \<Longrightarrow> x = y" by presburger
 
(*


  value "unat((of_nat 100)::u64)"
  value "of_nat 0::u64"
 value "of_nat 2::u64"
lemma of_nat_nat_trans:"x = 100 \<Longrightarrow> unat((of_nat x)::u64) = (x::nat)"

proof-
  assume assm0:"x = 100"
  have "\<exists> x1. x1 = ((of_nat x)::u64)" by simp
  then obtain x1 where a0:"x1 = ((of_nat x)::u64)" by auto
  have a1:"of_nat(unat x1) = x1" using assm0 by simp
  have a2:"\<exists> x2. x2 = (unat ((of_nat x)::u64))" by simp
  then obtain x2 where a3:"x2 = (unat ((of_nat x)::u64))" by auto
  have "of_nat (unat ((of_nat x)::u64)) = ((of_nat x)::u64)" by (simp add: a0 a3)  
  hence "(unat ((of_nat x)::u64)) = x" using of_nat_def 
  let "?x" = "(of_nat x)::u64"
  have "of_nat(unat ?x) = ?x" sorry
  let "?y" = "(unat ((of_nat x)::u64))"
  have "of_nat(?y) = ?x" by simp 
  hence "(unat ((of_nat x)::u64)) = x" apply (simp add: of_nat_def)
  thus ?thesis *)
(*
lemma hh:"jitflat_bpf lt init_second_layer = prog \<Longrightarrow> fst prog = concat(map snd (map snd lt))"
  sorry

(*length (snd(snd(lt!idx))) \<le> 10*)
lemma hhh:
  "jitflat_bpf lt init_second_layer = prog \<Longrightarrow> 
  \<forall> idx. idx \<ge> 0 \<and> idx < length (map snd (map snd lt)) \<longrightarrow> length ((map snd (map snd lt))!idx) \<le> 10 \<Longrightarrow> 
  0 < length lt \<and> length lt \<le> 100000 \<Longrightarrow>  
  length (fst prog)\<le>1000000"
  using hh sorry
*)

lemma hh:"jitflat_bpf lt (l1,l_pc1,l_jump1) = prog \<Longrightarrow> fst prog = l1@ concat(map snd (map snd lt))"
  sorry

(*length (snd(snd(lt!idx))) \<le> 10*)
lemma hhh:
  "jitflat_bpf lt (l1,l_pc1,l_jump1) = prog \<Longrightarrow> 
  \<forall> idx. idx \<ge> 0 \<and> idx < length (map snd (map snd lt)) \<longrightarrow> length ((map snd (map snd lt))!idx) \<le> 10 \<Longrightarrow> 
  0 < length lt \<and> length lt \<le> 100000 \<Longrightarrow>  
  length (fst prog) - length l1 \<le>1000000"
  using hh sorry

(*
lemma flattern_lbin_easy:
  assumes a0:"l_bin0!0=(num,off,l)" and
   a1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1) ) = xpc" and
   a4:"well_formed_prog l_bin0"
 shows "list_in_list l (unat xpc) l2"
proof-
  let "?xs" = "tl l_bin0"
  have b0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
  let curr_pc = of_nat (length l1) in 
  let l_jump' = update_l_jump (num,off,l) l_pc1 l_jump1 in  
      jitflat_bpf ?xs (l1@l, l_pc1@[(curr_pc,num)], l_jump'))" using a1 by auto

  have b1:"(num,off,l)#?xs = l_bin0" using a0 a1
    by (metis Nitpick.size_list_simp(2) hd_conv_nth list.collapse not_less0) 
  have c0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) =  (jitflat_bpf ?xs (l1@l, l_pc1@[(of_nat (length l1),num)], update_l_jump (num,off,l) l_pc1 l_jump1))"
      using b0 by auto
  have c1_0:"jitflat_bpf ?xs (l1@l, l_pc1@[((of_nat (length l1)),num)],update_l_jump (num,off,l) l_pc1 l_jump1) = (l2,l_pc2,l_jump2)" using c0 a2 b1 by simp 
  have c1_1:"list_in_list (l_pc1@[((of_nat (length l1)),num)]) 0 l_pc2" using c1_0 not_change_prefix_l_pc by simp
  have c1_2:"list_in_list [((of_nat (length l1)),num)] (length l_pc1) l_pc2" using c1_1 list_in_list_concat by force
  have c1:"l_pc2! (length(l_pc1)) = ((of_nat (length l1)),num)" using not_change_prefix_l_pc c1_2 by simp

  have c2:"xpc = of_nat (length l1)" using c1 a3 by simp

  have c3_1:"list_in_list (l1@l) 0 l2" using c1_0 not_change_prefix_l_bin by blast
  have c3_2:"list_in_list l (length l1) l2" using c3_1 list_in_list_concat by (metis plus_nat.add_0)  
  then have c3_3:"unat (of_nat (length l1)) = (length l1)" sorry   
    then show ?thesis by simp    
  qed
*)

(*lemma flattern_l_bin0:
  assumes a0:"l_bin0!(unat pc)=(num,off,l)" and
   a1:"l_bin0 \<noteq> []" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1 + (unat pc))) = xpc"
 shows "list_in_list l (unat xpc) l2"
  sorry*)

(*lemma flattern_l_bin0:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   unat pc < length l_bin0 \<and> unat pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
   fst (l_pc2 ! (length l_pc1 + (unat pc))) = xpc \<Longrightarrow>
   list_in_list l (unat xpc) l2"
proof(induct l_bin0 arbitrary: pc num off l l1 l_pc1 l_jump1 l2 l_pc2 l_jump2 xpc)
  case Nil
  then show ?case by simp
next
  case (Cons a l_bin0)
  assume assm0:"l_bin0!(unat pc)=(num,off,l)" and
   assm1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   assm2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   assm3:"fst (l_pc2 ! (length l_pc1 + (unat pc))) = xpc"
  then show ?case sorry
qed*)


lemma flattern_l_bin0:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   unat pc < length l_bin0 \<and> unat pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow>
   fst (l_pc2 ! (unat pc)) = xpc \<Longrightarrow>
    well_formed_prog l_bin0 \<Longrightarrow>
   list_in_list l (unat xpc) l2"
proof-
  assume assm0:"l_bin0!(unat pc)=(num,off,l)" and
   assm1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   assm2:"jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2)" and
   assm3:"fst (l_pc2 ! (unat pc)) = xpc"and
   assm4:"well_formed_prog l_bin0"

  let "?prefix" = "take (unat pc) l_bin0"
  let "?suffix" = "drop (unat pc+1) l_bin0"
  have "?prefix@[(num,off,l)]@?suffix= l_bin0" using append_take_drop_id assm0
    by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc append_eq_Cons_conv assm1 drop_0 drop_Suc_Cons drop_drop plus_1_eq_Suc self_append_conv2)  
  hence a0:"?prefix@((num,off,l)#?suffix)= l_bin0" by simp

  hence "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf ?prefix init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf ((num,off,l)#?suffix) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" 
    using init_second_layer_def jitflat_bpf_induct3 by (metis assm2) 

  then obtain l2' l_pc2' l_jump2' where c0:"jitflat_bpf ?prefix init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf ((num,off,l)#?suffix) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" by auto

  have c1:"jitflat_bpf ((num,off,l)#?suffix) (l2', l_pc2', l_jump2') = (
    let l_jump' = update_l_jump (num,off,l) l_pc2' l_jump2' in
        jitflat_bpf ?suffix (
          l2'@l,
          l_pc2'@[(of_nat(length l2'),num)],
          l_jump')
  )" using assm2 init_second_layer_def of_nat_def c0 using jitflat_bpf.simps(2) by presburger   

  have c2:"list_in_list l_pc2' 0 l_pc2" using not_change_prefix_l_pc c0 c1 by blast

  have c3:"(l_pc2 ! (unat pc)) = (of_nat(length l2'),num)" using c2 l_pc_length_prop
    by (smt (z3) Cons_nth_drop_Suc Suc_eq_plus1 ab_semigroup_add_class.add_ac(1) add.commute assm1 assm2 c0 c1 diff_add_inverse diff_diff_cancel 
        init_second_layer_def length_drop less_or_eq_imp_le list.size(3) list.size(4) list_in_list.simps(2) list_in_list_concat not_change_prefix_l_pc) 
    
  have c4:"fst (l_pc2 ! (unat pc)) = (of_nat(length l2'))" using c3 by auto
  
  have c6:"list_in_list l (length l2') l2" using c0 c1 not_change_prefix_l_bin
    by (metis (mono_tags, lifting) list_in_list_concat plus_nat.add_0) 

  have c6_0:"0 < length l_bin0 \<and> length l_bin0 \<le> 100000" using well_formed_prog_def assm2 assm4 by simp
  have c6_1:"(\<forall> idx. idx \<ge> 0 \<and> idx < length (map snd (map snd l_bin0)) \<longrightarrow> length ((map snd (map snd l_bin0))!idx) \<le> 10)" 
    using well_formed_prog_def assm2 assm4 by simp

  have "length l2' \<le>1000000" using assm4 hhh assm2 well_formed_prog_def init_second_layer_def sorry
  hence "(unat(of_nat(length l2')))= length l2'" using c6 nat_of_nat_trans sorry  
  hence c7:"list_in_list l (unat(of_nat(length l2'))) l2" using c6 by metis     

    
  have "list_in_list l (unat(fst (l_pc2 ! (unat pc)))) l2" using c7 c4 by metis 
     then show ?thesis using assm3 by force 
   qed


lemma flattern_num:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   unat pc < length l_bin0 \<and> unat pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow>
   snd (l_pc2!(unat pc)) = num"
proof(induct l_bin0 arbitrary: pc num off l l2 l_pc2 l_jump2)
  case Nil 
  have "length l_bin0 = 0" using Nil by simp
  then show ?case using Nil.prems(2) by auto  
    
next
  case (Cons a l_bin0)
  then show ?case
  proof-
  have assm1:"(a # l_bin0) ! unat pc = (num, off, l)" using Cons by simp
  have assm2:"unat pc < length (a # l_bin0) \<and> (0::nat) \<le> unat pc" using Cons by simp
  have assm3:"jitflat_bpf (a # l_bin0) init_second_layer = (l2, l_pc2, l_jump2)" using Cons by simp
  
  have "l_bin0 ! unat pc = (num, off, l) \<Longrightarrow> unat pc < length l_bin0 \<and> (0::nat) \<le> unat pc \<Longrightarrow>
    jitflat_bpf l_bin0 init_second_layer = (l2, l_pc2, l_jump2) \<Longrightarrow> snd (l_pc2 ! unat pc) = num"
    using Cons by simp

  have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
  show ?thesis
  proof(cases "unat pc = 0")
    case True
      have "snd (l_pc2!(unat pc)) = num" using not_change_prefix_l_pc True
        by (smt (verit, ccfv_threshold) append_Nil assm1 assm3 init_second_layer_def jitflat_bpf.simps(2) 
            list_in_list.simps(2) nth_Cons_0 prod.collapse prod.inject)
      then show ?thesis by simp
  next
    case False
      have b0:"unat pc \<ge>1" using False a0 by simp
      let "?pc" = "unat pc -1"
      have b1:"?pc < length l_bin0 \<and> (0::nat) \<le> ?pc" using assm2 b0 using diff_le_self order_le_less_trans by simp
      let "?x" = "tl l_bin0"
      have b2:"l_bin0 ! ?pc = (num, off, l)" using assm1
        by (simp add: False order_neq_le_trans) 
      
      have b2_1:"jitflat_bpf (a#l_bin0) init_second_layer = (
        jitflat_bpf l_bin0 (
          []@(snd(snd a)),
          []@[(0, fst a)],
          update_l_jump a [] []))" using init_second_layer_def 
        by (metis jitflat_bpf.simps(2) list.size(3) prod.exhaust_sel semiring_1_class.of_nat_0) 
  
      hence b2_2:"jitflat_bpf (a#l_bin0) init_second_layer = jitflat_bpf l_bin0 ((snd(snd a)),[(0, fst a)],update_l_jump a [] [])" by auto
      
      have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf l_bin0 init_second_layer = (l2',l_pc2',l_jump2') " by (metis surj_pair)
      then obtain l2' l_pc2' l_jump2' where b3_1:"jitflat_bpf l_bin0 init_second_layer = (l2',l_pc2',l_jump2')" by auto
      (*have b4:"l_bin0 \<noteq> []" sorry*)
  
        have b3:"snd (l_pc2'! ?pc) = num" using Cons False using b0 b1 b2 b3_1 
        by (metis (mono_tags, lifting) order_neq_le_trans unat_gt_0 unat_minus_one) 
  
      have c0:"map snd l_pc2' = map fst l_bin0" using num_corr b3_1 init_second_layer_def
        by (metis append_Nil append_eq_conv_conj) 
      have c1:"map snd l_pc2 = map fst (a#l_bin0)" using num_corr assm3 init_second_layer_def
        by (metis drop0 list.size(3)) 
      (*have c2:"l_pc2 \<noteq> []" using c1 by auto
      have c3:"l_pc2' \<noteq> []" sorry*)
      (*have c2:"map fst (a#l_bin0) = fst a # map fst l_bin0" by auto*)
  
      (*have "\<exists> l2'' l_pc2'' l_jump2''. jitflat_bpf [a] init_second_layer = l2'' l_pc2'' l_jump2''" by blast
      then obtain l2'' l_pc2'' l_jump2'' where "jitflat_bpf [a] init_second_layer = l2'' l_pc2'' l_jump2''" by auto
      have b2_3:"list_in_list [(0, fst a)] 0 l_pc2" using not_change_prefix_l_pc b2_2 assm3 by metis
      have b2_4:"l_pc2!0 = (0, fst a)" using b2_3 by auto*)
      have "map snd l_pc2 = (fst a)#(map snd l_pc2')" using c0 c1 b2_2 by auto
        (*using assm3 b3 init_second_layer_def not_change_prefix_l_pc b2_2 b2_3 b2_4 num_corr *)
      hence "(map snd l_pc2)!(unat pc) = (map snd l_pc2')!?pc" using b3 False by auto
      hence "snd (l_pc2! unat pc) = num" 
        using b3 False by (metis assm2 b1 c0 c1 map_equality_iff nth_map)
      then show ?thesis by auto  
    qed
  qed
qed

(*
lemma flattern_num:
  assumes a0:"l_bin0!(unat pc)=(num,off,l)" and
   a1:"l_pc2 \<noteq> []" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"unat pc < length l_bin0 \<and> unat pc \<ge> 0"
 shows "snd (l_pc2!(length l_pc1 + unat pc)) = num"
  sorry*)



lemma err_is_still_err2:"x64_sem n l Stuck = xst' \<Longrightarrow> xst' = Stuck "
  apply(induct n, simp)
  using perir_step_def
  by auto

lemma intermediate_step_is_ok2:
  "x64_sem n l xst = xst' \<Longrightarrow> n \<ge> 0 \<Longrightarrow> xst' \<noteq> Stuck \<Longrightarrow> \<exists> xpc xrs xm xss. xst = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: l xst xst')
   apply simp apply (meson outcome.exhaust) 
  using err_is_still_err2 by (metis outcome.exhaust)

lemma err_is_still_err3:"flat_bpf_sem n lt (pc,Stuck) = (pc',s') \<Longrightarrow> s' = Stuck "
  apply(induct n, simp)
  using flat_bpf_one_step_def by simp
  

lemma intermediate_step_is_ok3:
  "flat_bpf_sem n lp (pc,s) = s' \<Longrightarrow> n \<ge> 0 \<Longrightarrow> snd s' \<noteq> Stuck \<Longrightarrow> 
  \<exists> xpc xrs xm xss. s = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: lp pc s s')
    apply simp 
  using err_is_still_err
  apply (meson outcome.exhaust)
  by (metis err_is_still_err3 outcome.exhaust prod.collapse) 

 (*l!x \<noteq> 0xe8 \<and> l!x \<noteq> 0xc3 \<and> l!(x+1) \<noteq> (0x39::u8) \<Longrightarrow>*)
lemma list_in_list_prop3:"x64_sem num l_bin (Next (xpc+x) xrs xm xss) = fxst \<Longrightarrow>
   x64_sem num l (Next x xrs xm xss) = xxst \<Longrightarrow>
   list_in_list l xpc l_bin \<Longrightarrow>
   xxst \<noteq> Stuck \<Longrightarrow>
   match_state1 xxst fxst"
proof(induction num arbitrary:l_bin xpc x xrs xm xss fxst l xrs xm xss xxst)
  case 0
  then show ?case using match_state1_def by auto
next
  case (Suc num)
  assume assm0:"x64_sem (Suc num) l_bin (Next (xpc+x) xrs xm xss) = fxst" and
      assm1:"x64_sem (Suc num) l (Next x xrs xm xss) = xxst" and
      assm2:"list_in_list l xpc l_bin" and
      assm3:"xxst \<noteq> Stuck" 
      (*and assm4:"l!x \<noteq> 0xe8 \<and> l!x \<noteq> 0xc3 \<and> l!(x+1) \<noteq> (0x39::u8)"*)

  have "x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) = 
              (case x64_decode (xpc+x) l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem 0 l_bin (exec_instr ins sz (xpc+x) xrs xm xss))" by simp
  hence b0:"x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) = 
              (case x64_decode (xpc+x) l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             (exec_instr ins sz (xpc+x) xrs xm xss))"
    using x64_sem.simps(1) by presburger 

  have "x64_sem 1 l (Next x xrs xm xss) = 
              (case x64_decode x l of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem 0 l (exec_instr ins sz x xrs xm xss))" by simp
  hence d0:"x64_sem 1 l (Next x xrs xm xss) = 
              (case x64_decode x l of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             (exec_instr ins sz x xrs xm xss))"
    using x64_sem.simps(1) by presburger  

  hence "x64_decode x l \<noteq> None" using d0
    by (metis Suc.prems(2) assm3 option.simps(4) x64_sem.simps(3)) 
  hence a0:"x64_decode x l = x64_decode (xpc+x) l_bin"  
   using assm2 list_in_list_prop2 by force

  have d1_0:"x64_sem 1 l (Next x xrs xm xss) \<noteq> Stuck" 
    using assm3 assm1 by (metis err_is_still_err2 plus_1_eq_Suc x64_sem_add) 
  hence d1_1:"x64_decode x l \<noteq> None" using d0 by(cases "x64_decode x l",simp_all)
  hence "\<exists> sz ins. x64_decode x l = Some (sz,ins)" by simp
  then obtain sz ins where d1_2:"x64_decode x l = Some (sz,ins)" by auto
  hence d1:"x64_sem 1 l (Next x xrs xm xss) = (exec_instr ins sz x xrs xm xss)" 
    using d0 by fastforce 

  hence "\<exists> xpc'' xrs'' xm'' xss''. exec_instr ins sz x xrs xm xss = Next xpc'' xrs'' xm'' xss''" 
    using d1 outcome.exhaust d1_0 by metis
  then obtain xpc'' xrs'' xm'' xss'' where d2:"exec_instr ins sz x xrs xm xss = Next xpc'' xrs'' xm'' xss''" by auto

  have b1:"x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) = (exec_instr ins sz (xpc+x) xrs xm xss)"
    using d1_1 d1_2 b0 a0 by simp
  (* have "x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) \<noteq> Stuck" using intermediate_step_is_ok2 sorry*)
  thus ?case
  proof(cases "x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) \<noteq> Stuck")
    case True
    hence "\<exists> xpc' xrs' xm' xss'. exec_instr ins sz (xpc+x) xrs xm xss = Next xpc' xrs' xm' xss'"
       using b1 outcome.exhaust by metis
    then obtain xpc' xrs' xm' xss' where b2:"exec_instr ins sz (xpc+x) xrs xm xss = Next xpc' xrs' xm' xss'" by auto
            (*xpc' = xpc1 + sz \<and> xpc'' = 0 + sz \<and> *)
    have a1:"xrs'' = xrs' \<and> xm'' = xm' \<and> xss'' = xss'"
              using b2 d2 apply(unfold exec_instr_def)
              apply(cases ins,simp_all)
              subgoal for x7 apply(unfold exec_push_def Let_def)
                apply(cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR x7)))",simp_all)
                done
              subgoal for x8 apply(unfold exec_pop_def Let_def)
                apply(cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))",simp_all)
                subgoal for a apply(cases a,simp_all)
                  done
                done
              subgoal for x131 x132 apply(cases "eval_testcond x131 xrs",simp_all)
                subgoal for a 
                  by (metis outcome.inject) 
                done
              subgoal for x151 x152 x153
                apply(unfold exec_store_def,simp_all)
                apply(cases "storev x153 xm (Vlong (eval_addrmode64 x151 xrs)) (Vlong (xrs (IR x152)))",simp_all)
                done
              subgoal for x201 x202 x203 
                apply(unfold exec_load_def,simp_all)
                apply(cases "loadv x203 xm (Vlong (eval_addrmode64 x202 xrs))",simp_all)
                subgoal for a apply(cases a,simp_all)
                  done
                done
              subgoal for x21a 
                apply(unfold exec_call_def,simp_all)
                done
              done

    have a2:"xpc'' = x + sz \<and> xpc'= xpc + x + sz" sorry
  
    let "?x" = "sz+x"
  
    have a3:"match_state1 (Next ?x xrs' xm' xss') (Next (?x + xpc) xrs' xm' xss')"
      using a1 apply(unfold match_state1_def)
      apply(cases "Next ?x xrs' xm' xss'",simp_all)
      done
  
    (*hence a4:"match_state1 (x64_sem 1 l (Next x xrs xm xss)) (x64_sem 1 l_bin (Next (xpc+x) xrs xm xss))" sorry*)
  
    have "x64_sem num l_bin (Next (xpc+x) xrs xm xss) = fxst \<Longrightarrow> 
    x64_sem num l (Next x xrs xm xss) = xxst \<Longrightarrow> 
    list_in_list l xpc l_bin \<Longrightarrow> 
    match_state1 xxst fxst" using Suc by simp
  
    have a5:"x64_sem num l_bin (Next (xpc+?x) xrs' xm' xss') = fxst" 
      using a2 a1
      by (metis Suc.prems(1) ab_semigroup_add_class.add_ac(1) add.commute b1 b2 plus_1_eq_Suc x64_sem_add) 
    have a6:"x64_sem num l (Next ?x xrs' xm' xss') = xxst" using a1 a2
      by (metis Suc.prems(2) add.commute d1 d2 plus_1_eq_Suc x64_sem_add) 
    have "match_state1 xxst fxst" using a6 a5 assm2 Suc by blast
    then show ?thesis by simp
  next
    case False
    have "exec_instr ins sz (xpc+x) xrs xm xss = Stuck" using b1 False by simp
    hence "exec_instr ins sz x xrs xm xss = Stuck" 
       apply(unfold exec_instr_def)
       apply(cases ins,simp_all)
       subgoal for x7 apply(unfold exec_push_def Let_def)
         apply(cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR x7)))",simp_all)
           done
       subgoal for x8 apply(unfold exec_pop_def Let_def)
         apply(cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))",simp_all)
         subgoal for a apply(cases a,simp_all)
         done
       done
       subgoal for x131 x132 apply(cases "eval_testcond x131 xrs",simp_all)
          subgoal for a by (metis outcome.distinct(1))          
          done
          subgoal for x151 x152 x153
            apply(unfold exec_store_def,simp_all)
            apply(cases "storev x153 xm (Vlong (eval_addrmode64 x151 xrs)) (Vlong (xrs (IR x152)))",simp_all)
          done
          subgoal for x201 x202 x203 
            apply(unfold exec_load_def,simp_all)
            apply(cases "loadv x203 xm (Vlong (eval_addrmode64 x202 xrs))",simp_all)
            subgoal for a apply(cases a,simp_all)
            done
          done
          subgoal for x21a 
            apply(unfold exec_call_def,simp_all)
            done
          done
    then show ?thesis using d2 by simp 
  qed
qed

lemma not_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l \<noteq> Some(1,Pret)"
  sorry

lemma not_call_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xe8 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<forall> d. x64_decode pc l \<noteq> Some(5, Pcall_i d)"
  sorry

lemma not_cmp_insn:"l\<noteq>[] \<Longrightarrow> l!(pc+1) \<noteq> 0x39 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<forall> src dst. x64_decode pc l \<noteq> Some(3, Pcmpq_rr src dst)"
  sorry

(*
lemma not_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l \<noteq> Some(1,Pret)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)+
      apply(cases "u32_of_u8_list [137::8 word, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)

       apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
  subgoal for a
apply rule+
      apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (4::8 word) (and (1::8 word) (l ! pc >> (2::nat))))",simp_all)
    apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
    subgoal for aa
    apply rule+
  apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
apply rule+
     apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word)) ",simp_all)
apply rule+
      apply(cases "u32_of_u8_list [1::8 word, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)
      done
    done
subgoal for a
apply rule+
     apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word)) ",simp_all)
apply rule+
      apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
     apply rule+

      apply(cases " u32_of_u8_list [137::8 word, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)

    apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
  
  apply(cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))] ",simp_all)
  
  apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
  subgoal for aa  
     apply(split if_splits,simp_all)+
  sorry

*)

lemma is_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc = 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l = Some(1,Pret)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)
  done  

lemma is_call_insn:"l\<noteq>[] \<Longrightarrow> l!pc = 0xe8 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<exists> d. x64_decode pc l = Some(5, Pcall_i d)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)
  apply(cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)
  done

lemma is_cmp_insn:"l\<noteq>[] \<Longrightarrow> l!(pc+1) = 0x39 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<exists> src dst. x64_decode pc l = Some(3, Pcmpq_rr src dst)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)
  apply(split if_splits,simp_all)
  sorry


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
  
  have c2:"distinct (map fst l_jump) \<Longrightarrow> find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow> (pc::64 word, npc) \<in> set l_jump" using Cons by blast

  have a1:"fst a = pc \<or> fst a \<noteq> pc"
    using word_coorder.extremum word_le_sub1 by blast 
  thus ?case
  proof(cases "fst a = pc")
    case True
    have "snd a = npc"  by (metis True a0 find_target_pc_in_l_pc.simps(2) fst_conv option.inject snd_conv surj_pair) 
    then show ?thesis using True by fastforce 
  next
    case False
    have "fst a \<noteq> pc" using False a1 by simp
    hence "\<exists> x. x \<in> set l_jump \<and> fst x = pc" using a0 c1 c0
      by (smt (verit, best) Cons.hyps eq_fst_iff find_target_pc_in_l_pc.elims list.distinct(1) list.inject) 
    then obtain x where b0:"x \<in> set l_jump \<and> fst x = pc" by auto
    hence "snd x = npc" using a0 c1 c0 c2
      by (metis False eq_key_imp_eq_value find_target_pc_in_l_pc.simps(2) fstI sndI surj_pair) 
    then show ?thesis using c1 b0 by fastforce
  qed
qed

(* \<and> fst (lt!idx2)< length l_pc*)
definition is_increase_list::" ((u64\<times>u64) list) \<Rightarrow> (u64 \<times> nat) list \<Rightarrow> bool" where 
  "is_increase_list lt lt2 \<equiv> (\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length lt \<longrightarrow> fst (lt!idx1) < fst (lt!idx2)) \<and> 
    (\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> unat (fst (lt!idx)) <  (length lt2))"

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
      have b4:"unat (fst (l_jump2'!(length l_jump1))) = (length l_pc1)" using b2_0 sorry
      have b5:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> unat (fst (l_jump1!idx)) < (length l_pc1))"
        using assm0 is_increase_list_def by blast 
      hence "(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> unat (fst (l_jump1!idx)) < (length l_pc2'))"
        by (metis b0 l_pc_length_prop trans_less_add2) 
      hence "(\<forall> idx. idx \<ge>0 \<and> idx < length l_jump2' \<longrightarrow> unat (fst (l_jump2'!idx)) < (length l_pc2'))"
        by (smt (verit, ccfv_SIG) One_nat_def add.commute b0 b2_0 b4 l_pc_length_prop length_append less_Suc_eq list.size(3) list.size(4) nth_append plus_1_eq_Suc) 
      hence "is_increase_list l_jump2' l_pc2'"
        by (smt (verit, best) One_nat_def b5 add.commute b2_0 b3 b4 is_increase_list_def length_append less_Suc_eq list.size(3) list.size(4) nth_append plus_1_eq_Suc word_less_nat_alt) 
      then show ?thesis using b0 Cons by blast
    qed
  qed

lemma l_jump_upperbound_aux:
  "\<exists> lt. jitflat_bpf lt init_second_layer = init_second_layer"
  apply(unfold init_second_layer_def)
  using jitflat_bpf.simps(1) by blast 

(*lemma l_jump_upperbound:
  "is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  snd(snd a) !1 = 0x39 \<Longrightarrow>
  \<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 < of_nat (length l_pc1)"
  using l_jump_elem_increases is_increase_list_def *)


(*
lemma l_jump_upperbound:
  "is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  snd(snd a) !1 = 0x39 \<Longrightarrow>
  \<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 < of_nat (length l_pc1)"
  using l_jump_elem_increases is_increase_list_def 
proof-
  assume 
  assm1:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) " and
  assm2:"snd(snd a) !1 = 0x39" and
  assm3:"is_increase_list l_jump1"
  have a1:"l_jump =  update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims assm1 by force
  hence "l_jump =  (let (num,off,l_bin0) = a in 
  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)]
  else l_jump1)" using update_l_jump_def by simp
  have "[a]\<noteq> []" by simp
  hence a2:"is_increase_list l_jump" using assm1 l_jump_elem_increases assm3 by blast
  hence b0:"l_jump =  l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + fst (snd a))]" using a1 assm2 by (simp add: case_prod_unfold update_l_jump_def) 
  hence b1:"l_jump \<noteq> []" by blast
  have b2:"length l_jump1 < length l_jump" using b0 by simp
  hence b3:"\<forall> idx1. idx1 < length l_jump1 \<and> idx1\<ge>0 \<and> length l_jump1 < length l_jump \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!(length l_jump1))" 
    using a2 b0 b1 b2 is_increase_list_def by blast 
  have b4:"fst (l_jump!(length l_jump1)) = of_nat (length l_pc1)" using b0 by fastforce 
  then show ?thesis using b3 by (smt (z3) assm1 add.commute add.right_neutral add_Suc_right b2 fst_conv in_set_conv_decomp le_add1 le_imp_less_Suc length_Cons length_append list_in_list.simps(2) list_in_list_concat not_change_prefix_l_jump) 
  qed
*)

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
    hence " (\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> unat (fst (l_jump1!idx)) <  (length l_pc1))" using a2 b0 False a3 l_jump_elem_increases a3 b0 is_increase_list_def by blast
    hence b2_1:" (\<forall> idx. idx \<ge>0 \<and> idx < length l_jump1 \<longrightarrow> unat (fst (l_jump1!idx)) \<noteq>  (length l_pc1))" by fastforce
    have b2_2:"unat(of_nat (length l_pc1)) = (length l_pc1)" sorry
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
  find_target_pc_in_l_pc l_jump (of_nat(length(l_pc1))+pc) = Some npc \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow>
  pc = 0 \<Longrightarrow>
  distinct (map fst l_jump1) \<Longrightarrow>
  jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1) \<Longrightarrow>
  is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  npc = off + (of_nat(length(l_pc1))+pc)"
proof-
  assume a0:"jitflat_bpf lt (l1,l_pc1,l_jump1) = (l_bin,l_pc,l_jump)" and
  a1:"lt!(unat pc) = (num,off,l)" and
  a2:"find_target_pc_in_l_pc l_jump (of_nat(length(l_pc1))+pc) = Some npc" and
  a3:"lt \<noteq> []" and
  a4:"pc = 0" and
  a5:"distinct (map fst l_jump1)" and
  a6:"jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)" and
  a6_1:"is_increase_list l_jump1 l_pc1"
  let "?xs" = "tl lt"
  let "?len" = "of_nat(length(l_pc1))"
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
  hence b2:"(?len,npc) \<in> set l_jump" using a2 a4 search_l_jump by simp
  have b3:"update_l_jump (num,off,l) l_pc l_jump = (
  if l!1 = (0x39::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
  else l_jump)" 
    apply(unfold update_l_jump_def Let_def,simp_all) done
  have b4:"l_jump \<noteq> []" using a2 by auto

  have "l!1 = (0x39::u8) \<or> l!1 \<noteq> (0x39::u8)" by auto
  thus ?thesis
  proof(cases "l!1 = (0x39::u8)")
    case True
    have c0_0:"update_l_jump (num,off,l) l_pc1 l_jump1 = l_jump1@[(?len, ?len+off)]" using True b0 update_l_jump_def by simp 
    hence c0_1:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
        jitflat_bpf ?xs (l1@l,l_pc1@[(of_nat (length l1),num)],l_jump1@[(?len, ?len+off)]))" 
      using b0 by presburger  
    have "\<exists> l1' l_pc1' l_jump1'. jitflat_bpf [(num,off,l)] (l1,l_pc1,l_jump1) = (l1',l_pc1',l_jump1') \<and> jitflat_bpf ?xs (l1',l_pc1',l_jump1') = (l_bin,l_pc,l_jump)" 
      using jitflat_bpf_induct a0 a7 by presburger 
    then obtain l1' l_pc1' l_jump1' where c0:"jitflat_bpf [(num,off,l)] (l1,l_pc1,l_jump1) = (l1',l_pc1',l_jump1') \<and> jitflat_bpf ?xs (l1',l_pc1',l_jump1') = (l_bin,l_pc,l_jump)" by auto
    hence c1:"l_jump1' = l_jump1@[(?len, ?len+off)]" using c0 c0_1 c0_0 by simp
    hence "list_in_list (l_jump1@[(?len, ?len+off)]) 0 l_jump" using a0 a7 not_change_prefix_l_jump b1_1 c1 c0 by blast
    hence "list_in_list [(?len, ?len+off)] (length l_jump1) l_jump" by (simp add: list_in_list_concat) 
    hence "(?len,?len+off) \<in> set l_jump" sorry
    hence "npc = off + ?len+pc" using a4 a2 b1 b2 eq_key_imp_eq_value by fastforce   
    then show ?thesis by simp
  next
    case False
    have "update_l_jump (num,off,l) l_pc1 l_jump1 = l_jump1" using False b0 update_l_jump_def by simp
    hence "jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = jitflat_bpf ?xs (l1@l,l_pc1@[(of_nat (length l1),num)],l_jump1)"  using b0 init_second_layer_def by fastforce
    hence "\<not>(\<exists> x. x \<in> set l_jump \<and> fst x = (?len+pc))" using b4 a3 a0 l_jump_elem_increases a3 a6 is_increase_list_def a6_1 sorry
    hence "find_target_pc_in_l_pc l_jump (?len+pc) = None" using a4 b2 by auto

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
  find_target_pc_in_l_pc l_jump (of_nat (length l_pc1) + pc) = Some npc \<longrightarrow> npc = off + (of_nat (length l_pc1) + pc)"
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
        unat pc < length lt \<and> (0::nat) \<le> unat pc \<Longrightarrow> find_target_pc_in_l_pc l_jump (of_nat (length l_pc1)+ pc) = Some npc \<Longrightarrow> npc = off + (of_nat (length l_pc1) + pc)" using Cons by blast

        have b4_0:"jitflat_bpf (somelt@[a]) init_second_layer = (l2',l_pc2',l_jump2')" 
          using assm4 b3_1 by (metis (no_types, opaque_lifting) jitflat_bpf_induct3 prod_cases3) 
        have "distinct (map fst l_jump2')" using l_jump_is_distinct b3_1 assm0 assm2 assm4 assm5 by blast
        hence b4:"find_target_pc_in_l_pc l_jump ((of_nat (length l_pc2'))+?pc) = Some npc \<longrightarrow> npc = off + ((of_nat (length l_pc2'))+?pc)" using Cons b1 b2 b3_1 b4_0 l_jump_elem_increases by blast 
        have b5:"length l_pc2' = length l_pc1 + 1" using b3_1 l_pc_length_prop by force
        
        have "find_target_pc_in_l_pc l_jump ((of_nat (length l_pc1))+pc) = Some npc \<longrightarrow> npc = off +  ((of_nat (length l_pc1))+pc)" 
          using b4 b5 by auto
        then show ?thesis by force 
      qed
    qed
end