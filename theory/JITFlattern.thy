theory JITFlattern

imports JITPer_aux x64Semantics JITPer
begin


type_synonym flat_bpf_prog = "x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)"

definition update_l_jump::"(nat \<times> u64 \<times> x64_bin) \<Rightarrow> (u64 \<times> nat) list \<Rightarrow> (u64\<times>u64) list \<Rightarrow> (u64\<times>u64) list" where
"update_l_jump x l_pc l_jump \<equiv> let l_bin0 = snd(snd x); off = fst(snd x) in
  if l_bin0!1 = (0x39::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
  else l_jump"

fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
  let curr_pc = of_nat (length l_bin) in 
  let l_jump' = update_l_jump (num,off,l_bin0) l_pc l_jump in
      jitflat_bpf xs (
        l_bin@l_bin0,
        l_pc@[(curr_pc,num)],
        l_jump')
)"

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

definition init_second_layer::"x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)" where
"init_second_layer \<equiv> ([],[],[])"
  
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
 

lemma list_in_list_prop2:"list_in_list l xpc l_bin \<Longrightarrow> x64_decode x l = x64_decode (xpc+x) l_bin"
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

lemma flattern_lbin:
  assumes a0:"l_bin0!0=(num,off,l)" and
   a1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1) ) = xpc"
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
  have c3_3:"unat (of_nat (length l1)) = (length l1)" sorry
  have c3:"list_in_list l (unat xpc) l2" using c2 c3_2 c3_3 by metis
    then show ?thesis by simp    
  qed


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
   list_in_list l (unat xpc) l2"
proof-
  assume assm0:"l_bin0!(unat pc)=(num,off,l)" and
   assm1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   assm2:"jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2)" and
   assm3:"fst (l_pc2 ! (unat pc)) = xpc"

  let "?prefix" = "take (unat pc) l_bin0"
  let "?suffix" = "drop (unat pc+1) l_bin0"
  have "?prefix@[(num,off,l)]@?suffix= l_bin0" using append_take_drop_id assm0
    by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc append_eq_Cons_conv assm1 drop_0 drop_Suc_Cons drop_drop plus_1_eq_Suc self_append_conv2)  
  hence "?prefix@((num,off,l)#?suffix)= l_bin0" by simp

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
    by (smt (z3) Cons_nth_drop_Suc Suc_eq_plus1 ab_semigroup_add_class.add_ac(1) add.commute assm1 assm2 c0 c1 diff_add_inverse diff_diff_cancel init_second_layer_def length_drop less_or_eq_imp_le list.size(3) list.size(4) list_in_list.simps(2) list_in_list_concat not_change_prefix_l_pc) 
    
  have c4:"fst (l_pc2 ! (unat pc)) = (of_nat(length l2'))" using c3 by auto
  
  have c6:"list_in_list l (length l2') l2" using c0 c1 not_change_prefix_l_bin
    by (metis (mono_tags, lifting) list_in_list_concat plus_nat.add_0) 
  hence c7:"list_in_list l (unat(of_nat(length l2'))) l2" sorry
  
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
        by (smt (verit, ccfv_threshold) append_Nil assm1 assm3 init_second_layer_def jitflat_bpf.simps(2) list_in_list.simps(2) nth_Cons_0 prod.collapse prod.inject)
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

fun find_target_pc_in_l_pc :: "((u64\<times>u64) list) \<Rightarrow> u64 \<Rightarrow> u64 option" where
"find_target_pc_in_l_pc [] _ = None" |
"find_target_pc_in_l_pc ((x, y)#xs) pc = (
  if x = pc then Some y
  else find_target_pc_in_l_pc xs pc
)"


definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
  let num = snd (l_pc!(unat pc)) in 
    (case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc rs m ss \<Rightarrow> (
        if l_bin!(xpc+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem 1 l_bin (Next xpc rs m ss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (unat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, xst)
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc rs m ss))
)))"

fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ (pc,st) = (pc,st)" |
"flat_bpf_sem (Suc n) lt (pc, xst) = (
   let pair = flat_bpf_one_step lt (pc, xst) in
    flat_bpf_sem n lt pair
)"


definition match_state1::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state1 fxst xxst \<equiv> 
  (case fxst of (Next xst xrs xm xss) \<Rightarrow>
    (case xxst of (Next xst1 xrs1 xm1 xss1) \<Rightarrow> 
     xrs = xrs1 \<and> xm = xm1 \<and> xss = xss1 |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"

definition match_state::"hybrid_state \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "match_state fxst xxst \<equiv> 
  (case fxst of (pc,Next xst xrs xm xss) \<Rightarrow>
    (case xxst of (pc1,Next xst1 xrs1 xm1 xss1) \<Rightarrow> 
      pc = pc1 \<and> match_state1 (Next xst1 xrs1 xm1 xss1) (Next xst xrs xm xss)  |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"
(*x64_decode 0 l = x64_decode xpc l
xxst = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow>
   fxst = Next xpc2 xrs2 xm2 xss2 \<Longrightarrow>
xrs1 = xrs2 \<and> xm1 = xm2 \<and> xss1 = xss2*)

lemma err_is_still_err2:"x64_sem n l Stuck = xst' \<Longrightarrow> xst' = Stuck "
  apply(induct n, simp)
  using perir_step_def
  by auto

lemma intermediate_step_is_ok2:
  "x64_sem n l xst = xst' \<Longrightarrow> n \<ge> 0 \<Longrightarrow> xst' \<noteq> Stuck \<Longrightarrow> \<exists> xpc xrs xm xss. xst = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: l xst xst')
   apply simp apply (meson outcome.exhaust) 
  using err_is_still_err2 by (metis outcome.exhaust)

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
  have a0:"x64_decode x l = x64_decode (xpc+x) l_bin" using assm2 list_in_list_prop2
    by (metis add_0 list_in_list.simps(1))


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
                subgoal for a
                  by (metis outcome.distinct(1))          
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
 
lemma one_step_equiv:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, fxst) = fxst'" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xxst) = xxst'" and
   a3:"xxst = Next xpc xrs xm xss" and
   a4:"lt \<noteq> []" and
   a5:"match_state (pc, xxst) (pc, fxst)" and
   a6:"snd xxst' \<noteq> Stuck" and
   a7:"unat pc < length lt \<and> unat pc \<ge> 0"
  shows"match_state xxst' fxst'"
proof-
  have "\<exists> xpc1. fxst = Next xpc1 xrs xm xss" using a3 a5 
    apply(unfold match_state_def match_state1_def) 
    apply(cases fxst,simp_all)
    done
  then obtain xpc1 where a6:"fxst = Next xpc1 xrs xm xss" by auto

  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst (lt!(unat pc))"
  let "?off" = "fst (snd (lt!(unat pc)))"
  let "?l" = "snd (snd (lt!(unat pc)))"
  have b0:"(?num, ?off, ?l) = lt!(unat pc)" by simp
 
  let "?xpc" = "fst (l_pc ! (unat pc))"
  have c0:"list_in_list ?l (unat ?xpc) l_bin" 
    using flattern_l_bin0 init_second_layer_def a1 b0 a4 a7 by metis
  have c1:"unat ?xpc= xpc1" sorry

  have "fxst' = flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, Next xpc1 xrs xm xss)" using a0 a6
    by (metis One_nat_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) old.prod.exhaust) 
  hence c2:"fxst' = (
  let num = snd (l_pc!(unat pc)) in 
        if l_bin!(xpc1+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem 1 l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (unat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, fxst)
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))" 
    apply(unfold flat_bpf_one_step_def Let_def) 
    using a3 a6 apply(cases "Next xpc1 xrs xm xss",simp_all)
    subgoal for x11 by meson  
    done

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
      then show ?thesis
      proof(cases "?l!1 = (0x39::u8)")
        case True
        hence "xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (?off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck) )" using True b1 b0 b5
          by (smt (z3) case_prod_conv outcome.exhaust outcome.simps(4) outcome.simps(5))  
        then show ?thesis sorry
      next
        case False
        have b6:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3 \<and> ?l!1 \<noteq> (0x39::u8)" using b5 False by blast
          have d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          (pc+1, xst'))" using b6 by (smt (verit) b0 b1 case_prod_conv)
          
          have c3_0:"list_in_list ?l xpc1 l_bin" using c0 c1 by simp
          have c3_1:"?l \<noteq> []" sorry
          have c3:"l_bin!xpc1 = ?l!0" using c3_0 c3_1
            by (metis list_in_list.simps(2) list_in_list_prop neq_Nil_conv) 
           (* by (metis list.collapse list_in_list.simps(2)) *)
          have c3_2:"l_bin!(xpc1+1) \<noteq> (0x39::u8)" sorry
          
          have c4:"fxst' = (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))"
            using c2 c3 b6 c3_2 by presburger 
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


lemma n_steps_equiv:
  "flat_bpf_sem n prog (pc,fxst) = fxst' \<Longrightarrow>
  jitflat_bpf lt init_second_layer = prog \<Longrightarrow>
  perir_sem n lt (pc,xxst) = xxst' \<Longrightarrow>
  xxst = Next xpc xrs xm xss \<Longrightarrow>
  snd xxst' = Next xpc' xrs' xm' xss' \<Longrightarrow>
  match_state (pc,xxst) (pc,fxst) \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow> 
  unat pc < length lt \<and> unat pc \<ge> 0 \<Longrightarrow>
  match_state xxst' fxst'"
proof(induct n arbitrary: prog pc fxst fxst' lt xxst xxst' xpc xrs xm xss xxst' xpc' xrs' xm' xss')
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
  assm7:"unat pc < length lt \<and> unat pc \<ge> 0"
  have "\<exists> next_s. next_s = perir_sem 1 lt (pc,xxst)" by simp
  then obtain next_s pc' where b0:"next_s = perir_sem 1 lt (pc,xxst)" by auto
  have "\<exists> next_f. flat_bpf_sem 1 prog (pc,fxst) = next_f" by blast
  then obtain next_f where b1:"flat_bpf_sem 1 prog (pc,fxst) = next_f" by simp
  (*have b2:"xrs1 = xrs \<and> xm = xm1 \<and> xss = xss1" using match_state_def assm3 assm7 assm6
    apply(cases "fxst",simp_all)
    done*)
  have a0:"perir_sem n lt next_s = xxst'" using x64_sem1_induct_aux3 assm2 b0
    using Suc.prems(3) by presburger 
  have "\<exists> pc' xrs1 xpc1 m1 xss1. (pc', Next xrs1 xpc1 m1 xss1) = next_s" using assm4 a0 intermediate_step_is_ok a0
    by (metis outcome.exhaust prod.collapse zero_le) 
  then obtain pc' xrs1 xpc1 m1 xss1 where a1:"(pc', Next xrs1 xpc1 m1 xss1) = next_s" by auto
  
  have bn:"match_state next_s next_f"
    using one_step_equiv b1 assm1 b0 assm3 assm5 assm6 a1 assm7 by (metis eq_snd_iff outcome.distinct(1)) 

  have a2:"(pc', snd next_f) = next_f" using bn match_state_def a1 b0 b1
    apply(cases "Next xrs1 xpc1 m1 xss1",simp_all)
    apply(cases "snd next_f",simp_all)
    subgoal for x11 x11a x12 x13 x14 by force
    subgoal for x11 by force
    done

  have c0:"flat_bpf_sem n prog next_f = fxst'" using flat_bpf_sem_induct_aux2 assm0 b1 by blast

  have "unat pc' < length lt \<and> unat pc \<ge> 0" sorry
  hence "match_state xxst' fxst'" 
    using a0 a1 a2 Suc bn c0 assm5 assm4 assm7 by (metis bot_nat_0.extremum) 
  then show ?case by simp
qed



end