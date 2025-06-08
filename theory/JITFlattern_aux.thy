theory JITFlattern_aux
  imports JITFlattern_def Proof1 
begin
lemma jitflat_bpf_induct:
  "jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> 
   \<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)"
  by (smt (verit) jitflat_bpf.simps(1) jitflat_bpf.simps(2) old.prod.case prod_cases3)

lemma jitflat_bpf_induct2:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2) \<Longrightarrow> jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)"
  using jitflat_bpf.elims
  by (metis (no_types, opaque_lifting) jitflat_bpf_induct prod_cases3) 


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


value "take 0 [1::nat,2]"
(*value "take 0 ([]::nat)"*)
value "list_in_list [] 0 [1::nat,2]"


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
  let "?k" = "(?num,?off,?l_bin0)"
  have a3:"jitflat_bpf [?k] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"
    by (metis (no_types, lifting) jitflat_bpf.simps(2) old.prod.case)  
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
  let "?k" = "(?num,?off,?l_bin0)"
  have a3:"jitflat_bpf [?k] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"
    by (metis (no_types, lifting) jitflat_bpf.simps(2) old.prod.case)
  have a4:"l_pc1@[(of_nat (length l1),?num)] = l_pc2'" using a3
    by (smt (verit) a0 jitflat_bpf.simps(1) split_pairs) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  have a5:"list_in_list l_pc1 0 l_pc2'" using a4 list_in_list_concat list_in_list_prop by blast
  have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis

  have a7:"list_in_list l_pc2' 0 l_pc2" using a6 a5 by (simp add: Cons.IH)  
  have a6:"list_in_list l_pc1 (0::nat) l_pc2" using a7 a4 list_in_list_concat by blast 
  then show ?case by simp
qed

lemma l_pc_length_prop:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
  length l_pc2 = length l_bin0 + length l_pc1"
  apply(induct l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2; simp)
  subgoal for a l l1 l_pc1 l_jump1 l2 l_pc2 l_jump2
    apply (cases a; simp)
    done
  done

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
    by (metis (mono_tags, lifting) jitflat_bpf.simps(2) old.prod.case prod.collapse)

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
  let "?k" = "(?num,?off,?l_bin0)"
  have a3:"jitflat_bpf [?k] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"
    by (metis (no_types, lifting) case_prod_conv jitflat_bpf.simps(2))  
  have a4:"l_jump2' = (let (num,off,l_bin0) = a in if (\<exists> num d. x64_decode 0 l_bin0 = Some(num, Pcall_i d)) then l_jump1@ [(of_nat (length l_pc1), off)] 
  else if (\<exists> num src dst. x64_decode 0 l_bin0 = Some(num, Pcmpq_rr src dst)) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)]
  else l_jump1)" 
    using a3 a0 update_l_jump_def
    apply(cases "x64_decode 0 (snd (snd a))",simp_all)
       apply(cases a,simp_all)
      subgoal for aa apply(cases a,simp_all)
        apply(cases aa,simp_all)
        subgoal for ab b c aaa ba
          apply(cases ba,simp_all)
          done
        done
      done
  hence a4:"l_jump2' = (if (\<exists> num d. x64_decode 0 ?l_bin0 = Some(num, Pcall_i d)) then l_jump1@ [(of_nat (length l_pc1), ?off)] 
  else if (\<exists> num src dst. x64_decode 0 ?l_bin0 = Some(num, Pcmpq_rr src dst)) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + ?off)]
  else l_jump1)" by (smt (verit) case_prod_conv prod.collapse) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  thus ?case
  proof(cases "(\<exists> num d. x64_decode 0 ?l_bin0 = Some(num, Pcall_i d))")
    case True
    have "l_jump2' = l_jump1@[(of_nat (length l_pc1), ?off)]" using True a4 by simp
    hence a5:"list_in_list l_jump1 0 l_jump2'" using list_in_list_concat list_in_list_prop by blast 
    have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis
    
    have a7:"list_in_list l_jump2' 0 l_jump2" using a6 a5 by (simp add: Cons.IH)  
    have "list_in_list l_jump1 (0::nat) l_jump2" using a7 a4 list_in_list_concat by metis
    then show ?thesis by simp
  next
    case False
    have b0:"\<not> (\<exists> num d. x64_decode 0 ?l_bin0 = Some(num, Pcall_i d))" using False by simp
    then show ?thesis
    proof(cases "(\<exists> num src dst. x64_decode 0 ?l_bin0 = Some(num, Pcmpq_rr src dst))")
      case True
      have "l_jump2' = l_jump1@[(of_nat (length l_pc1), of_nat (length l_pc1) + ?off)]" using True a4 b0 by simp
      hence a5:"list_in_list l_jump1 0 l_jump2'" using list_in_list_concat list_in_list_prop by blast 
      have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis
    
      have a7:"list_in_list l_jump2' 0 l_jump2" using a6 a5 by (simp add: Cons.IH)  
      have "list_in_list l_jump1 (0::nat) l_jump2" using a7 a4 list_in_list_concat by metis
      then show ?thesis by simp
    next
      case False
      have "l_jump2' = l_jump1" using False a4 b0 by simp
      hence a5:"list_in_list l_jump1 0 l_jump2'" using  list_in_list_prop by blast
      have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis
    
      have a7:"list_in_list l_jump2' 0 l_jump2" using a6 a5 by (simp add: Cons.IH)  
      have "list_in_list l_jump1 (0::nat) l_jump2" using a7 a4 list_in_list_concat by metis
      then show ?thesis by simp
    qed
  qed
qed
 


lemma nat_of_nat_trans:"x < u64_MAX \<Longrightarrow> of_nat(unat x) = (x::u64)"
  using u64_MAX_def of_nat_def by simp

lemma "x\<ge>0 \<and> y\<ge>0  \<Longrightarrow> ((of_nat x) ::int) = ((of_nat y) ::int)  \<Longrightarrow> x = y" by presburger


lemma flattern_l_bin0:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   unat pc < length l_bin0 \<and> unat pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow>
   fst (l_pc2 ! (unat pc)) = xpc \<Longrightarrow>
    well_formed_prog l_bin0 \<Longrightarrow>
   list_in_list l xpc l2"
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
  )" using assm2 init_second_layer_def of_nat_def c0 using jitflat_bpf.simps(2)
    by simp   

  have c2:"list_in_list l_pc2' 0 l_pc2" using not_change_prefix_l_pc c0 c1 by blast

  have c3:"(l_pc2 ! (unat pc)) = (of_nat(length l2'),num)" using c2 l_pc_length_prop
    by (smt (z3) Cons_nth_drop_Suc Suc_eq_plus1 ab_semigroup_add_class.add_ac(1) add.commute assm1 assm2 c0 c1 diff_add_inverse diff_diff_cancel 
        init_second_layer_def length_drop less_or_eq_imp_le list.size(3) list.size(4) list_in_list.simps(2) list_in_list_concat not_change_prefix_l_pc) 
    
  have c4:"fst (l_pc2 ! (unat pc)) = (of_nat(length l2'))" using c3 by auto
  
  have c6:"list_in_list l (length l2') l2" using c0 c1 not_change_prefix_l_bin
    by (metis (mono_tags, lifting) list_in_list_concat plus_nat.add_0)     
  have "list_in_list l (fst (l_pc2 ! (unat pc))) l2" using c6 c4 by auto
     then show ?thesis using assm3 by force 
   qed

(*
lemma flattern_num_geric:
  "l_bin0!pc=(num,off,l) \<Longrightarrow>
   pc < length l_bin0  \<Longrightarrow>
   jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
   snd (l_pc2!pc) = num"
  apply(induct l_bin0 arbitrary: pc num off l l1 l_pc1 l_jump1 l2 l_pc2 l_jump2 ; simp)
  subgoal for a al pc num off l l1 l_pc1 l_jump1 l2 l_pc2 l_jump2
    apply (cases pc; simp)
    subgoal *)

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
        using append_Nil assm1 assm3 init_second_layer_def jitflat_bpf.simps(2) 
            list_in_list.simps(2) nth_Cons_0 prod.collapse prod.inject
        by (smt (z3) case_prod_conv)
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
          update_l_jump a [] []))"
        apply simp
        by (cases a; simp add: init_second_layer_def)
  
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
      have "map snd l_pc2 = (fst a)#(map snd l_pc2')" using c0 c1 b2_2 by auto
        (*using assm3 b3 init_second_layer_def not_change_prefix_l_pc b2_2 b2_3 b2_4 num_corr *)
      hence "(map snd l_pc2)!(unat pc) = (map snd l_pc2')!?pc" using b3 False by auto
      hence "snd (l_pc2! unat pc) = num" 
        using b3 False by (metis assm2 b1 c0 c1 map_equality_iff nth_map)
      then show ?thesis by auto  
    qed
  qed
qed


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
  apply (meson outcome.exhaust)
  by (metis err_is_still_err3 outcome.exhaust prod.collapse) 


end