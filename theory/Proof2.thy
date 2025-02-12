theory Proof2
  imports Proof1 x64Semantics rBPFSem
begin

lemma x64_decode_extend:
  assumes 
    a1:"x64_decode 0 x = Some res1"
  shows "x64_decode 0 (x@xs) = Some res1"
  apply(unfold x64_decode_def)
  apply(split if_splits,simp_all)
  apply (unfold Let_def)
 apply(split if_splits)
  apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ xs) ! 0)) 0)",simp_all)
   apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ xs) ! Suc (Suc 0) >> 3)) (and 1 ((x @ xs) ! 0 >> 2)))",simp_all)
    apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) 4 (and 1 ((x @ xs) ! 0 >> 2)))",simp_all)
     apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ xs) ! Suc (Suc 0))) (and 1 ((x @ xs) ! 0)))",simp_all)
      apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ xs) ! Suc 0)) (and 1 ((x @ xs) ! 0)))",simp_all)
  
       apply rule+
  using assms x64_decode_def apply auto[1]
  using assms x64_decode_def apply auto[1]
          apply(unfold Let_def)
          apply(split if_splits,simp_all)
          apply (simp add: nth_append)
         apply (metis One_nat_def length_greater_0_conv nth_append option.inject option.simps(3))
  prefer 2 
(*proof-
  have "\<exists> l_bin. x64_encode (snd res1) = Some l_bin" sorry
  then obtain l_bin where b0:"x64_encode (snd res1) = Some l_bin" by auto
  have b1:"x64_decode 0 l_bin = Some (length l_bin, (snd res1))" using b0 x64_encode_decode_consistency by auto
  have "x64_decode 0 x = Some (length l_bin, (snd res1))" using a1 a0 b0 b1 try

lemma x64_decode_extend:"x\<noteq> [] \<Longrightarrow> x64_decode 0 x = Some res1 \<Longrightarrow> x64_decode 0 (x@xs) = Some res1"
  sorry
*)


lemma x64_encodes_decodes_consistency:"
    Some l_bin = x64_encodes2 ins \<Longrightarrow>
    x64_decodes_aux (length ins) 0 l_bin = Some ins_list \<Longrightarrow>
    map snd ins_list = ins"
proof(induct ins arbitrary: l_bin ins_list)
  case Nil
  then show ?case by auto
next
  case (Cons a prog)
  assume assm1:"Some l_bin = x64_encodes2 (a # prog)" and
         assm2:"x64_decodes_aux (length (a # prog)) 0 l_bin = Some ins_list"
  have "\<exists> l_bin2. Some l_bin2 = x64_encodes2 prog" using Cons x64_encodes2_induct x64_encodes2_def assm1 
    by (metis (no_types, lifting) option.case_eq_if x64_encodes1.simps(2))
  then obtain l_bin2 where c0:"Some l_bin2 = x64_encodes2 prog" by auto
  have "\<exists> l_bin1. Some l_bin1 = x64_encode a" using assm1
    by (metis (no_types, lifting) option.case_eq_if option.collapse x64_encodes1.simps(2) x64_encodes2_def)
  then obtain l_bin1 where c1:"Some l_bin1 = x64_encode a" by auto
  have c2:"l_bin1@l_bin2 = l_bin" using x64_encodes2_induct c0 c1 assm1 by metis

  have d0_1: "\<exists> ins_list1. x64_decode 0 l_bin1 = Some ins_list1" using x64_encode_decode_consistency c1 by blast
  then obtain ins_list1 where d0:"x64_decode 0 l_bin1 = Some ins_list1" by auto
  have d1:"snd ins_list1 = a" using d0 x64_encode_decode_consistency c1 by auto
  have d1_1:"l_bin1 \<noteq> []" using c1 apply(cases " x64_encode a",simp_all) 
    subgoal for aa apply(cases a,simp_all)
      subgoal for x11 x12 by auto
          apply auto[1]
      subgoal for x3 apply(unfold Let_def) apply (split if_splits) apply auto[1] 
        apply auto[1]
        done
      subgoal for x4 apply(unfold Let_def) apply (split if_splits) apply auto[1] apply auto[1] done
      subgoal for x51 x52 apply auto[1]
        done
      subgoal for x6 by blast
      done
    done
  have d1_2:"x64_decode 0 l_bin = Some ins_list1" using x64_decode_extend d0 d1 c2 d1_1 by blast
  let "?insx_len" =  "fst ins_list1"
  have d2_1:"(length prog) + 1 = length (a # prog)" by simp
  have "\<exists> ins_list2. x64_decodes_aux (length prog) 0 (drop ?insx_len l_bin) = Some ins_list2 \<and> ins_list = ins_list1#ins_list2" 
    using x64_decodes_aux_induct2 assm2 d1_2 d2_1
    by (metis One_nat_def add.right_neutral add_Suc_right)
  then obtain ins_list2 where d2:" x64_decodes_aux (length prog) 0 (drop ?insx_len l_bin) = Some ins_list2 \<and> ins_list = ins_list1#ins_list2" by auto
  have d2_0:"l_bin2 = drop ?insx_len l_bin" using c1 c2 d0 x64_encode_decode_consistency d2 assm1 assm2 by auto
  have e0:"map snd ins_list2 = prog" using Cons c0 d2 d2_0 by blast
  have e2:"map snd ins_list = a # prog" using d2 c2 d1 e0 by fastforce
  then show ?case by simp
qed



  (*
lemma "
    Some l_bin = x64_encodes2 ins \<Longrightarrow>
    x64_decodes_aux (length ins) 0 l_bin = Some ins_list \<Longrightarrow>
    map snd ins_list = ins"
proof(induct ins arbitrary: l_bin ins_list)
  case Nil
  then show ?case by auto
next
  case (Cons a prog)
  assume assm1:"Some l_bin = x64_encodes2 (a # prog)" and
         assm2:"x64_decodes_aux (length (a # prog)) 0 l_bin = Some ins_list"
  have "\<exists> l_bin2. Some l_bin2 = x64_encodes2 prog" using Cons x64_encodes2_induct x64_encodes2_def assm1 
    by (metis (no_types, lifting) option.case_eq_if x64_encodes1.simps(2))
  then obtain l_bin2 where c0:"Some l_bin2 = x64_encodes2 prog" by auto
  have "\<exists> l_bin1. Some l_bin1 = x64_encode a" using assm1
    by (metis (no_types, lifting) option.case_eq_if option.collapse x64_encodes1.simps(2) x64_encodes2_def)
  then obtain l_bin1 where c1:"Some l_bin1 = x64_encode a" by auto
  have c2:"l_bin1@l_bin2 = l_bin" using x64_encodes2_induct c0 c1 assm1 by metis

  have d_1: "\<exists> ins_list1. x64_decode 0 l_bin1 = Some ins_list1" using x64_encode_decode_consistency c1 by blast
  hence "\<exists> ins_list1. x64_decode 0 l_bin = Some ins_list1" 
    by (smt (verit, del_insts) assm2 length_Cons not_None_eq option.case_eq_if x64_decodes_aux.simps(2))
  then obtain ins_list1 where d0:"x64_decode 0 l_bin = Some ins_list1" by auto
  have d1:"snd ins_list1 = a" using d0 x64_encode_decode_consistency c1
    by (smt (z3) One_nat_def Suc_le_mono c2 le_add1 list.size(3) option.discI option.inject plus_1_eq_Suc split_pairs x64_decode_def x64_decode_extend)
  let "?insx_len" =  "fst ins_list1"
  have d2_1:"(length prog) + 1 = length (a # prog)" by simp
  have "\<exists> ins_list2. x64_decodes_aux (length prog) 0 (drop ?insx_len l_bin) = Some ins_list2 \<and> ins_list = ins_list1#ins_list2" 
    using x64_decodes_aux_induct2 assm2 d0 d2_1
    by (metis One_nat_def add.right_neutral add_Suc_right)
  then obtain ins_list2 where d2:" x64_decodes_aux (length prog) 0 (drop ?insx_len l_bin) = Some ins_list2 \<and> ins_list = ins_list1#ins_list2" by auto
  have d2_0:"l_bin2 = drop ?insx_len l_bin" using c1 c2 d0 x64_encode_decode_consistency d2 assm1 assm2 try
  (*have "\<exists> ins_list2. x64_decodes_aux (length prog) 0 l_bin2 = Some ins_list2" using assm2 assm1 d2_0 sorry
  then obtain ins_list2 where d2:"x64_decodes_aux (length prog) 0 l_bin2 = Some ins_list2" by auto
 have "l_bin1 \<noteq> []" using c1 apply(cases " x64_encode a",simp_all) 
    subgoal for aa apply(cases a,simp_all)
      subgoal for x11 x12 by auto
          apply auto[1]
      subgoal for x3 apply(unfold Let_def) apply (split if_splits) apply auto[1] 
        apply auto[1]
        done
      sorry
    sorry
  hence d2_1:"x64_decode 0 l_bin = Some ins_list1" using d0 c2 x64_decode_extend by blast
  have d2_2:"l_bin1 = (take ?insx_len l_bin) " by (metis append_same_eq c2 d2_0 hhh)
*)
  have e0:"map snd ins_list2 = prog" using Cons c0 d2 d2_0 by blast
  have e2:"map snd ins_list = a # prog" using d2 c2 d1 e0 by fastforce
  then show ?case by simp
qed

have "\<exists> insa. x64_encode ins = Some insa"
    using assm1 option.collapse x64_encodes2_def by fastforce
  then obtain insa where b2:"x64_encode a = Some insa" by auto
  hence "\<exists> insx. x64_decode 0 insa = Some insx" by (metis x64_encode_decode_consistency)
  then obtain insx where b3:"x64_decode 0 insa = Some insx" by auto
  have b4:"snd insx = a" using x64_encode_decode_consistency b2 b3 by (metis option.sel snd_conv)
  let "?insx_len" =  "fst insx"
  have "\<exists> hhh. x64_decodes_aux (length a) 0 insa = Some hhh" using assm2 b2 try
  have "x64_decodes_aux 1 0 insa = Some [insx]" using x64_decodes_aux_equiv b3 try
  have "\<exists> ins_list'. x64_decodes_aux (length ins) ?insx_len l_bin' = Some ins_list'" 
    using b1 assm2 x64_decodes_aux_induct b2 b3 b4
   
  then obtain ins_list' where  b2:"x64_decodes 0 l_bin' = Some ins_list'" by auto
  have b3:"map snd ins_list' = ins" using b0 b1 b2 Cons by blast
  have "\<exists> h. x64_encode a = Some h"
    by (metis (mono_tags, lifting) assm1 option.case_eq_if option.collapse x64_encodes_aux.simps(2) x64_encodes_def x64_encodes_suffix_def)
  then obtain h where "x64_encode a = Some h" by auto
  moreover have "\<exists> x. x64_decode 0 h = Some x" 
    by (metis calculation x64_encode_decode_consistency)
    then obtain x where "x64_decode 0 h = Some x" by auto
    hence c0:"snd x = a" by (metis calculation option.inject snd_conv x64_encode_decode_consistency)
  then show ?case using c0 b3 Cons 
  qed*)




end




