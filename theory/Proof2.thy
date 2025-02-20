theory Proof2
  imports Proof1 x64Semantics rBPFSem
begin

(*lemma x64_decode_extend:
  assumes 
    a1:"x64_decode 0 x = Some res1"
  shows "x64_decode 0 (x@[a]) = Some res1"
  apply(unfold x64_decode_def)
  apply(split if_splits,simp_all)
  apply (unfold Let_def)
  apply(split if_splits)+ apply simp_all
  apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) 4 (and 1 ((x @ [a]) ! 0 >> 2)))",simp_all)
   apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! 0)) 0)",simp_all)
    prefer 2
  subgoal for aa 
    apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! Suc (Suc 0))) (and 1 ((x @ [a]) ! 0))) ",simp_all)
     apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! Suc 0)) (and 1 ((x @ [a]) ! 0)))",simp_all)
      apply(cases"ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! Suc (Suc 0) >> 3)) (and 1 ((x @ [a]) ! 0 >> 2)))",simp_all)
       apply rule+
           apply simp
          apply auto[1]
         apply rule
         apply(unfold bitfield_insert_u8_def Let_def ireg_of_u8_def,simp) 
    apply(split if_splits)+ 
              apply simp
        (*    apply(split if_splits)+  apply simp
             apply(split if_splits)+  apply simp
             apply(split if_splits)+  apply simp
             apply(split if_splits)+  apply simp*)
             apply simp
            apply auto[1]
           apply simp
    apply simp
         apply rule+ 
          apply(split if_splits)+  
               apply blast
              apply auto[1]
             apply simp
            apply simp
    apply(split if_splits)+ 
               apply blast
              apply blast
             apply blast
            apply blast
           apply(split if_splits)+ 
               apply blast
              apply blast
             apply blast
            apply blast
    
    



   (*apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! Suc (Suc 0))) (and 1 ((x @ [a]) ! 0))) ",simp_all)
    apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! Suc 0)) (and 1 ((x @ [a]) ! 0)))",simp_all)
  apply(cases "ireg_of_u8 (bitfield_insert_u8 3 (Suc 0) (and 7 ((x @ [a]) ! Suc (Suc 0) >> 3)) (and 1 ((x @ [a]) ! 0 >> 2))) ",simp_all)*)
      apply rule+
         prefer 5
  subgoal for aa
    apply rule+ 
  sorry


*)
  


lemma x64_decode_extend:
  assumes 
    a1:"x64_decode 0 x = Some res1"
  shows "x64_decode 0 (x@xs) = Some res1"
  sorry


  (*apply(unfold x64_decode_def)
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
  prefer 2 *)
(*proof-
  have "\<exists> l_bin. x64_encode (snd res1) = Some l_bin" sorry
  then obtain l_bin where b0:"x64_encode (snd res1) = Some l_bin" by auto
  have b1:"x64_decode 0 l_bin = Some (length l_bin, (snd res1))" using b0 x64_encode_decode_consistency by auto
  have "x64_decode 0 x = Some (length l_bin, (snd res1))" using a1 a0 b0 b1 try

lemma x64_decode_extend:"x\<noteq> [] \<Longrightarrow> x64_decode 0 x = Some res1 \<Longrightarrow> x64_decode 0 (x@xs) = Some res1"
  sorry
*)

(*
lemma x64_encodes_decodes_consistency:"
    l_bin = x64_encodes2 ins \<Longrightarrow>
    x64_decodes_aux (length ins) 0 l_bin = Some ins_list \<Longrightarrow>
    map snd ins_list = ins"
proof(induct ins arbitrary: l_bin ins_list)
  case Nil
  then show ?case by auto
next
  case (Cons a prog)
  assume assm1:"l_bin = x64_encodes2 (a # prog)" and
         assm2:"x64_decodes_aux (length (a # prog)) 0 l_bin = Some ins_list"
  have "\<exists> l_bin2. l_bin2 = x64_encodes2 prog" using Cons x64_encodes2_induct x64_encodes2_def assm1 
    by (metis (no_types, lifting) option.case_eq_if x64_encodes1.simps(2))
  then obtain l_bin2 where c0:"l_bin2 = x64_encodes2 prog" by auto
  have "\<exists> l_bin1. l_bin1 = x64_encode a" using assm1
    by (metis (no_types, lifting) option.case_eq_if option.collapse x64_encodes1.simps(2) x64_encodes2_def)
  then obtain l_bin1 where c1:"l_bin1 = x64_encode a" by auto
  have c2:"l_bin1@l_bin2 = l_bin" using x64_encodes2_induct c0 c1 assm1 by metis

  have d0_1: "\<exists> ins_list1. x64_decode 0 l_bin1 = Some ins_list1" using x64_encode_decode_consistency c1 list_in_list_prop by blast
  then obtain ins_list1 where d0:"x64_decode 0 l_bin1 = Some ins_list1" by auto
  have d1:"snd ins_list1 = a" using d0 x64_encode_decode_consistency c1 list_in_list_prop by fastforce
  have d1_1:"l_bin1 \<noteq> []" using c1 apply(cases "x64_encode a",simp_all) 
    apply(cases a,simp_all)
      subgoal for x3 apply(unfold Let_def) apply (split if_splits) apply auto[1] 
        apply auto[1]
        done
      subgoal for x4 apply(unfold Let_def) apply (split if_splits) apply auto[1] apply auto[1] done
    done
  have d1_2:"x64_decode 0 l_bin = Some ins_list1" using x64_decode_extend d0 d1 c2 d1_1 by blast
  let "?insx_len" =  "fst ins_list1"
  have d2_1:"(length prog) + 1 = length (a # prog)" by simp
  have "\<exists> ins_list2. x64_decodes_aux (length prog) 0 (drop ?insx_len l_bin) = Some ins_list2 \<and> ins_list = ins_list1#ins_list2" 
    using x64_decodes_aux_induct2 assm2 d1_2 d2_1
    by (metis One_nat_def add.right_neutral add_Suc_right)
  then obtain ins_list2 where d2:" x64_decodes_aux (length prog) 0 (drop ?insx_len l_bin) = Some ins_list2 \<and> ins_list = ins_list1#ins_list2" by auto
  have d2_0:"l_bin2 = drop ?insx_len l_bin" using c1 c2 d0 x64_encode_decode_consistency d2 assm1 assm2 list_in_list_prop sorry
  have e0:"map snd ins_list2 = prog" using Cons c0 d2 d2_0 by blast
  have e2:"map snd ins_list = a # prog" using d2 c2 d1 e0 by fastforce
  then show ?case by simp
qed
*)


end




