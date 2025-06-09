theory JITFix_prob1
  imports JITFlattern JITFix_def
begin

lemma jit_fix_not_change:
  "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow> 
  x64_decode xpc l_bin0 = Some v \<Longrightarrow>
  (\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num cond d. x64_decode xpc l_bin0 = Some(num, Pjcc cond d))) \<Longrightarrow>
  x64_decode xpc prog = Some v"
  sorry
(*
  apply (induction l_jump arbitrary: l_bin0 l_pc prog xpc v; simp add: get_updated_l_bin_def Let_def split: if_split_asm)
  subgoal for a al l_bin0 l_pc prog xpc v
    apply (cases "l_pc ! unat (snd a)"; simp)
    subgoal for addr num2
      apply (cases "x64_decode (fst (l_pc ! nat (fst a))) l_bin0"; simp)
      subgoal for aa
        apply (cases aa; simp)
        subgoal for sza insa
          apply (cases insa; simp add: Let_def)
          subgoal for x1 x2
            apply (cases "x64_decode (fst (l_pc ! nat (fst a)) + sza) l_bin0"; simp)
            subgoal for bb
              apply (cases bb; simp)
              subgoal for szb insb
                apply (cases insb; simp add: Let_def)
                subgoal for x3 x4 *)


lemma x64_bin_update_is_disjoint:
  "jitfix [x] l_bin0 l_pc = Some prog' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>
  x \<in> set l_jump \<Longrightarrow>
  Some prog' = Some (x64_bin_update (length u8_list) l_bin0 xpc u8_list) \<Longrightarrow>
  x64_decode xpc prog' = Some v \<Longrightarrow>
  x64_decode xpc prog = Some v"
  sorry

lemma x64_bin_update_is_disjoint2:
  "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>
  x \<in> set l_jump \<Longrightarrow>
  jitfix [x] l_bin0 l_pc = prog' \<Longrightarrow>
  prog' \<noteq> None"
  sorry


lemma x64_decode_Pcall_i_x64_encode_length_eq: "
  x64_decode xpc l = Some (sz, Pcall_i i) \<Longrightarrow>
  u8_list = x64_encode (Pcall_i i1) \<Longrightarrow> 
  length u8_list = sz"
  apply (simp add: x64_decode_def x64_encode_def Let_def split: if_split_asm)
  subgoal
    apply (cases "u32_of_u8_list [l ! Suc (Suc xpc), l ! (xpc + (3::nat)),
  l ! (xpc + (4::nat)), l ! (xpc + (5::nat))]"; simp)
    by (cases "cond_of_u8 (and (15::8 word) (l ! Suc xpc))"; simp)
  subgoal by (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat))
  (and (7::8 word) (l ! xpc)) (0::8 word))"; simp)
  subgoal
    by (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat))
  (and (7::8 word) (l ! xpc)) (0::8 word))"; simp)
  subgoal
    apply (cases "u32_of_u8_list [l ! Suc xpc, l ! Suc (Suc xpc),
  l ! (xpc + (3::nat)), l ! (xpc + (4::nat))]"; simp)
    by (simp add: length_u8_list_of_u32_eq_4)
  subgoal
    by (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat))
  (and (7::8 word) (l ! Suc xpc)) (and (1::8 word) (l ! xpc)))"; simp add: split: if_split_asm)
  subgoal
    by (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat))
  (and (7::8 word) (l ! Suc xpc)) (and (1::8 word) (l ! xpc)))"; simp add: split: if_split_asm)
  subgoal
    apply (cases "ireg_of_u8
           (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! Suc (Suc xpc) >> (3::nat)))
             (and (1::8 word) (l ! xpc >> (2::nat))))"; simp)
    by (cases "ireg_of_u8
              (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word)
  (l ! Suc (Suc xpc))) (and (1::8 word) (l ! xpc)))"; simp add: split: if_split_asm)
  subgoal
    by (cases "ireg_of_u8
           (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word)
  (l ! Suc (Suc xpc))) (and (1::8 word) (l ! xpc)))"; simp add: split: if_split_asm)
  subgoal
    apply (cases "ireg_of_u8
           (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! Suc (Suc xpc) >> (3::nat)))
             (and (1::8 word) (l ! xpc >> (2::nat))))"; simp)
    by (cases "ireg_of_u8
              (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word)
  (l ! Suc (Suc xpc))) (and (1::8 word) (l ! xpc)))"; simp add: split: if_split_asm)
  subgoal
    apply (cases "ireg_of_u8
           (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! Suc (Suc xpc) >> (3::nat)))
             (and (1::8 word) (l ! xpc >> (2::nat))))"; simp)
    by (cases "ireg_of_u8
              (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word)
  (l ! Suc (Suc xpc))) (and (1::8 word) (l ! xpc)))"; simp add: split: if_split_asm)
  done

lemma x64_bin_update_nth_eq: "xpc < length l \<Longrightarrow> xpc < n \<Longrightarrow>
  x64_bin_update (length l1) (l[xpc := a]) n l1 ! xpc = a"
  apply (induction l1 arbitrary: xpc n l; simp)
  subgoal for a al xpc n l
    using nth_list_update_eq
    by (simp add: list_update_swap)
  done

lemma x64_bin_update_nth_eq0 : "xpc < length l \<Longrightarrow>
0 < length l1 \<Longrightarrow>
  x64_bin_update (length l1) l xpc l1 ! xpc = l1!0"
  apply (induction l1 arbitrary: xpc l; simp)
  subgoal for a al xpc l
    using nth_list_update_eq
    by (simp add: x64_bin_update_nth_eq)
  done

lemma list_in_list_x64_bin_update_eq: "xpc + length l1 < length l \<Longrightarrow>
  list_in_list l1 xpc (x64_bin_update (length l1) l xpc l1)"
  apply (induction l1 arbitrary: xpc l ; simp)
  subgoal for xpc l
    by (metis Suc_lessD add_lessD1 lessI x64_bin_update_nth_eq)
  done

lemma list_in_list_x64_bin_update_list_eq: "
  xpc + (length l0) + (length l1) < length l \<Longrightarrow>
  list_in_list l1 (length l0 + xpc)
     (x64_bin_update (length l0 + length l1) l xpc (l0 @ l1))"
  apply (induction l0 arbitrary: l1 xpc l ; simp)
  subgoal for l1 xpc l
    using list_in_list_x64_bin_update_eq by blast
  subgoal for a al l1 xpc l
    using x64_bin_update_nth_eq
    by (metis add_Suc length_list_update nat_arith.suc1) 
  done

lemma x64_decode_list_in_list_x64_bin_update_Pcall_i_eq:  "
sz = length (x64_encode (Pcall_i i1)) \<Longrightarrow>
xpc + sz < length l \<Longrightarrow>
list_in_list (x64_encode (Pcall_i i1)) xpc (x64_bin_update sz l xpc (x64_encode (Pcall_i i1)))"
  apply (simp add: x64_decode_def x64_encode_def Let_def split: if_split_asm)
  apply (rule conjI)
  subgoal
    apply (subgoal_tac "5 = length (((232::8 word) # u8_list_of_u32 i1))")
     prefer 2
    subgoal
      by (simp add: length_u8_list_of_u32_eq_4)
    apply (subgoal_tac "(((232::8 word) # u8_list_of_u32 i1))!0 = 232")
     prefer 2
    subgoal by simp
    apply (subgoal_tac "x64_bin_update (length (((232::8 word) # u8_list_of_u32 i1))) l xpc
(((232::8 word) # u8_list_of_u32 i1)) ! xpc = (((232::8 word) # u8_list_of_u32 i1))!0")
    subgoal
      by (meson Suc_lessD lessI less_add_Suc1 less_trans_Suc x64_bin_update_nth_eq)
    apply (rule x64_bin_update_nth_eq0 [of xpc l "(((232::8 word) # u8_list_of_u32 i1))" ]; simp)
    done
    subgoal
      apply (subgoal_tac "list_in_list (u8_list_of_u32 i1) (length [232] + xpc)
     (x64_bin_update (length [232]+ length (u8_list_of_u32 i1)) l xpc ([232] @ (u8_list_of_u32 i1)))")
      subgoal
        by simp

      apply (rule list_in_list_x64_bin_update_list_eq)
      by (simp add: length_u8_list_of_u32_eq_4)
    done

lemma x64_encode_x64_decode_same:"
  xpc + sz < length l \<Longrightarrow>
  sz = length (x64_encode (Pcall_i i1)) \<Longrightarrow>
  u8_list = x64_encode (Pcall_i i1) \<Longrightarrow>
  l1 = x64_bin_update (length u8_list) l xpc u8_list \<Longrightarrow>
    x64_decode xpc l1 = Some (sz, Pcall_i i1)"
  apply (subgoal_tac "length u8_list = sz")
  prefer 2
  subgoal
    by blast
  subgoal 
    apply (rule x64_encode_decode_consistency; simp)
    apply (rule x64_decode_list_in_list_x64_bin_update_Pcall_i_eq; simp?)
    done                              
  done

lemma x64_decode_list_in_list_x64_bin_update_Pjcc_eq:  "
sz = length (x64_encode (Pjcc cond d)) \<Longrightarrow>
xpc + sz < length l \<Longrightarrow>
list_in_list (x64_encode (Pjcc cond d)) xpc (x64_bin_update sz l xpc (x64_encode (Pjcc cond d)))"
  apply (simp add: x64_decode_def x64_encode_def Let_def split: if_split_asm)
  apply (rule conjI)
  subgoal
    using x64_bin_update_nth_eq0
    by (metis (no_types, lifting) add_2_eq_Suc' add_Suc_right add_lessD1 length_list_update
        less_add_Suc1 list_update_swap n_not_Suc_n numeral_2_eq_2 x64_bin_update_nth_eq)
  subgoal
    apply (rule conjI)
    subgoal 
      using x64_bin_update_nth_eq0
      by (simp add: x64_bin_update_nth_eq)
    subgoal
      apply (subgoal_tac "list_in_list (u8_list_of_u32 (ucast d)) (length [15, bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond cond)] + xpc)
     (x64_bin_update (length (u8_list_of_u32 (ucast d))) (l[xpc := 15::8 word, Suc xpc := bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond cond)])
  (length [15, bitfield_insert_u8 (0::nat) (4::nat) (128::8 word) (u8_of_cond cond)] +  xpc) (u8_list_of_u32 (ucast d)))")
       prefer 2
      subgoal
        by (simp add: list_in_list_x64_bin_update_eq)
      subgoal by simp
      done
    done
  done

lemma x64_encode_x64_decode_same2:
  "xpc + sz < length l \<Longrightarrow>
  sz = length (x64_encode (Pjcc cond d)) \<Longrightarrow>
  u8_list = x64_encode (Pjcc cond d) \<Longrightarrow>
  l1 = x64_bin_update (length u8_list) l xpc u8_list \<Longrightarrow>
    x64_decode xpc l1 = Some (sz, Pjcc cond d)"
  apply (subgoal_tac "length u8_list = sz")
  prefer 2
  subgoal
    by blast
  subgoal 
    apply (rule x64_encode_decode_consistency; simp)
    apply (rule x64_decode_list_in_list_x64_bin_update_Pjcc_eq; simp?)
    done
  done


lemma x64_encode_x64_decode_other:
  "xpc + sz < length l \<Longrightarrow>
  xpc1 + sz1 < length l \<Longrightarrow>
  (xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow>
  x64_decode xpc1 l = Some (sz1, ins1) \<Longrightarrow>
  sz = length (x64_encode (Pjcc cond d)) \<Longrightarrow>
  u8_list = x64_encode (Pjcc cond d) \<Longrightarrow>
  l1 = x64_bin_update (length u8_list) l xpc u8_list \<Longrightarrow>
    x64_decode xpc1 l1 = Some (sz1, ins)"
  sorry

end