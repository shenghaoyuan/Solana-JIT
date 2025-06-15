theory Proof1
imports
  Main
  rBPFCommType rBPFSyntax x64Assembler x64Disassembler x64DecodeProofAux

begin

value "x64_decode 0 (x64_encode (Paddq_rr RAX RBX))"

lemma list_in_list_prop_aux1:"x@[] = x"
  by blast

lemma list_in_list_prop_aux2: "list_in_list l2 (length l1) (l1@l2@l3)"
  apply (induction l2 arbitrary: l1 l3)
  subgoal for l1 l3
    by simp
  subgoal for a l2 l1 l3
    apply simp
    by (metis append.left_neutral append_Cons append_assoc length_append_singleton)
  done

lemma list_in_list_prop: "list_in_list l 0 l"
  using list_in_list_prop_aux1
  by (metis append_Nil list_in_list_prop_aux2 list.size(3))

(*
lemma list_in_list_0_app: "list_in_list l0 0 l \<Longrightarrow> \<exists> l1. l = l0 @ l1"
  apply (induction l0 arbitrary: l) *)

(*
lemma list_in_list_prop2:"list_in_list l1 0 l2 \<Longrightarrow> list_in_list l2 0 l3 \<Longrightarrow> list_in_list l1 0 l3"
  using list_in_list_prop_aux1
  sorry*)

lemma x64_bin_update_nth_other: "(xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow> xpc1 < length l \<Longrightarrow>
  sz = (length l1) \<Longrightarrow> 0 < sz1 \<Longrightarrow> 0 < sz \<Longrightarrow> xpc + sz < length l \<Longrightarrow>
  (x64_bin_update (length l1) l xpc l1)!xpc1 = l!xpc1"
  apply (induction l1 arbitrary: xpc sz xpc1 sz1 l ; simp)
  subgoal for a al xpc sz xpc1 sz1 l
    by (smt (verit, ccfv_threshold) add.commute add_Suc_right leD length_list_update less_add_same_cancel2 list.size(3) not_less_eq_eq nth_list_update_neq x64_bin_update.simps(1) zero_less_Suc)
  done

lemma x64_bin_update_length_eq: "x64_bin_update (length l1) l xpc l1 = l2 \<Longrightarrow> length l = length l2"
  apply (induction l1 arbitrary: xpc l l2; simp)
  subgoal for a al xpc l l2
    by auto 
  done


axiomatization where x64_encode_decode_consistency: 
  "list_in_list l_bin pc l \<Longrightarrow>
  l_bin = x64_encode ins \<Longrightarrow>
  length l_bin = n \<Longrightarrow>
  x64_decode pc l = Some (n, ins)" and
x64_encode_x64_decode_other:
  "(xpc1 + sz1 \<le> xpc \<or> xpc+sz \<le> xpc1) \<Longrightarrow>
  x64_decode xpc1 l = Some (sz1, ins1) \<Longrightarrow>
  length u8_list = sz \<Longrightarrow>
  x64_bin_update sz l xpc u8_list = l1 \<Longrightarrow>
    x64_decode xpc1 l1 = Some (sz1, ins1)"

lemma x64_decode_encode_length_eq_jcc: "x64_decode xpc l_bin0 = Some (szb, Pjcc x3 x4) \<Longrightarrow>
  length (x64_encode (Pjcc x3 t)) = szb"
  apply (simp add: x64_decode_def x64_encode_def Let_def split: if_split_asm)
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply (erule conjE)
    using length_u8_list_of_u32_eq_4 by simp
  subgoal
    apply ((erule case_option_eq_NE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  done

lemma x64_decode_encode_length_eq_call: "x64_decode xpc l_bin0 = Some (sz, Pcall_i x1) \<Longrightarrow>
    length (x64_encode (Pcall_i t)) = sz"
  apply (simp add: x64_decode_def x64_encode_def Let_def split: if_split_asm)
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule conjE)+; simp?)
    using length_u8_list_of_u32_eq_4 by simp
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  subgoal
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    apply ((erule case_option_eq_NE | erule ifE | erule conjE)+; simp?)
    done
  done

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

end