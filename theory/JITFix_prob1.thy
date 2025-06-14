theory JITFix_prob1
  imports JITFlattern JITFix_def Proof1
begin

definition nth_error :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
"nth_error l a = (if length l \<le> a then None else Some (l!a))"

definition wf_l_pc :: "(nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
"wf_l_pc l_pc l_xpc len \<equiv> (
  (\<forall> x. x \<in> set (map fst l_pc) \<longrightarrow> x < len) \<and>
  (\<forall> x. x \<in> set (map fst l_pc) \<longrightarrow> x \<in> set (map fst l_xpc)) \<and>
  (\<forall> i j xi yi xj yj.
    nth_error l_pc i = Some (xi, yi) \<longrightarrow>
    nth_error l_pc j = Some (xj, yj) \<longrightarrow>
      xi < yi)
)"

fun wf_l_xpc :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
"wf_l_xpc [] _ = True" |
"wf_l_xpc [xpc] len = (0 < snd xpc \<and> fst xpc + snd xpc = len)" |
"wf_l_xpc (xpc # xpc1 # l_xpc) len = (
  0 < snd xpc \<and>
  (fst xpc + snd xpc) = fst xpc1 \<and>
  wf_l_xpc (xpc1 # l_xpc) len
)"

definition wf_l_jump :: "nat list \<Rightarrow> (int\<times>u64) list \<Rightarrow> bool" where
"wf_l_jump l_pc l_jump \<equiv> (\<forall> x y. 
  (x, y) \<in> set l_jump \<longrightarrow>
    (nat x) \<in> set l_pc \<and> (unat y) \<in> set l_pc)"

definition flattern_inv :: "x64_bin \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (int\<times>u64) list \<Rightarrow> bool" where
"flattern_inv l_bin l_xpc l_pc l_jump \<equiv> (
   \<comment>\<open> l_bin \<close>
  l_bin \<noteq> [] \<and>
   \<comment>\<open> l_pc \<close>
  (l_pc \<noteq> [] \<and> wf_l_pc l_pc l_xpc (length l_bin)) \<and>
   \<comment>\<open> l_xpc \<close>
  (l_xpc \<noteq> [] \<and> wf_l_xpc l_xpc (length l_bin)) \<and>
   \<comment>\<open> l_jump \<close>
  (wf_l_jump (map fst l_pc) l_jump)
)"


definition l_pc_neq :: "(nat \<times> nat) list \<Rightarrow> bool" where
"l_pc_neq l_pc \<equiv> (\<forall> i j.
  i \<noteq> j \<and> i \<le> length l_pc \<and> j \<le> length l_pc \<longrightarrow>
    fst (l_pc!i) \<noteq> fst (l_pc!j))"

definition l_xpc_neq :: "(nat \<times> nat) list \<Rightarrow> bool" where
"l_xpc_neq l_xpc \<equiv> (\<forall> i j.
  i \<noteq> j \<and> i \<le> length l_xpc \<and> j \<le> length l_xpc \<longrightarrow>
    fst (l_xpc!i) + snd (l_xpc!i) \<noteq> fst (l_xpc!j) + snd (l_xpc!j))"

lemma x64_decode_xpc_neq: "
  x64_decode xpc l_bin0 = Some (sz, ins1) \<Longrightarrow>
  \<forall>(cond::testcond) d::32 signed word. ins1 \<noteq> Pjcc cond d \<Longrightarrow>
  x64_decode xpc1 l_bin0 = Some (sz1, Pjcc x3 x4) \<Longrightarrow>
    xpc \<noteq> xpc1"
  by auto


lemma wf_l_xpc_cons_leq: "
  wf_l_xpc ((xpc, sz) # al) len \<Longrightarrow> xpc \<noteq> xpc1 \<Longrightarrow> list_in (xpc1, sz1) al \<Longrightarrow>
    xpc + sz \<le> xpc1"
  apply (induction al arbitrary: len xpc xpc1 sz sz1; simp?)
  subgoal for a al len xpc xpc1 sz sz1
    apply (erule conjE)+
    apply (cases a)
    subgoal for xpc0 sz0
      apply (erule disjE; simp)
      by (metis add_leD1 dual_order.eq_iff)
    done
  done    

lemma x64_decode_xpc_neq_other: "
  wf_l_xpc l_xpc len \<Longrightarrow>
  xpc \<noteq> xpc1 \<Longrightarrow>
  list_in (xpc, sz) l_xpc \<Longrightarrow>
  list_in (xpc1, sz1) l_xpc \<Longrightarrow>
    xpc + sz \<le> xpc1 \<or> xpc1 + sz1 \<le> xpc"
  apply (induction l_xpc arbitrary: len xpc xpc1 sz sz1; simp?)
  subgoal for a al len xpc xpc1 sz sz1
    apply (cases "(xpc, sz) = a"; simp)
    subgoal
      apply (cases "(xpc1, sz1) = a"; simp)
      subgoal
        by auto
      subgoal 
        apply (subgoal_tac "xpc + sz \<le> xpc1"; simp?)
        apply (cases al; simp)
        subgoal for a1 al1
          apply (cases "(xpc1, sz1) = a1"; simp)
          subgoal by auto
          apply (erule conjE)+
          using wf_l_xpc_cons_leq
          by (metis add_leD1 dual_order.refl fst_conv prod.collapse snd_conv)
        done
      done
    apply (cases "(xpc1, sz1) = a"; simp)
    subgoal
      using wf_l_xpc_cons_leq
      by simp
    subgoal
      by (metis list_in.elims(2) wf_l_xpc.simps(3)) 
    done
  done

lemma case_option_eq_E:
  assumes c: "(case x of None \<Rightarrow> P | Some y \<Rightarrow> Q y) = Some z"
  obtains
    (None) "x = None" and "P = Some z"
  | (Some) y where "x = Some y" and "Q y = Some z"
  using c by (cases x) simp_all


lemma case_option_eq_NE:
  assumes c: "(case x of None \<Rightarrow> None | Some y \<Rightarrow> Q y) = Some z"
  obtains
    (None) "x = None" and "False"
  | (Some) y where "x = Some y" and "Q y = Some z"
  using c by (cases x) simp_all

lemma ifE:
  assumes c: "(if Q then x else y) = R"
  obtains
    "Q = True \<and> x = R" 
  | "Q = False \<and> y = R"
  using c by argo

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
        
lemma jit_fix_not_change: "
  wf_l_xpc l_xpc len \<Longrightarrow>
  l_pc_neq l_pc \<Longrightarrow>
  l_xpc_neq l_xpc \<Longrightarrow>
  (xpc, sz1) \<in> set l_xpc \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc l_xpc = Some prog \<Longrightarrow> 
  x64_decode xpc l_bin0 = Some (sz1, ins1) \<Longrightarrow>
  (\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))) \<and>
  (\<not> (\<exists> num cond d. x64_decode xpc l_bin0 = Some(num, Pjcc cond d))) \<Longrightarrow>
  x64_decode xpc prog = Some (sz1, ins1)"
  apply (induction l_jump arbitrary: l_bin0 l_xpc l_pc prog xpc sz1 ins1; simp add: get_updated_l_bin_def Let_def split: if_split_asm)
  subgoal for a al l_bin0 l_xpc l_pc prog xpc sz1 ins1
    apply (cases "l_pc ! unat (snd a)"; simp)
    subgoal for addr num2
      apply (cases "x64_decode (fst (l_pc ! nat (fst a))) l_bin0"; simp)
      subgoal for aa
        apply (cases aa; simp)
        subgoal for sza insa
          apply (cases "list_in (fst (l_pc ! nat (fst a)), sza) l_xpc"; simp)
          apply (cases insa; simp add: Let_def)
          subgoal for x1 x2
            apply (cases "x64_decode (fst (l_pc ! nat (fst a)) + sza) l_bin0"; simp)
            subgoal for bb
              apply (cases bb; simp)
              subgoal for szb insb
                apply (cases "list_in (fst (l_pc ! nat (fst a)) + sza, szb) l_xpc"; simp)
                apply (cases insb; simp add: Let_def)
                subgoal for x3 x4 
                  apply (subgoal_tac "x64_decode xpc (x64_bin_update
       (length
         (x64_encode (Pjcc x3 (word_of_nat addr - (word_of_nat (fst (l_pc ! nat (fst a))) + word_of_nat sza + word_of_nat szb + 1)))))
       l_bin0 (fst (l_pc ! nat (fst a)) + sza)
       (x64_encode (Pjcc x3 (word_of_nat addr - (word_of_nat (fst (l_pc ! nat (fst a))) + word_of_nat sza + word_of_nat szb + 1))))) = Some (sz1, ins1)")
                  subgoal
                    by blast
                  subgoal 
                    apply (rule x64_encode_x64_decode_other; simp?)
                    apply (rule x64_decode_xpc_neq_other; simp?)
                    subgoal
                      by auto
                    subgoal
                      by (meson list_in_set_in_iff)
                    subgoal
                      using list_in_set_in_iff x64_decode_encode_length_eq_jcc
                      by simp
                    done
                  done
                done
              done
            done

          subgoal for x1
            apply (subgoal_tac "x64_decode xpc (x64_bin_update (length (x64_encode (Pcall_i (word_of_nat addr)))) l_bin0 (fst (l_pc ! nat (fst a)))
       (x64_encode (Pcall_i (word_of_nat addr)))) = Some (sz1, ins1)")
            subgoal
              by blast
            subgoal 
              apply (rule x64_encode_x64_decode_other; simp?)
              apply (rule x64_decode_xpc_neq_other; simp?)
              subgoal
                by auto
              subgoal
                by (meson list_in_set_in_iff)
              subgoal
                using list_in_set_in_iff x64_decode_encode_length_eq_call
                by simp
              done
            done
          done
        done
      done
    done
  done

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

end