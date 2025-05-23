theory JITFlattern_prob
  imports JITFlattern_def JITFlattern_aux JITPer_aux
begin

(** see Solana-x64-Semantics nth_error branch `x64DecodeProp.thy`
  The current version could not be proven becasue of `!`
 *)
lemma x64_decode_length_none: "
  x64_decode (length l) l = None"
  sorry

(*lemma list_in_list_implies_set_relation:
  "list_in_list [x] pos l_jump \<Longrightarrow> x \<in> set l_jump"
  sorry*)
lemma list_in_list_x64_decode:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode n l_bin = Some v \<Longrightarrow> x64_decode (pc+n) l = Some v"
  sorry


(** see Solana-x64-Semantics nth_error branch `x64EncodeProp.thy`
 *)
lemma x64_encode_length_ge_1: "x64_encode ins = l \<Longrightarrow> 1 \<le> length l"
  sorry


fun x64_bin_is_sequential :: "nat \<Rightarrow> x64_bin \<Rightarrow> nat \<Rightarrow> bool" where
"x64_bin_is_sequential 0 l pc = False" |
"x64_bin_is_sequential (Suc n) l pc = (
  if pc = length l then
    True
  else (
    case x64_decode pc l of
    None \<Rightarrow> False |
    Some (sz, ins) \<Rightarrow> (
      case ins of
      Pjcc _ _ \<Rightarrow> False |
      Pcall_i _ \<Rightarrow> False |
      Pret \<Rightarrow> False |
      _ \<Rightarrow> x64_bin_is_sequential n l (pc + sz)
)))"

lemma x64_bin_is_sequential_x64_decode: "
  x64_bin_is_sequential n l x \<Longrightarrow>
  x64_decode x l = Some (sz, ins) \<Longrightarrow>
    x64_bin_is_sequential n l (x + sz)"
  apply (induction n arbitrary: l x sz ins)
  subgoal for l x sz ins
    by simp
  subgoal for n1 l x sz ins
    apply simp
    apply (cases "x = length l"; simp)
    subgoal using x64_decode_length_none by simp

    apply (subgoal_tac "x64_bin_is_sequential n1 l (x + sz)")
    subgoal
      apply (cases "x64_decode (x + sz) l"; simp)
      subgoal
        apply (cases n1; simp)
        subgoal for n2
          apply (cases "x + sz = length l"; simp)
          done
        done

      subgoal for ins1
        apply (cases ins1; simp)
        subgoal for sz1 ins2
          apply (cases ins2; simp; cases n1; simp)
          subgoal for n2
            apply (cases "x + sz = length l"; simp)
            done
          subgoal for x1 x2 x3
            apply (cases "x + sz = length l"; simp)
            done
          subgoal for x1 x2
            apply (cases "x + sz = length l"; simp)
            done
          done
        done
      done

    apply (cases ins; simp)
    done
  done

lemma x64_sem_stuck: "x64_sem n l Stuck = Stuck"
  by (cases n; simp)

lemma x64_bin_is_sequential_x64_decode_pret_false: "
  x64_bin_is_sequential n l x \<Longrightarrow>
    x64_decode x l = Some (sz2, Pret) \<Longrightarrow> False"
  apply (cases n; simp)
  subgoal for n1
    apply (cases "x64_decode x l"; simp)
    subgoal for ins1
      apply (cases "x = length l"; simp)
      using x64_decode_length_none by auto
    done
  done

lemma x64_bin_is_sequential_x64_decode_pjcc_false: "
  x64_bin_is_sequential n l x \<Longrightarrow>
    x64_decode x l = Some (sz2, Pjcc x1 x2) \<Longrightarrow> False"
  apply (cases n; simp)
  subgoal for n1
    apply (cases "x64_decode x l"; simp)
    subgoal for ins1
      apply (cases "x = length l"; simp)
      using x64_decode_length_none by auto
    done
  done

lemma x64_bin_is_sequential_x64_decode_pcall_false: "
  x64_bin_is_sequential n l x \<Longrightarrow>
    x64_decode x l = Some (sz2, Pcall_i x1) \<Longrightarrow> False"
  apply (cases n; simp)
  subgoal for n1
    apply (cases "x64_decode x l"; simp)
    subgoal for ins1
      apply (cases "x = length l"; simp)
      using x64_decode_length_none by auto
    done
  done

lemma "x64_decode x l = Some (sz2, Pcall_i x1) \<Longrightarrow> \<not> (x64_bin_is_sequential n l x)"
  using x64_bin_is_sequential_x64_decode_pcall_false by blast

 (*l!x \<noteq> 0xe8 \<and> l!x \<noteq> 0xc3 \<and> l!(x+1) \<noteq> (0x39::u8) \<Longrightarrow>*)
lemma list_in_list_prop3: "
  x64_sem num l_bin (Next (xpc+x) xrs xm xss) = fxst \<Longrightarrow>
  x64_sem num l (Next x xrs xm xss) = xxst \<Longrightarrow>
  x64_bin_is_sequential (length l) l x \<Longrightarrow>
  list_in_list l xpc l_bin \<Longrightarrow>
  fxst \<noteq> Stuck \<Longrightarrow>
  xxst \<noteq> Stuck \<Longrightarrow>
    match_state1 xxst fxst"
  apply (induction num arbitrary: l_bin xpc x xrs xm xss fxst l xxst)
  subgoal for l_bin xpc x xrs xm xss fxst l xxst
    apply simp using match_state1_def by auto

  subgoal for n l_bin xpc x xrs xm xss fxst l xxst
    apply simp
    apply (cases fxst; simp)
    subgoal for xpc1 xrs1 xm1 xstk1
      apply (cases xxst; simp)
      subgoal for xpc2 xrs2 xm2 xstk2

        apply (cases "x64_decode x l"; simp)
        subgoal for ins
          apply (cases ins; simp)
          subgoal for sz2 ins1
            apply (subgoal_tac "x64_decode (xpc + x) l_bin = Some (sz2, ins1)")
             prefer 2
            subgoal            
              apply (rule list_in_list_x64_decode [of l xpc l_bin x "(sz2, ins1)"]; simp)
              done
            apply simp
            apply (subgoal_tac "x64_bin_is_sequential (length l) l (x+sz2)")
            prefer 2
            subgoal using x64_bin_is_sequential_x64_decode
              by simp
            
            apply (cases ins1; simp add: exec_instr_def)
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal
              using x64_bin_is_sequential_x64_decode_pret_false
              by blast
            subgoal for x1
              apply (simp add: exec_push_def Let_def)
              apply (cases "storev M64 xm (Vptr sp_block (xrs (IR SP) -
  u64_of_memory_chunk M64)) (Vlong (xrs (IR x1)))"; simp add: x64_sem_stuck)
              subgoal for xm2
              apply (simp only: add.assoc [of xpc x sz2])
                by blast
              done
            subgoal for x1
              apply (simp add: exec_pop_def Let_def)
              apply (cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))"; simp add: x64_sem_stuck)
              subgoal for v
                apply (cases v; simp add: x64_sem_stuck)
                subgoal for i
                  apply (simp only: add.assoc [of xpc x sz2])
                  by blast
                done
              done
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2
              using x64_bin_is_sequential_x64_decode_pjcc_false by blast
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2 x3
              apply (simp add: exec_store_def Let_def)
              apply (cases "storev x3 xm (Vlong (eval_addrmode64 x1 xrs)) (Vlong (xrs (IR x2)))"; simp add: x64_sem_stuck)
              subgoal for xm2
              apply (simp only: add.assoc [of xpc x sz2])
                by blast
              done
            subgoal for x1 x2
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1
              apply (simp only: add.assoc [of xpc x sz2])
              by blast
            subgoal for x1 x2 x3
              apply (simp add: exec_load_def Let_def)
              apply (cases "loadv x3 xm (Vlong (eval_addrmode64 x2 xrs))"; simp add: x64_sem_stuck)
              subgoal for v
                apply (cases v; simp add: x64_sem_stuck add.assoc [of xpc x sz2])
                done
              done
            subgoal for x1
              using x64_bin_is_sequential_x64_decode_pcall_false
              by blast
            done
          done
        done
      done
    done
  done


lemma not_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l \<noteq> Some(1,Pret)"
  apply(simp add: x64_decode_def Let_def)
  apply (cases "and (15::8 word) (l ! pc >> (4::nat)) \<noteq> (4::8 word)"; simp)
  subgoal
    apply (cases "and (31::8 word) (l ! pc >> (3::nat)) = (10::8 word)"; simp)
    subgoal
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! pc)) 0)"; simp)
      subgoal for dst
        by auto
      done

    apply (cases "and (31::8 word) (l ! pc >> (3::nat)) = (11::8 word)"; simp)
    subgoal
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! pc)) 0)"; simp)
      subgoal for dst
        by auto
      done

    apply (cases "l ! pc = (232::8 word)"; simp)
    apply (cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]"; simp)
    subgoal for dst
      by auto
    done
  apply (cases "l ! pc = (15::8 word)"; simp add: Let_def)
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (10::8 word)"; simp)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      by auto
    done
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (11::8 word)"; simp add: Let_def)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      by auto
    done
  apply (cases "l ! Suc pc = 1"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    subgoal for dst
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
      subgoal for src
        apply (cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
        by auto
      done
    done
  apply (cases "l ! Suc pc = (247::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word) \<and> and (7::8 word) (l ! Suc (Suc pc) >> (3::nat)) = (4::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    apply (cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
    by auto

  apply (cases "l ! Suc pc = (57::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    by auto
    
  apply (cases "l ! Suc pc = (137::8 word)"; simp)
  apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
  by auto


lemma not_call_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xe8 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<forall> d. x64_decode pc l \<noteq> Some(5, Pcall_i d)"
  apply(simp add: x64_decode_def Let_def)
  apply (cases "l ! pc = (195::8 word)"; simp)
  apply (cases "and (15::8 word) (l ! pc >> (4::nat)) \<noteq> (4::8 word)"; simp)
  subgoal
    apply (cases "and (31::8 word) (l ! pc >> (3::nat)) = (10::8 word)"; simp)
    subgoal
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! pc)) 0)"; simp)
      done

    apply (cases "and (31::8 word) (l ! pc >> (3::nat)) = (11::8 word)"; simp)
    subgoal
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! pc)) 0)"; simp)
      done
    done

  apply (cases "l ! pc = (232::8 word)"; simp)
  apply (cases "l ! pc = (15::8 word)"; simp add: Let_def)
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (10::8 word)"; simp)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      by auto
    done
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (11::8 word)"; simp add: Let_def)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      by auto
    done
  apply (cases "l ! Suc pc = 1"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    subgoal for dst
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
      subgoal for src
        apply (cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
        by auto
      done
    done
  apply (cases "l ! Suc pc = (247::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word) \<and> and (7::8 word) (l ! Suc (Suc pc) >> (3::nat)) = (4::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    done

    apply (cases "l ! Suc pc = (57::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    by auto
    
  apply (cases "l ! Suc pc = (137::8 word)"; simp)
  apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
  by auto

lemma not_cmp_insn:"l\<noteq>[] \<Longrightarrow> l!(pc+1) \<noteq> 0x39 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<forall> src dst. x64_decode pc l \<noteq> Some(3, Pcmpq_rr src dst)"
  apply(simp add: x64_decode_def Let_def)
  apply (cases "l ! pc = (195::8 word)"; simp)
  apply (cases "and (15::8 word) (l ! pc >> (4::nat)) \<noteq> (4::8 word)"; simp)
  subgoal
    apply (cases "and (31::8 word) (l ! pc >> (3::nat)) = (10::8 word)"; simp)
    subgoal
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! pc)) 0)"; simp)
      by auto

    apply (cases "and (31::8 word) (l ! pc >> (3::nat)) = (11::8 word)"; simp)
    subgoal
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! pc)) 0)"; simp)
      by auto

    apply (cases "l ! pc = (232::8 word)"; simp)
    apply (cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]"; simp)
    subgoal for dst by auto
    done

  apply (cases "l ! pc = (15::8 word)"; simp add: Let_def)
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (10::8 word)"; simp)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      by auto
    done
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (11::8 word)"; simp add: Let_def)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      by auto
    done
  apply (cases "l ! Suc pc = 1"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    subgoal for dst
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
      subgoal for src
        apply (cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
        by auto
      done
    done
  apply (cases "l ! Suc pc = (247::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word) \<and> and (7::8 word) (l ! Suc (Suc pc) >> (3::nat)) = (4::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    subgoal for dst by auto
    done

  apply (cases "l ! Suc pc = (57::8 word)"; simp)
    
  apply (cases "l ! Suc pc = (137::8 word)"; simp)
  apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
  by auto

lemma x64_encode_app_length_minus_1: "x64_encode ins @ l1 = l \<Longrightarrow> n-1 \<le> length l1 \<Longrightarrow> n \<le> length l"
  using x64_encode_length_ge_1
  by (metis One_nat_def Suc_pred add_mono le_zero_eq length_append linorder_not_less order_less_imp_le plus_1_eq_Suc) 


lemma x64_encode_app_length_ge_2[simp]: "x64_encode ins1 @ x64_encode ins2 = l  \<Longrightarrow> 2 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1
  by auto

lemma x64_encode_app_length_ge_3[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 = l \<Longrightarrow> 3 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  by (metis add.commute add_diff_cancel_left' numeral_Bit0 numeral_Bit1)

lemma x64_encode_app_length_ge_4[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 = l \<Longrightarrow> 4 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3
  by (simp add: numeral_Bit1) 

lemma x64_encode_app_length_ge_5[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 = l \<Longrightarrow> 5 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3 x64_encode_app_length_ge_4
  by (metis diff_Suc_1 eval_nat_numeral(3))

lemma x64_encode_app_length_ge_6[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 @ x64_encode ins6 = l \<Longrightarrow> 6 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3 x64_encode_app_length_ge_4 x64_encode_app_length_ge_5
  by (metis diff_Suc_1 eval_nat_numeral(2) semiring_norm(28))

lemma x64_encode_app_length_ge_7[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 @
  x64_encode ins6 @ x64_encode ins7 = l \<Longrightarrow> 7 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3 x64_encode_app_length_ge_4 x64_encode_app_length_ge_5
  x64_encode_app_length_ge_6
  by (metis add_diff_cancel_left' eval_nat_numeral(3) plus_1_eq_Suc )

lemma x64_encode_app_length_ge_8[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 @
  x64_encode ins6 @ x64_encode ins7 @ x64_encode ins8 = l \<Longrightarrow> 8 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3 x64_encode_app_length_ge_4 x64_encode_app_length_ge_5
  x64_encode_app_length_ge_6 x64_encode_app_length_ge_7
  by (metis diff_Suc_1 eval_nat_numeral(2) semiring_norm(26,27))

lemma x64_encode_app_length_ge_9[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 @
  x64_encode ins6 @ x64_encode ins7 @ x64_encode ins8 @ x64_encode ins9 = l \<Longrightarrow> 9 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3 x64_encode_app_length_ge_4 x64_encode_app_length_ge_5
  x64_encode_app_length_ge_6 x64_encode_app_length_ge_7 x64_encode_app_length_ge_8
  by (metis diff_Suc_1 eval_nat_numeral(3))

lemma x64_encode_app_length_ge_10[simp]: "
  x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 @
  x64_encode ins6 @ x64_encode ins7 @ x64_encode ins8 @ x64_encode ins9 @ x64_encode ins10 = l
  \<Longrightarrow> 10 \<le> length l"
  using x64_encode_app_length_minus_1 x64_encode_length_ge_1 x64_encode_app_length_ge_2
  x64_encode_app_length_ge_3 x64_encode_app_length_ge_4 x64_encode_app_length_ge_5
  x64_encode_app_length_ge_6 x64_encode_app_length_ge_7 x64_encode_app_length_ge_8
  x64_encode_app_length_ge_9
  by (metis diff_Suc_1 eval_nat_numeral(2) semiring_norm(28))

lemma per_jit_ins_num_le_length:"per_jit_ins ins = Some (num, off, l) \<Longrightarrow> num \<le> (length l)"
  apply (cases ins; simp add: per_jit_ins_def)
  subgoal for x1 x2 x3 x4
    apply (simp add: per_jit_load_reg64_def)
    apply (erule conjE)
    apply (erule conjE)
    by simp 
  subgoal for x1 x2 x3 x4
    apply (cases x3; simp)
    subgoal for y
      apply (simp add: per_jit_store_reg64_def)
    apply (erule conjE)
    apply (erule conjE)
    by simp 
    done
  subgoal for x1 x2 x3
    apply (cases x1; cases x3; simp)
    subgoal for y
      apply (simp add: per_jit_add_imm64_1_def)
      apply (erule conjE)
      apply (erule conjE)
        by simp
    subgoal for y
      apply (simp add: per_jit_add_reg64_1_def)
      using x64_encode_length_ge_1 by auto
    subgoal for y
      apply (simp add: per_jit_sub_reg64_1_def)
      using x64_encode_length_ge_1 by force
    subgoal for y
      apply (simp add: per_jit_mul_reg64_def)
      apply (erule conjE)
      apply (erule conjE)
      apply (cases "bpf_to_x64_reg x2"; simp)
      done

    subgoal for y
      apply (simp add: per_jit_or_reg64_1_def)
    using x64_encode_app_length_minus_1
    by (metis One_nat_def x64_encode_length_ge_1)
    subgoal for y
      apply (simp add: per_jit_and_reg64_1_def)
      using x64_encode_length_ge_1 by auto
    subgoal for y
      apply (simp add: per_jit_shift_lsh_reg64_def)
      apply (erule conjE)
      apply (erule conjE)
      apply (cases "bpf_to_x64_reg x2"; cases "bpf_to_x64_reg y"; simp)
      using x64_encode_length_ge_1 by force
    subgoal for y
      apply (simp add: per_jit_shift_rsh_reg64_def)
      apply (erule conjE)
      apply (erule conjE)
      apply (cases "bpf_to_x64_reg x2"; cases "bpf_to_x64_reg y"; simp)
      using x64_encode_length_ge_1 by force
    subgoal for y
      apply (simp add: per_jit_xor_reg64_1_def)
      apply (erule conjE)
      apply (erule conjE)
      using x64_encode_length_ge_1 by force
    subgoal for y
      apply (simp add: per_jit_mov_reg64_1_def)
      apply (erule conjE)
      apply (erule conjE)
      using x64_encode_length_ge_1 by force
    subgoal for y
      apply (simp add: per_jit_shift_arsh_reg64_def)
      apply (erule conjE)
      apply (erule conjE)
      apply (cases "bpf_to_x64_reg x2"; cases "bpf_to_x64_reg y"; simp)
      using x64_encode_length_ge_1 by force
    done
  subgoal for x1 x2 x3 x4
    apply (cases x3; simp)
    subgoal for y
      apply (simp add: per_jit_jcc_def Let_def)
      apply (cases "(case x1 of Eq \<Rightarrow> Cond_e | Gt \<Rightarrow> Cond_a | Ge \<Rightarrow> Cond_ae | Lt \<Rightarrow> Cond_b | Le \<Rightarrow> Cond_be | Ne \<Rightarrow> Cond_ne | SGt \<Rightarrow> Cond_g
         | SGe \<Rightarrow> Cond_ge | SLt \<Rightarrow> Cond_l | SLe \<Rightarrow> Cond_le) =
        Cond_e"; simp)
    apply (erule conjE)
    apply (erule conjE)
      by (simp add: x64_encode_app_length_minus_1)
    done
  subgoal for x1 x2
    apply (simp add: per_jit_call_reg_def)
      using x64_encode_length_ge_1 by force
  subgoal
    apply (simp add: per_jit_exit_def)
    using x64_encode_length_ge_1 by force
  done

lemma x64_bin_is_sequential_more: "
  x64_bin_is_sequential n l pc \<Longrightarrow>
  x64_bin_is_sequential (n+m) l pc"
  apply (induction n arbitrary: l pc m; simp)
  subgoal for n1 l pc m
    apply (cases "pc = length l"; simp)
    apply (cases "x64_decode pc l"; simp)
    subgoal for ins
      apply (cases ins; simp)
      subgoal for sz ins1
        apply (cases ins1; simp)
        done
      done
    done
  done


lemma list_in_list_length_app [simp]: "list_in_list l (length l1 + n) (l1 @ l2) = list_in_list l n l2"
  apply (induction l arbitrary: n l1 l2)
  subgoal for n l1 l2
    by simp
  subgoal for a l n l1 l2
    apply simp
    by (metis add_Suc_right)
  done


lemma x64_decode_encode_0 [simp]: "x64_decode 0 (x64_encode ins1 @ l) = Some (length (x64_encode ins1), ins1)"
  by (metis append_Nil list.size(3) list_in_list_prop_aux2 x64_encode_decode_consistency)

lemma x64_decode_encode_1 [simp]: "
  x64_decode (length (x64_encode ins1))
  (x64_encode ins1 @ x64_encode ins2 @ l) = Some (length (x64_encode ins2), ins2)"
  using list_in_list_length_app
  using list_in_list_prop_aux2 x64_encode_decode_consistency by blast

lemma x64_decode_encode_2 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ l) = Some (length (x64_encode ins3), ins3)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins3"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_3 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ l) = Some (length (x64_encode ins4), ins4)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins4"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_4 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3) + length (x64_encode ins4))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5 @ l) = Some (length (x64_encode ins5), ins5)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins5"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_5 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3)
   + length (x64_encode ins4) + length (x64_encode ins5))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5
   @ x64_encode ins6 @ l) = Some (length (x64_encode ins6), ins6)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins6"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_6 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3)
   + length (x64_encode ins4) + length (x64_encode ins5) + length (x64_encode ins6))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5
   @ x64_encode ins6 @ x64_encode ins7 @ l) = Some (length (x64_encode ins7), ins7)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins7"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_7 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3)
   + length (x64_encode ins4) + length (x64_encode ins5) + length (x64_encode ins6) + length (x64_encode ins7))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5
   @ x64_encode ins6 @ x64_encode ins7 @ x64_encode ins8 @ l) = Some (length (x64_encode ins8), ins8)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins8"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_8 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3)
   + length (x64_encode ins4) + length (x64_encode ins5) + length (x64_encode ins6) + length (x64_encode ins7)
   + length (x64_encode ins8))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5
   @ x64_encode ins6 @ x64_encode ins7 @ x64_encode ins8 @ x64_encode ins9 @ l) = Some (length (x64_encode ins9), ins9)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins9"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_decode_encode_9 [simp]: "
  x64_decode (length (x64_encode ins1) + length (x64_encode ins2) + length (x64_encode ins3)
   + length (x64_encode ins4) + length (x64_encode ins5) + length (x64_encode ins6) + length (x64_encode ins7)
   + length (x64_encode ins8) + length (x64_encode ins9))
  (x64_encode ins1 @ x64_encode ins2 @ x64_encode ins3 @ x64_encode ins4 @ x64_encode ins5
   @ x64_encode ins6 @ x64_encode ins7 @ x64_encode ins8 @ x64_encode ins9 @ x64_encode ins10 @ l) = Some (length (x64_encode ins10), ins10)"
  apply (rule x64_encode_decode_consistency [of "x64_encode ins10"])
  subgoal
    by (metis append_assoc length_append list_in_list_prop_aux2)
  subgoal by simp
  subgoal by simp
  done

lemma x64_bin_is_sequential_mul_rax: "num = (4::nat) \<Longrightarrow>
    off = 0 \<Longrightarrow>
    l = x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @ x64_encode (Ppushl_r RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Ppopl RDX) \<Longrightarrow>
    bpf_to_x64_reg x2 = RAX \<Longrightarrow>
    x64_bin_is_sequential
     (length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) +
      (length (x64_encode (Ppushl_r RDX)) + (length (x64_encode (Pimulq_r REG_SCRATCH)) + length (x64_encode (Ppopl RDX)))))
     (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @ x64_encode (Ppushl_r RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Ppopl RDX)) 0"
  apply (cases "length l"; simp)
  apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
  subgoal for n1 
    apply (cases n1; simp)
    apply (metis (no_types, lifting) add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
    subgoal for n2
      apply (cases n2; simp)
      apply (metis bot_nat_0.extremum le_add_same_cancel2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis Suc4_eq_add_4 Suc_n_not_le_n add_0 length_append x64_encode_app_length_ge_4)
        subgoal for n4 
          apply (subgoal_tac "x64_decode
        (length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) + length (x64_encode (Ppushl_r RDX)) +
         length (x64_encode (Pimulq_r REG_SCRATCH)))
        (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @
         x64_encode (Ppushl_r RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Ppopl RDX)) = Some (
      length (x64_encode (Ppopl RDX)),
        Ppopl RDX)")
          subgoal apply simp
            apply (cases n4; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_3)
        done
      done
    done
  done

lemma x64_bin_is_sequential_mul_rbx: "
  bpf_to_x64_reg x2 = r \<Longrightarrow>
  x64_bin_is_sequential
     (length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) +
      (length (x64_encode (Ppushl_r RAX)) +
       (length (x64_encode (Pmovq_rr RAX r)) +
        (length (x64_encode (Ppushl_r RDX)) +
         (length (x64_encode (Pimulq_r REG_SCRATCH)) +
          (length (x64_encode (Ppopl RDX)) + (length (x64_encode (Pmovq_rr r RAX)) + length (x64_encode (Ppopl RAX)))))))))
     (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @
      x64_encode (Ppushl_r RAX) @
      x64_encode (Pmovq_rr RAX r) @
      x64_encode (Ppushl_r RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Ppopl RDX) @ x64_encode (Pmovq_rr r RAX) @ x64_encode (Ppopl RAX))
     0"
  apply (cases "(length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) +
      (length (x64_encode (Ppushl_r RAX)) +
       (length (x64_encode (Pmovq_rr RAX r)) +
        (length (x64_encode (Ppushl_r RDX)) +
         (length (x64_encode (Pimulq_r REG_SCRATCH)) +
          (length (x64_encode (Ppopl RDX)) + (length (x64_encode (Pmovq_rr r RAX)) + length (x64_encode (Ppopl RAX)))))))))"; simp)
  apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
  subgoal for n1 
    apply (cases n1; simp)
    apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
    subgoal for n2
      apply (cases n2; simp)
      apply (metis add_le_same_cancel2 le_SucE le_add2 length_append not_numeral_le_zero numeral_Bit0 x64_encode_app_length_ge_8)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis add_2_eq_Suc le_add2 length_append not_less_eq_eq numeral_2_eq_2 numeral_Bit0 x64_encode_app_length_ge_8)
        subgoal for n4 
          apply (cases n4; simp)
          apply (metis add_2_eq_Suc add_le_same_cancel2 length_append not_numeral_le_zero numeral_2_eq_2 numeral_Bit0
              x64_encode_app_length_ge_8)
          subgoal for n5 
            apply (cases n5; simp)
            apply (metis Suc4_eq_add_4 le_add2 length_append not_less_eq_eq numeral_2_eq_2 numeral_Bit0 x64_encode_app_length_ge_8)
            subgoal for n6
              apply (cases n6; simp)
              apply (metis One_nat_def Suc4_eq_add_4 Suc_1 add_2_eq_Suc' le_add2 length_append not_less_eq_eq numeral_Bit0 x64_encode_app_length_ge_8)
              subgoal for n7
                apply (cases n7; simp)
                apply (metis Suc4_eq_add_4 Suc_n_not_le_n add_0 length_append numeral_Bit0 x64_encode_app_length_ge_8)
                subgoal for n8
                  apply (subgoal_tac "x64_decode
           (length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) + length (x64_encode (Ppushl_r RAX)) + length (x64_encode (Pmovq_rr RAX r)) +
            length (x64_encode (Ppushl_r RDX)) +
            length (x64_encode (Pimulq_r REG_SCRATCH)) +
            length (x64_encode (Ppopl RDX)) +
            length (x64_encode (Pmovq_rr r RAX)))
           (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @
            x64_encode (Ppushl_r RAX) @
            x64_encode (Pmovq_rr RAX r) @
            x64_encode (Ppushl_r RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Ppopl RDX) @ x64_encode (Pmovq_rr r RAX) @ x64_encode (Ppopl RAX)) = Some (
      length (x64_encode (Ppopl RAX)),
        Ppopl RAX)")
                  subgoal apply simp
                    apply (cases n8; simp)
                    apply (simp add: x64_encode_def Let_def)
                    done
                  apply (rule x64_encode_decode_consistency [of "x64_encode (Ppopl RAX)"])
                  subgoal 
                    using list_in_list_length_app append_assoc length_append list_in_list_prop_aux2
                  proof -
                    have "\<forall>ws wsa. list_in_list (ws::8 word list) (length wsa) (wsa @ ws)"
                      by (metis (no_types) append_eq_append_conv2 list_in_list_prop_aux2)
                    then show ?thesis
                      by (smt (z3) append_assoc length_append)
                  qed
                  subgoal by simp
                  subgoal by simp
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma x64_bin_is_sequential_mul_rdx: "x64_bin_is_sequential
     (length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) +
      (length (x64_encode (Ppushl_r RAX)) +
       (length (x64_encode (Pmovq_rr RAX RDX)) +
        (length (x64_encode (Pimulq_r REG_SCRATCH)) + (length (x64_encode (Pmovq_rr RDX RAX)) + length (x64_encode (Ppopl RAX)))))))
     (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @
      x64_encode (Ppushl_r RAX) @ x64_encode (Pmovq_rr RAX RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Pmovq_rr RDX RAX) @ x64_encode (Ppopl RAX))
     0"
  apply (cases "(length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) +
      (length (x64_encode (Ppushl_r RAX)) +
       (length (x64_encode (Pmovq_rr RAX RDX)) +
        (length (x64_encode (Pimulq_r REG_SCRATCH)) + (length (x64_encode (Pmovq_rr RDX RAX)) + length (x64_encode (Ppopl RAX)))))))"; simp)
  apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
  subgoal for n1 
    apply (cases n1; simp)
    apply (metis (no_types, lifting) add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
    subgoal for n2
      apply (cases n2; simp)
      apply (metis le_add_same_cancel1 length_append less_eq_nat.simps(1) not_less_eq_eq numeral_3_eq_3 numeral_Bit0 x64_encode_app_length_ge_6)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis add_le_same_cancel2 length_append not_numeral_le_zero numeral_3_eq_3 numeral_Bit0 x64_encode_app_length_ge_6)
        subgoal for n4 
          apply (cases n4; simp)
          apply (metis Suc3_eq_add_3 add_2_eq_Suc' add_le_same_cancel1 length_append not_numeral_le_zero numeral_3_eq_3 numeral_Bit0 x64_encode_app_length_ge_6)
          subgoal for n5 
             apply (cases n5; simp)
            apply (metis Suc3_eq_add_3 Suc_n_not_le_n length_append numeral_3_eq_3 numeral_Bit0 x64_encode_app_length_ge_6)
            subgoal for n6 
          apply (subgoal_tac "x64_decode
              (length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1))) + length (x64_encode (Ppushl_r RAX)) + length (x64_encode (Pmovq_rr RAX RDX)) +
               length (x64_encode (Pimulq_r REG_SCRATCH)) +
               length (x64_encode (Pmovq_rr RDX RAX)))
              (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg y1)) @
               x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr RAX RDX) @ x64_encode (Pimulq_r REG_SCRATCH) @ x64_encode (Pmovq_rr RDX RAX) @ x64_encode (Ppopl RAX)) = Some (
      length (x64_encode (Ppopl RAX)),
        Ppopl RAX)")
          subgoal apply simp
            apply (cases n6; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (smt (verit, ccfv_threshold) append_eq_append_conv2 x64_decode_encode_5)
        done
      done
    done
  done
    done
  done

lemma x64_bin_is_sequential_mul: "(case x3 of SOImm (word::32 signed word) \<Rightarrow> None | SOReg (x::bpf_ireg) \<Rightarrow> per_jit_mul_reg64 x2 x) = Some (num, off, l) \<Longrightarrow>
    ins = BPF_ALU64 BPF_MUL x2 x3 \<Longrightarrow> x64_bin_is_sequential (length l) l 0"
  apply (cases x3; simp)
  subgoal for y1
    apply (simp add: per_jit_mul_reg64_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (drule sym [of _ l])
    apply (cases "bpf_to_x64_reg x2"; simp)
    subgoal using x64_bin_is_sequential_mul_rax by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rdx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    subgoal using x64_bin_is_sequential_mul_rbx by blast
    done
  done


lemma x64_bin_is_sequential_mul_lsh: 
  "(case x3 of SOImm (word::32 signed word) \<Rightarrow> None | SOReg (x::bpf_ireg) \<Rightarrow> per_jit_shift_lsh_reg64 x2 x) = Some (num, off, l) \<Longrightarrow>
    ins = BPF_ALU64 BPF_LSH x2 x3 \<Longrightarrow> x64_bin_is_sequential (length l) l 0"
  apply (cases x3; simp)
  subgoal for y1
    apply (simp add: per_jit_shift_lsh_reg64_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (subgoal_tac "bpf_to_x64_reg x2 =RCX \<or> bpf_to_x64_reg x2 \<noteq> RCX")
     prefer 2 subgoal by auto
    apply (erule disjE)
    subgoal
      apply simp
      apply (subgoal_tac "bpf_to_x64_reg y1 =RCX \<or> bpf_to_x64_reg y1 \<noteq> RCX")
       prefer 2 subgoal by auto
      apply (erule disjE)
      subgoal
        apply simp
        apply (cases "length l"; simp)
         apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
        subgoal for n1
          apply (drule sym [of _ l])
          apply simp

            apply (subgoal_tac "x64_decode 0 (x64_encode (Pshlq_r RCX)) = Some (
    length (x64_encode (Pshlq_r RCX)),
      Pshlq_r RCX)")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          apply (subgoal_tac "num=5")
           prefer 2 subgoal
            by (cases "bpf_to_x64_reg y1"; simp)
          apply (subgoal_tac "l = x64_encode (Ppushl_r (bpf_to_x64_reg y1)) @
            x64_encode (Pxchgq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1)) @
            x64_encode (Pshlq_r (bpf_to_x64_reg y1)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Ppopl (bpf_to_x64_reg y1))")
           prefer 2 subgoal
            by (cases "bpf_to_x64_reg y1"; simp)
          apply simp
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1 
            apply (cases n1; simp)
            apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
            subgoal for n2
              apply (cases n2; simp)
              apply (metis One_nat_def Suc_1 eval_nat_numeral(3) le_add2 length_append not_less_eq_eq numeral_Bit0 x64_encode_app_length_ge_5)
              subgoal for n3
                apply (cases n3; simp)
                apply (metis eval_nat_numeral(2) le_add2 length_append not_less_eq_eq numeral_3_eq_3 semiring_norm(26,27) x64_encode_app_length_ge_4)
                subgoal for n4 
                  apply (cases n4; simp)
                  apply (metis One_nat_def Suc4_eq_add_4 Suc_n_not_le_n length_append one_plus_numeral semiring_norm(3) x64_encode_app_length_ge_5)
                  subgoal for n5 
                     apply (subgoal_tac "x64_decode
           (length (x64_encode (Ppushl_r (bpf_to_x64_reg y1))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg y1))) +
            length (x64_encode (Pshlq_r (bpf_to_x64_reg y1))) +
            length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1))))
           (x64_encode (Ppushl_r (bpf_to_x64_reg y1)) @
            x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg y1)) @
            x64_encode (Pshlq_r (bpf_to_x64_reg y1)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Ppopl (bpf_to_x64_reg y1))) = Some (
      length (x64_encode (Ppopl (bpf_to_x64_reg y1))),
        Ppopl (bpf_to_x64_reg y1))")
          subgoal apply simp
            apply (cases n5; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (smt (verit, ccfv_threshold) append_eq_append_conv2 x64_decode_encode_4)
        done
      done
    done
  done
  done
  apply (subgoal_tac "l= x64_encode (Ppushl_r RCX) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Pshlq_r (bpf_to_x64_reg x2)) @ x64_encode (Ppopl RCX)")
  prefer 2 subgoal by (cases "bpf_to_x64_reg x2"; simp)
  apply simp
  apply (cases "length l"; simp)
  apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
  subgoal for n1 
    apply (cases n1; simp)
    apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
    subgoal for n2
      apply (cases n2; simp)
      apply (metis le_add2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis One_nat_def add_le_same_cancel2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3 x64_encode_length_ge_1)
        subgoal for n4 
         apply (subgoal_tac "x64_decode
           (length (x64_encode (Ppushl_r RCX)) + length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1))) + length (x64_encode (Pshlq_r (bpf_to_x64_reg x2))))
           (x64_encode (Ppushl_r RCX) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Pshlq_r (bpf_to_x64_reg x2)) @ x64_encode (Ppopl RCX)) = Some (
      length (x64_encode (Ppopl RCX)),
        Ppopl RCX)")
          subgoal apply simp
            apply (cases n4; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_3)
        done
        done
      done
    done
  done


lemma x64_bin_is_sequential_mul_rsh: 
  "(case x3 of SOImm (word::32 signed word) \<Rightarrow> None | SOReg (x::bpf_ireg) \<Rightarrow> per_jit_shift_rsh_reg64 x2 x) = Some (num, off, l) \<Longrightarrow>
    ins = BPF_ALU64 BPF_RSH x2 x3 \<Longrightarrow> x64_bin_is_sequential (length l) l 0"
  apply (cases x3; simp)
  subgoal for y1
    apply (simp add: per_jit_shift_rsh_reg64_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (subgoal_tac "bpf_to_x64_reg x2 =RCX \<or> bpf_to_x64_reg x2 \<noteq> RCX")
     prefer 2 subgoal by auto
    apply (erule disjE)
    subgoal
      apply simp
      apply (subgoal_tac "bpf_to_x64_reg y1 =RCX \<or> bpf_to_x64_reg y1 \<noteq> RCX")
       prefer 2 subgoal by auto
      apply (erule disjE)
      subgoal
        apply simp
        apply (cases "length l"; simp)
         apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
        subgoal for n1
          apply (drule sym [of _ l])
          apply simp

            apply (subgoal_tac "x64_decode 0 (x64_encode (Pshrq_r RCX)) = Some (
    length (x64_encode (Pshrq_r RCX)),
      Pshrq_r RCX)")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          apply (subgoal_tac "num=5")
           prefer 2 subgoal
            by (cases "bpf_to_x64_reg y1"; simp)
          apply (subgoal_tac "l = x64_encode (Ppushl_r (bpf_to_x64_reg y1)) @
            x64_encode (Pxchgq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1)) @
            x64_encode (Pshrq_r (bpf_to_x64_reg y1)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Ppopl (bpf_to_x64_reg y1))")
           prefer 2 subgoal
            by (cases "bpf_to_x64_reg y1"; simp)
          apply simp
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1 
            apply (cases n1; simp)
            apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
            subgoal for n2
              apply (cases n2; simp)
              apply (metis One_nat_def Suc_1 eval_nat_numeral(3) le_add2 length_append not_less_eq_eq numeral_Bit0 x64_encode_app_length_ge_5)
              subgoal for n3
                apply (cases n3; simp)
                apply (metis eval_nat_numeral(2) le_add2 length_append not_less_eq_eq numeral_3_eq_3 semiring_norm(26,27) x64_encode_app_length_ge_4)
                subgoal for n4 
                  apply (cases n4; simp)
                  apply (metis One_nat_def Suc4_eq_add_4 Suc_n_not_le_n length_append one_plus_numeral semiring_norm(3) x64_encode_app_length_ge_5)
                  subgoal for n5 
                     apply (subgoal_tac "x64_decode
           (length (x64_encode (Ppushl_r (bpf_to_x64_reg y1))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg y1))) +
            length (x64_encode (Pshrq_r (bpf_to_x64_reg y1))) +
            length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1))))
           (x64_encode (Ppushl_r (bpf_to_x64_reg y1)) @
            x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg y1)) @
            x64_encode (Pshrq_r (bpf_to_x64_reg y1)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Ppopl (bpf_to_x64_reg y1))) = Some (
      length (x64_encode (Ppopl (bpf_to_x64_reg y1))),
        Ppopl (bpf_to_x64_reg y1))")
          subgoal apply simp
            apply (cases n5; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (smt (verit, ccfv_threshold) append_eq_append_conv2 x64_decode_encode_4)
        done
      done
    done
  done
  done
  apply (subgoal_tac "l= x64_encode (Ppushl_r RCX) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Pshrq_r (bpf_to_x64_reg x2)) @ x64_encode (Ppopl RCX)")
  prefer 2 subgoal by (cases "bpf_to_x64_reg x2"; simp)
  apply simp
  apply (cases "length l"; simp)
  apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
  subgoal for n1 
    apply (cases n1; simp)
    apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
    subgoal for n2
      apply (cases n2; simp)
      apply (metis le_add2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis One_nat_def add_le_same_cancel2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3 x64_encode_length_ge_1)
        subgoal for n4 
         apply (subgoal_tac "x64_decode
           (length (x64_encode (Ppushl_r RCX)) + length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1))) + length (x64_encode (Pshrq_r (bpf_to_x64_reg x2))))
           (x64_encode (Ppushl_r RCX) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Pshrq_r (bpf_to_x64_reg x2)) @ x64_encode (Ppopl RCX)) = Some (
      length (x64_encode (Ppopl RCX)),
        Ppopl RCX)")
          subgoal apply simp
            apply (cases n4; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_3)
        done
        done
      done
    done
  done



lemma x64_bin_is_sequential_mul_arsh: 
  "(case x3 of SOImm (word::32 signed word) \<Rightarrow> None | SOReg (x::bpf_ireg) \<Rightarrow> per_jit_shift_arsh_reg64 x2 x) = Some (num, off, l) \<Longrightarrow>
    ins = BPF_ALU64 BPF_ARSH x2 x3 \<Longrightarrow> x64_bin_is_sequential (length l) l 0"
  apply (cases x3; simp)
  subgoal for y1
    apply (simp add: per_jit_shift_arsh_reg64_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (subgoal_tac "bpf_to_x64_reg x2 =RCX \<or> bpf_to_x64_reg x2 \<noteq> RCX")
     prefer 2 subgoal by auto
    apply (erule disjE)
    subgoal
      apply simp
      apply (subgoal_tac "bpf_to_x64_reg y1 =RCX \<or> bpf_to_x64_reg y1 \<noteq> RCX")
       prefer 2 subgoal by auto
      apply (erule disjE)
      subgoal
        apply simp
        apply (cases "length l"; simp)
         apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
        subgoal for n1
          apply (drule sym [of _ l])
          apply simp

            apply (subgoal_tac "x64_decode 0 (x64_encode (Psarq_r RCX)) = Some (
    length (x64_encode (Psarq_r RCX)),
      Psarq_r RCX)")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          apply (subgoal_tac "num=5")
           prefer 2 subgoal
            by (cases "bpf_to_x64_reg y1"; simp)
          apply (subgoal_tac "l = x64_encode (Ppushl_r (bpf_to_x64_reg y1)) @
            x64_encode (Pxchgq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1)) @
            x64_encode (Psarq_r (bpf_to_x64_reg y1)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Ppopl (bpf_to_x64_reg y1))")
           prefer 2 subgoal
            by (cases "bpf_to_x64_reg y1"; simp)
          apply simp
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1 
            apply (cases n1; simp)
            apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
            subgoal for n2
              apply (cases n2; simp)
              apply (metis One_nat_def Suc_1 eval_nat_numeral(3) le_add2 length_append not_less_eq_eq numeral_Bit0 x64_encode_app_length_ge_5)
              subgoal for n3
                apply (cases n3; simp)
                apply (metis eval_nat_numeral(2) le_add2 length_append not_less_eq_eq numeral_3_eq_3 semiring_norm(26,27) x64_encode_app_length_ge_4)
                subgoal for n4 
                  apply (cases n4; simp)
                  apply (metis One_nat_def Suc4_eq_add_4 Suc_n_not_le_n length_append one_plus_numeral semiring_norm(3) x64_encode_app_length_ge_5)
                  subgoal for n5 
                     apply (subgoal_tac "x64_decode
           (length (x64_encode (Ppushl_r (bpf_to_x64_reg y1))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg y1))) +
            length (x64_encode (Psarq_r (bpf_to_x64_reg y1))) +
            length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1))))
           (x64_encode (Ppushl_r (bpf_to_x64_reg y1)) @
            x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg y1)) @
            x64_encode (Psarq_r (bpf_to_x64_reg y1)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Ppopl (bpf_to_x64_reg y1))) = Some (
      length (x64_encode (Ppopl (bpf_to_x64_reg y1))),
        Ppopl (bpf_to_x64_reg y1))")
          subgoal apply simp
            apply (cases n5; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (smt (verit, ccfv_threshold) append_eq_append_conv2 x64_decode_encode_4)
        done
      done
    done
  done
  done
  apply (subgoal_tac "l= x64_encode (Ppushl_r RCX) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Psarq_r (bpf_to_x64_reg x2)) @ x64_encode (Ppopl RCX)")
  prefer 2 subgoal by (cases "bpf_to_x64_reg x2"; simp)
  apply simp
  apply (cases "length l"; simp)
  apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
  subgoal for n1 
    apply (cases n1; simp)
    apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
    subgoal for n2
      apply (cases n2; simp)
      apply (metis le_add2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis One_nat_def add_le_same_cancel2 length_append not_less_eq_eq numeral_3_eq_3 x64_encode_app_length_ge_3 x64_encode_length_ge_1)
        subgoal for n4 
         apply (subgoal_tac "x64_decode
           (length (x64_encode (Ppushl_r RCX)) + length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1))) + length (x64_encode (Psarq_r (bpf_to_x64_reg x2))))
           (x64_encode (Ppushl_r RCX) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg y1)) @ x64_encode (Psarq_r (bpf_to_x64_reg x2)) @ x64_encode (Ppopl RCX)) = Some (
      length (x64_encode (Ppopl RCX)),
        Ppopl RCX)")
          subgoal apply simp
            apply (cases n4; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_3)
        done
        done
      done
    done
  done

lemma x64_bin_is_sequential_per_jit_ins: "\<forall>(src::ireg) (dst::ireg) t1. x64_decode 0 l \<noteq> Some (t1, Pcmpq_rr src dst) \<Longrightarrow>
    \<forall>d t2. x64_decode 0 l \<noteq> Some (t2, Pcall_i d) \<Longrightarrow>
    x64_decode 0 l \<noteq> Some (1,Pret) \<Longrightarrow> 
    per_jit_ins ins = Some (num, off, l) \<Longrightarrow> x64_bin_is_sequential (length l) l 0"
  apply (simp add: per_jit_ins_def)
  apply (cases ins; simp)
  subgoal for x1 x2 x3 x4
    apply (simp add: per_jit_load_reg64_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (drule sym [of _ l])
    apply (cases "length l"; simp)
    apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
    subgoal for n1
    apply (cases n1; simp)
      apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
      subgoal for n2
        apply (cases n2; simp)
        apply (metis Suc_n_not_le_n length_append numeral_3_eq_3 x64_encode_app_length_ge_3)
      subgoal for n3
        apply (subgoal_tac "x64_decode
           (length (x64_encode (Pmovl_ri REG_SCRATCH (scast x4))) + length (x64_encode (Paddq_rr REG_SCRATCH (bpf_to_x64_reg x3))))
           (x64_encode (Pmovl_ri REG_SCRATCH (scast x4)) @
            x64_encode (Paddq_rr REG_SCRATCH (bpf_to_x64_reg x3)) @
            x64_encode (Pmov_rm (bpf_to_x64_reg x2) (Addrmode (Some REG_SCRATCH) None 0) x1)) = Some (
length (x64_encode (Pmov_rm (bpf_to_x64_reg x2) (Addrmode (Some REG_SCRATCH) None 0) x1)),
  Pmov_rm (bpf_to_x64_reg x2) (Addrmode (Some REG_SCRATCH) None 0) x1)")
        subgoal apply simp
        apply (cases n3; simp)
          apply (simp add: x64_encode_def Let_def)
          done
        by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_2)
      done
    done
  done
  subgoal for x1 x2 x3 x4
    apply (cases x3; simp)
    subgoal for y1
    apply (simp add: per_jit_store_reg64_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (drule sym [of _ l])
    apply (cases "length l"; simp)
    apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
    subgoal for n1
    apply (cases n1; simp)
      apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
      subgoal for n2
        apply (cases n2; simp)
        apply (metis bot_nat_0.extremum eval_nat_numeral(3) le_add_same_cancel2 length_append not_less_eq_eq numeral_2_eq_2 x64_encode_app_length_ge_3)
      subgoal for n3
        apply (cases n3; simp)
        apply (metis Suc4_eq_add_4 Suc_n_not_le_n add_0 length_append x64_encode_app_length_ge_4)
        subgoal for n4
          apply (subgoal_tac "x64_decode
             (length (x64_encode (Pmovl_ri REG_SCRATCH (scast x4))) + length (x64_encode (Paddq_rr REG_SCRATCH (bpf_to_x64_reg x2))) +
              length (x64_encode (Pmovq_rr REG_OTHER_SCRATCH (bpf_to_x64_reg y1))))
             (x64_encode (Pmovl_ri REG_SCRATCH (scast x4)) @
              x64_encode (Paddq_rr REG_SCRATCH (bpf_to_x64_reg x2)) @
              x64_encode (Pmovq_rr REG_OTHER_SCRATCH (bpf_to_x64_reg y1)) @ 
              x64_encode (Pmov_mr (Addrmode (Some REG_SCRATCH) None 0) REG_OTHER_SCRATCH x1)) = Some (
  length (x64_encode (Pmov_mr (Addrmode (Some REG_SCRATCH) None 0) REG_OTHER_SCRATCH x1)),
    Pmov_mr (Addrmode (Some REG_SCRATCH) None 0) REG_OTHER_SCRATCH x1)")
            subgoal apply simp
              apply (cases n4; simp)
              apply (simp add: x64_encode_def Let_def)
              done
            by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_3)
          done
        done
      done
    done
  done
  subgoal for x1 x2 x3
    apply (cases x1; simp)
    subgoal
      apply (cases x3; simp)
      subgoal for y1
        apply (simp add: per_jit_add_imm64_1_def)
        apply (erule subst)
        apply (erule conjE)
        apply (erule conjE)
        apply (drule sym [of _ l])
        apply (cases "length l"; simp)
        apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
        subgoal for n1
        apply (cases n1; simp)
          apply (metis add_is_0 not_one_le_zero one_is_add x64_encode_length_ge_1)
          subgoal for n2
            apply (subgoal_tac "x64_decode (length (x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast y1))))
             (x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast y1)) @
              x64_encode (Paddq_rr (bpf_to_x64_reg x2) REG_OTHER_SCRATCH)) = Some (
    length (x64_encode (Paddq_rr (bpf_to_x64_reg x2) REG_OTHER_SCRATCH)),
      Paddq_rr (bpf_to_x64_reg x2) REG_OTHER_SCRATCH)")
            subgoal apply simp
              apply (cases n2; simp)
              apply (simp add: x64_encode_def Let_def)
              done
            by (metis (no_types, lifting) append_eq_append_conv2 x64_decode_encode_1)
          done
        done
      subgoal for y1
        apply (simp add: per_jit_add_reg64_1_def)
        apply (erule subst)
        apply (erule conjE)
        apply (erule conjE)
        apply (drule sym [of _ l])
        apply (cases "length l"; simp)
        apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
        subgoal for n1 
          apply (subgoal_tac "x64_decode 0 (x64_encode (Paddq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))) = Some (
      length (x64_encode (Paddq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
        Paddq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
          subgoal apply simp
            apply (cases n1; simp)
            apply (simp add: x64_encode_def Let_def)
            done
          by (metis append_eq_append_conv2 x64_decode_encode_0)
        done
      done
  
    subgoal
      apply (cases x3; simp)
      subgoal for y1
        apply (simp add: per_jit_sub_reg64_1_def)
        apply (erule subst)
        apply (erule conjE)
        apply (erule conjE)
        apply (drule sym [of _ l])
        apply (cases "length l"; simp)
        apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
        subgoal for n1
          apply (subgoal_tac "x64_decode 0 (x64_encode (Psubq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))) = Some (
  length (x64_encode (Psubq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
    Psubq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
            subgoal apply simp
              apply (cases n1; simp)
              apply (simp add: x64_encode_def Let_def)
              done
            by (metis append_eq_append_conv2 x64_decode_encode_0)
          done
        done
  
      subgoal
        using x64_bin_is_sequential_mul by blast
      subgoal
        apply (cases x3; simp)
        subgoal for y1
          apply (simp add: per_jit_or_reg64_1_def)
          apply (erule subst)
          apply (erule conjE)
          apply (erule conjE)
          apply (drule sym [of _ l])
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1
            apply (subgoal_tac "x64_decode 0 (x64_encode (Porq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))) = Some (
    length (x64_encode (Porq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
      Porq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          done
      subgoal
        apply (cases x3; simp)
        subgoal for y1
          apply (simp add: per_jit_and_reg64_1_def)
          apply (erule subst)
          apply (erule conjE)
          apply (erule conjE)
          apply (drule sym [of _ l])
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1
            apply (subgoal_tac "x64_decode 0 (x64_encode (Pandq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))) = Some (
    length (x64_encode (Pandq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
      Pandq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          done
        subgoal using x64_bin_is_sequential_mul_lsh by blast
        subgoal using x64_bin_is_sequential_mul_rsh by blast

      subgoal
        apply (cases x3; simp)
        subgoal for y1
          apply (simp add: per_jit_xor_reg64_1_def)
          apply (erule subst)
          apply (erule conjE)
          apply (erule conjE)
          apply (drule sym [of _ l])
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1
            apply (subgoal_tac "x64_decode 0 (x64_encode (Pxorq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))) = Some (
    length (x64_encode (Pxorq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
      Pxorq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          done

      subgoal
        apply (cases x3; simp)
        subgoal for y1
          apply (simp add: per_jit_mov_reg64_1_def)
          apply (erule subst)
          apply (erule conjE)
          apply (erule conjE)
          apply (drule sym [of _ l])
          apply (cases "length l"; simp)
          apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
          subgoal for n1
            apply (subgoal_tac "x64_decode 0 (x64_encode (Pmovq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))) = Some (
    length (x64_encode (Pmovq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
      Pmovq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
              subgoal apply simp
                apply (cases n1; simp)
                apply (simp add: x64_encode_def Let_def)
                done
              by (metis append_eq_append_conv2 x64_decode_encode_0)
            done
          done
        subgoal using x64_bin_is_sequential_mul_arsh by blast
        done

  subgoal for x1 x2 x3 x4
    apply (cases x3; simp)
    subgoal for y1
      apply (simp add: per_jit_jcc_def Let_def)
      apply (cases "(case x1 of Eq \<Rightarrow> Cond_e | Gt \<Rightarrow> Cond_a | Ge \<Rightarrow> Cond_ae | Lt \<Rightarrow> Cond_b | Le \<Rightarrow> Cond_be | Ne \<Rightarrow> Cond_ne | SGt \<Rightarrow> Cond_g | SGe \<Rightarrow> Cond_ge | SLt \<Rightarrow> Cond_l
         | SLe \<Rightarrow> Cond_le) =
        Cond_e"; simp)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (cases "length l"; simp)
    apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
      subgoal for n1
        apply (subgoal_tac "x64_decode 0 l = Some (
  length (x64_encode (Pcmpq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))),
  Pcmpq_rr (bpf_to_x64_reg x2) (bpf_to_x64_reg y1))")
        subgoal
          by simp

        apply (drule sym [of _ l])
        apply simp
        done
      done
    done

  subgoal for x1 x2
    apply (simp add: per_jit_call_reg_def Let_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (drule sym [of _ l])
    apply (cases "length l"; simp)
    apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
    subgoal for n1
      apply (subgoal_tac "x64_decode 0 (x64_encode (Pcall_i 0)) = Some (
    length (x64_encode (Pcall_i 0)), Pcall_i 0)")
        subgoal
          by simp
        using list_in_list_prop x64_encode_decode_consistency by blast
      done

    subgoal
    apply (simp add: per_jit_exit_def Let_def)
    apply (erule subst)
    apply (erule conjE)
    apply (erule conjE)
    apply (drule sym [of _ l])
    apply (cases "length l"; simp)
    apply (metis list.size(3) not_one_le_zero x64_encode_length_ge_1)
    subgoal for n1
      apply (subgoal_tac "x64_decode 0 (x64_encode Pret) = Some (
    length (x64_encode Pret), Pret)")
      subgoal

        apply (simp add: x64_encode_def)
        done
      by (metis append_eq_append_conv2 x64_decode_encode_0)

      done
    done

lemma x64_bin_is_sequential_x64_decode2:
  "jitper insns = Some lt \<Longrightarrow> 
  lt!pc = (num,off,l) \<Longrightarrow>
   pc < length lt  \<Longrightarrow>
  x64_decode 0 l \<noteq> None \<Longrightarrow> 
  x64_decode 0 l \<noteq> Some (1,Pret) \<Longrightarrow> 
  (\<not>(\<exists> src dst t1. x64_decode 0 l = Some(t1, Pcmpq_rr src dst))) \<Longrightarrow> 
  (\<not>(\<exists> d t2. x64_decode 0 l = Some(t2, Pcall_i d))) \<Longrightarrow>
  x64_bin_is_sequential (length l) l 0"
  apply (induction insns arbitrary: lt pc num off l; simp)

  subgoal for ins lp lt pc num off l
    apply (cases "per_jit_ins ins"; simp)
    subgoal for lp1
      apply (cases "jitper lp"; simp)
      subgoal for res
(**r here to use IH, we should discuss two cases:
- lp1 = (num, off, l), that is `pc = 0`
- res!unat pc = ... that is to use IH, and pc = Suc pc1
 *)
        apply (cases pc; simp)
        subgoal (* pc = 0 *)
          apply (subgoal_tac "lp1 = (num, off, l)")
           prefer 2 subgoal by auto
          using x64_bin_is_sequential_per_jit_ins
          by simp

        subgoal for pc1
          apply (subgoal_tac "pc1 < length lt")
          prefer 2 subgoal
            by simp
          apply (subgoal_tac "res ! pc1 = (num, off, l)")
          prefer 2 subgoal
            by auto
          by auto
        done
      done
    done
  done
end
