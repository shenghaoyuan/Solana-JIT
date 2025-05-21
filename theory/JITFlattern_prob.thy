theory JITFlattern_prob
  imports JITFlattern_def JITFlattern_aux
begin

(** see Solana-x64-Semantics nth_error branch `x64DecodeProp.thy`
  The current version could not be proven becasue of `!`
 *)
lemma x64_decode_length_none: "
  x64_decode (length l) l = None"
  sorry

lemma list_in_list_implies_set_relation:
  "list_in_list [x] pos l_jump \<Longrightarrow> x \<in> set l_jump"
  sorry
lemma list_in_list_x64_decode:
  "list_in_list l_bin pc l \<Longrightarrow> x64_decode n l_bin = Some v \<Longrightarrow> x64_decode (pc+n) l = Some v"
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

end
