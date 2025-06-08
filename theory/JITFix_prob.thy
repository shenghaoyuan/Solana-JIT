theory JITFix_prob
  imports JITFlattern JITFix_def
begin

(*
fun is_lt_list_nat:: "(nat list) \<Rightarrow> bool" where
"is_lt_list_nat [] = True" |
"is_lt_list_nat (x#xs) = (
  case xs of
  [] \<Rightarrow> True |
  y#ys \<Rightarrow> (x < y) \<and> (is_lt_list_nat ys)
)" *)

definition is_lt_list_nat :: "(nat list) \<Rightarrow> nat \<Rightarrow> bool" where
"is_lt_list_nat l m = (\<forall> i j. i < j \<and> j < length l \<longrightarrow> (l!i < l!j \<and> l!j < m))"


lemma jitflat_bpf_is_lt_list_nat_inv: "
  is_lt_list_nat (map fst l_pc) (length l_bin) \<Longrightarrow>
  jitflat_bpf l (l_bin, l_pc, l_jump) = (l_bin1, l_pc1, l_jump1) \<Longrightarrow>
    is_lt_list_nat (map fst l_pc1) (length l_bin1)"
  apply (induction l arbitrary: l_bin l_pc l_jump l_bin1 l_pc1 l_jump1; simp?)
  subgoal for a l1 l_bin l_pc l_jump l_bin1 l_pc1 l_jump1
    apply (cases a; simp)
    subgoal for na ba ca
      sorry
      sorry
      sorry
(*
is_lt_list_nat (map fst (l_pc @ [(length l_bin, aa)])) (length (l_bin @ c))
      using not_change_prefix_l_pc *)

lemma l_pc_index_corr_geric:
  "l_pc \<noteq> [] \<Longrightarrow> 
  pc < length l_pc \<Longrightarrow> 
  fst (l_pc!pc) = xpc \<Longrightarrow> 
  distinct (map fst l_pc) \<Longrightarrow>
  find_target_pc_in_l_pc2 l_pc xpc n = Some (pc+n)"
  apply (induction l_pc arbitrary: pc xpc; simp)
  subgoal for a l_pc1 pc xpc 
    apply (cases pc; simp)
    subgoal
      sorry
    sorry
done

lemma l_pc_index_corr:
  "l_pc \<noteq> [] \<Longrightarrow> 
   (unat pc) < length l_pc  \<Longrightarrow> 
  fst (l_pc! (unat pc)) = xpc \<Longrightarrow> 
  distinct (map fst l_pc) \<Longrightarrow>
  find_target_pc_in_l_pc2 l_pc xpc 0 = Some (unat pc)"
  sorry

lemma x64_bin_is_sequential_x64_decode3:
  "jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  num = snd (l_pc!(unat pc)) \<Longrightarrow>
  (\<not> (\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)) \<and> 
   \<not> (\<exists> sz imm. x64_decode xpc l_bin0 = Some(sz, Pcall_i imm)) \<and> 
   \<not>(\<exists> sz. x64_decode xpc l_bin0 = Some(sz, Pret_anchor))) \<Longrightarrow>
  jitper insns = Some lt \<Longrightarrow>
  well_formed_prog lt \<Longrightarrow>
  x64_bin_is_sequential num l_bin0 xpc"
  sorry

lemma fix_bpf_one_step_stuck: "fix_bpf_one_step l Stuck = Stuck"
  by (simp add: fix_bpf_one_step_def)

lemma fix_bpf_sem_stuck: "fix_bpf_sem n l Stuck = Stuck"
  by (induction n arbitrary: l; simp add: fix_bpf_one_step_stuck)

lemma fix_bpf_one_step_length_none: "fix_bpf_one_step (l_bin0, l_pc, l_jump) (Next (length l_bin0) xrs xm xss) = Stuck"
  by (simp add: fix_bpf_one_step_def x64_decode_length_none)

lemma x64_bin_is_sequential_equivalence :
  "x64_bin_is_sequential num l_bin0 xpc \<Longrightarrow>
  fix_bpf_sem num (l_bin0,l_pc,l_jump) (Next xpc xrs xm xss) = xst1 \<Longrightarrow>
  xst2 = x64_sem num l_bin0 (Next xpc xrs xm xss) \<Longrightarrow> 
  xst1 = xst2"
  apply (induction num arbitrary: l_bin0 xpc xrs xm xss l_pc l_jump xst1 xst2; simp)
  subgoal for n l_bin0 xpc xrs xm xss l_pc l_jump xst1 xst2
    apply (simp add: split: if_split_asm)
    subgoal \<comment>\<open> xpc = length l_bin0 \<close>
      by (simp add: x64_decode_length_none fix_bpf_one_step_length_none fix_bpf_sem_stuck)

    subgoal \<comment>\<open> xpc <> length l_bin0 \<close>
      apply (erule case_optionE; simp)
      subgoal for ins2
        apply (cases ins2; simp)
        subgoal for sz ins
          apply (cases ins; simp add: fix_bpf_one_step_def exec_instr_def)
          subgoal for x1
            apply (simp add: exec_push_def Let_def)
            apply (cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR x1)))"; simp)
            apply (simp add: x64_sem_stuck fix_bpf_sem_stuck)
            done
          subgoal for x1
            apply (simp add: exec_pop_def Let_def)
            apply (cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))"; simp)
            subgoal by (simp add: x64_sem_stuck fix_bpf_sem_stuck)
            subgoal for v1
              by (cases v1; simp add: x64_sem_stuck fix_bpf_sem_stuck)
            done
          subgoal for x1 x2 x3
            apply (simp add: exec_store_def Let_def)
            apply (cases "storev x3 xm (Vlong (eval_addrmode64 x1 xrs)) (Vlong (xrs (IR x2)))"; simp)
            apply (simp add: x64_sem_stuck fix_bpf_sem_stuck)
            done
          subgoal for x1 x2 x3
            apply (simp add: exec_load_def Let_def)
            apply (cases "loadv x3 xm (Vlong (eval_addrmode64 x2 xrs))"; simp)
            subgoal by (simp add: x64_sem_stuck fix_bpf_sem_stuck)
            subgoal for v1
              by (cases v1; simp add: x64_sem_stuck fix_bpf_sem_stuck)
            done
          subgoal for x1
            apply (subgoal_tac "\<exists> xrs1 xm1 xss1. exec_call_external xpc sz M64 xm xss xrs x1 = Next (xpc+sz) xrs1 xm1 xss1")
            prefer 2
            using exec_call_external_prop
             apply metis
            apply (erule exE)+
            subgoal for xrs1 xm1 xss1
              apply simp
              done
            done
          subgoal
            apply (subgoal_tac "\<exists> xrs1 xm1 xss1. exec_ret_external xpc sz M64 xm xss xrs = Next (xpc+sz) xrs1 xm1 xss1")
            prefer 2
            using exec_ret_external_prop
             apply metis
            apply (erule exE)+
            subgoal for xrs1 xm1 xss1
              apply simp
              done
            done
          done
        done
      done
    done
  done


end