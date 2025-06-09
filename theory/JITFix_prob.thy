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


(*lemma jitflat_bpf_is_lt_list_nat_inv: "
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
*)
(*
is_lt_list_nat (map fst (l_pc @ [(length l_bin, aa)])) (length (l_bin @ c))
      using not_change_prefix_l_pc *)

definition is_increase_list_l_pc::" (nat \<times> nat) list \<Rightarrow> x64_bin \<Rightarrow> bool" where 
  "is_increase_list_l_pc lt lt2 \<equiv> (\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length lt \<longrightarrow> fst (lt!idx1) < fst (lt!idx2)) \<and> 
    (\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> fst (lt!idx) <  (length lt2))"


lemma l_pc_elem_increases:
  "jitflat_bpf lt (l1, l_pc1, l_jump1) = (l, l_pc, l_jump) \<Longrightarrow> 
  is_increase_list_l_pc l_pc1 l1 \<Longrightarrow>
  \<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> snd(snd (lt!idx)) \<noteq> []  \<Longrightarrow>
  is_increase_list_l_pc l_pc l"
proof(induct lt arbitrary: l1 l_pc1 l_jump1 l l_pc l_jump)
    case Nil
    then show ?case by force
  next
    case (Cons a lt)
    assume assm0:"is_increase_list_l_pc l_pc1 l1" and
      assm1:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l, l_pc, l_jump)" and
      assm2:"\<forall> idx. idx \<ge>0 \<and> idx < length (a#lt) \<longrightarrow> snd(snd ((a#lt)!idx)) \<noteq> []"
      (*and assm2:"(a#lt) \<noteq> []"*)
    have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and>  jitflat_bpf lt (l2',l_pc2',l_jump2') = (l,l_pc,l_jump)"
      using jitflat_bpf_induct assm1 by blast 
    then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf lt (l2',l_pc2',l_jump2') = (l,l_pc,l_jump)" by auto

    hence b0_k: "jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2')" using b0 by simp
    hence b0_n:"l_pc2' = l_pc1@[(of_nat (length l1),fst a)]" by (cases a; simp)
    
    hence b3:"\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_pc1 \<longrightarrow> fst (l_pc2'!idx1) < fst (l_pc2'!idx2)" 
      using assm0 b0_n by (simp add: JITFix_prob.is_increase_list_l_pc_def nth_append) 
    have b4:"(fst (l_pc2'!(length l_pc1))) = (length l1)"
      by (simp add: b0_n) 
    have b5:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_pc1 \<longrightarrow> (fst (l_pc1!idx)) < (length l1))"
      using assm0 is_increase_list_l_pc_def by blast 
    hence "(\<forall> idx. idx \<ge>0 \<and> idx < length l_pc1 \<longrightarrow> (fst (l_pc1!idx)) < fst (l_pc2'!(length l_pc1)))"
      using b4 b5 by simp
    hence b7_1:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_pc1 \<longrightarrow> (fst (l_pc2'!idx)) < (fst (l_pc2'!(length l_pc1))))"
      by (simp add: b0_n nth_append) 
    hence b7:"(\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_pc2' \<longrightarrow> fst (l_pc2'!idx1) < fst (l_pc2'!idx2))" 
      using b7_1 by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 b0_n b3 length_append less_SucE list.size(3) list.size(4)) 

    have c0:"l2' = l1@(snd (snd a))" using b0_k by (cases a; simp)
    have c1:"(snd (snd a)) \<noteq> [] " using well_formed_prog_def
      using Cons.prems(3) by force 
    have c2:"length l1 < length l2'" using c0 c1 by simp 
    have "(\<forall> idx. idx \<ge>0 \<and> idx < length l_pc1 \<longrightarrow> (fst (l_pc2'!idx)) < (length l2'))"
      using b5 using b5 c2 by (metis b4 b7_1 dual_order.strict_trans) 
    hence b6:"(\<forall> idx. idx \<ge>0 \<and> idx < length l_pc2' \<longrightarrow> (fst (l_pc2'!idx)) < (length l2'))"
      using b0 b0_n b4
      by (metis One_nat_def add.commute c2 l_pc_length_prop less_SucE list.size(3) list.size(4) plus_1_eq_Suc) 
    hence bn:"is_increase_list_l_pc l_pc2' l2'"
      using b6 b7 is_increase_list_l_pc_def by simp
    then show ?case using b0 Cons assm2 bn
      by (metis Suc_leI le_imp_less_Suc length_Cons less_or_eq_imp_le nth_Cons_Suc) 
  qed

lemma l_pc_is_distinct:
  "jitflat_bpf lt (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow> 
  distinct (map fst l_pc1) \<Longrightarrow> 
  is_increase_list_l_pc l_pc1 l1 \<Longrightarrow> 
  \<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> snd(snd (lt!idx)) \<noteq> []  \<Longrightarrow>
  distinct (map fst l_pc)"
proof(induct lt arbitrary: l1 l_pc1 l_jump1 l_bin l_pc l_jump)
  case Nil
  then show ?case by simp
next
  case (Cons a lt)
  assume a0:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump)" and 
  a1:"distinct (map fst l_pc1)" and
  a2:"\<forall> idx. idx \<ge>0 \<and> idx < length (a#lt) \<longrightarrow> snd(snd ((a#lt)!idx)) \<noteq> []" and
  a3:"is_increase_list_l_pc l_pc1 l1"
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" using jitflat_bpf_induct a0 by simp
  then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" by auto
  hence b2_0:"l_pc2' = l_pc1@[(of_nat (length l1),fst a)]" by (cases a; simp)

  hence " (\<forall> idx. idx \<ge>0 \<and> idx < length l_pc1 \<longrightarrow> (fst (l_pc1!idx)) <  (length l1))" 
    using b0 a3 l_jump_elem_increases a3 b0 is_increase_list_l_pc_def by blast
  hence b2_1:" (\<forall> idx. idx \<ge>0 \<and> idx < length l_pc1 \<longrightarrow> (fst (l_pc1!idx)) \<noteq>  (length l1))" by fastforce
  hence "\<forall> elem1 elem2. (elem1,elem2) \<in> set l_pc1 \<longrightarrow> elem1 \<noteq> (length l1)" using b2_1
    by (metis bot_nat_0.extremum eq_fst_iff in_set_conv_nth) 
        
  hence "\<forall> elem1. elem1 \<in> set (map fst l_pc1) \<longrightarrow> elem1 \<noteq> (length l1)" by auto
      
  hence "distinct ((map fst l_pc1) @ [of_nat (length l1)])"
    using Cons.prems(2) by auto 
  hence b2:"distinct (map fst l_pc2')" using b2_0 by simp
  have "is_increase_list_l_pc l_pc2' l2'" 
    by (metis a2 a3 b0 l_pc_elem_increases le0 le_imp_less_Suc length_Cons less_Suc0 list.size(3) nth_Cons_0) 
  then show ?case using Cons b2 b0 by (metis Suc_leI le_imp_less_Suc length_Cons less_or_eq_imp_le nth_Cons_Suc) 
 qed


lemma l_pc_index_corr_generic:
  "pc < length l_pc \<Longrightarrow> 
  fst (l_pc!pc) = xpc \<Longrightarrow> 
  distinct (map fst l_pc) \<Longrightarrow>
  is_increase_list_l_pc l_pc l1 \<Longrightarrow> 
  find_target_pc_in_l_pc2 l_pc xpc n = Some (pc+n)"
proof(induct l_pc arbitrary: pc xpc l1 n)
  case Nil
  then show ?case by force
next
  case (Cons a l_pc)
  assume 
  a1:"pc < length (a#l_pc)" and
  a2:"fst ((a#l_pc)!pc) = xpc" and
  a3:"distinct (map fst (a#l_pc))" and
  a4:"is_increase_list_l_pc (a#l_pc) l1"
  have "pc < length l_pc \<Longrightarrow> fst (l_pc ! pc) = xpc \<Longrightarrow> distinct (map fst l_pc) \<Longrightarrow> is_increase_list_l_pc l_pc l1 \<Longrightarrow> find_target_pc_in_l_pc2 l_pc xpc n = Some (pc + n)"
    using Cons by blast
  have b0:"is_increase_list_l_pc l_pc l1" using a4
    by (smt (verit, ccfv_SIG) Suc_leI is_increase_list_l_pc_def le_imp_less_Suc length_Cons less_or_eq_imp_le nth_Cons_Suc) 
  have b1:"distinct (map fst l_pc)" using a3 by fastforce 
  have b2:"pc>0 \<or> pc=0" by blast
  then show ?case 
  proof(cases "pc=0")
    case True
    have b3:"xpc = fst a" using True a2 by simp
    have "find_target_pc_in_l_pc2 (a#l_pc) (fst a) n = Some (pc + n)"
      using True b3 by simp
    then show ?thesis using b3 by blast 
  next
    case False
    have b2_1:"pc>0" using b2 False by blast
    let "?pc" = "pc-1"
    have b3:"fst ((l_pc)!?pc) = xpc" using b2_1 a2 by auto 
    have b4:"?pc <length l_pc" using b2_1 a1 by simp
    have bn:"find_target_pc_in_l_pc2 l_pc xpc n = Some (?pc + n)"
      using b0 b1 b3 b4 Cons.hyps by blast
    have "find_target_pc_in_l_pc2 (a#l_pc) xpc n = Some (pc + n)"
      by (smt (verit, best) Cons.hyps One_nat_def Suc_pred a1 a4 add.commute add_Suc_right b0 b1 b2_1 b3 b4 find_target_pc_in_l_pc2.simps(2) is_increase_list_l_pc_def le0 nat_neq_iff nth_Cons' plus_nat.add_0) 
    then show ?thesis by simp
  qed
qed


lemma l_pc_index_corr:
  "(unat pc) < length l_pc  \<Longrightarrow> 
  fst (l_pc! (unat pc)) = xpc \<Longrightarrow> 
   distinct (map fst l_pc) \<Longrightarrow>
  is_increase_list_l_pc l_pc l1 \<Longrightarrow> 
  find_target_pc_in_l_pc2 l_pc xpc 0 = Some (unat pc)"
  using l_pc_index_corr_generic by auto

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

lemma num_increases:
"find_target_pc_in_l_pc2 xs xpc n = Some num \<Longrightarrow> num \<ge> n"
  apply(induct xs arbitrary: xpc n num)
   apply simp
  by (metis Suc_le_lessD add.commute find_target_pc_in_l_pc2.simps(2) less_or_eq_imp_le option.inject plus_1_eq_Suc)

lemma l_pc_index_corr2_generic:
  "pc < length l_pc \<Longrightarrow> 
  distinct (map fst l_pc) \<Longrightarrow>
  is_increase_list_l_pc l_pc l1 \<Longrightarrow>
  find_target_pc_in_l_pc2 l_pc xpc n = Some (pc+n) \<Longrightarrow> 
  fst (l_pc!pc) = xpc"
proof(induct l_pc arbitrary: pc xpc l1 n)
  case Nil
  then show ?case by force
next
  case (Cons a l_pc)
  assume 
  a1:"pc < length (a#l_pc)" and
  a2:"find_target_pc_in_l_pc2 (a#l_pc) xpc n = Some (pc+n)" and
  a3:"distinct (map fst (a#l_pc))" and
  a4:"is_increase_list_l_pc (a#l_pc) l1"
  have b0:"is_increase_list_l_pc l_pc l1" using a4
    by (smt (verit, ccfv_SIG) Suc_leI is_increase_list_l_pc_def le_imp_less_Suc length_Cons less_or_eq_imp_le nth_Cons_Suc) 
  have b1:"distinct (map fst l_pc)" using a3 by fastforce 
  have "pc < length l_pc \<Longrightarrow> distinct (map fst l_pc) \<Longrightarrow> is_increase_list_l_pc l_pc l1 \<Longrightarrow> find_target_pc_in_l_pc2 l_pc xpc n = Some (pc + n) \<Longrightarrow> fst (l_pc ! pc) = xpc"
    using Cons by simp
  have b2:"pc>0 \<or> pc=0" by blast
  then show ?case
  proof(cases "pc=0")
    case True
    have b3:"find_target_pc_in_l_pc2 (a#l_pc) xpc n = Some n" 
      using True a2 by simp
    have "fst a = xpc" 
    proof(rule ccontr)
      assume assm:"\<not>(fst a = xpc)"
      hence "find_target_pc_in_l_pc2 (a#l_pc) xpc n = find_target_pc_in_l_pc2 l_pc xpc (n+1)" 
        by simp
      hence "find_target_pc_in_l_pc2 (a#l_pc) xpc n \<noteq> Some n" 
        using num_increases by force        
      thus "False" using b3 by auto
    qed
    then show ?thesis by (simp add: True) 
  next
    case False
    have b2_1:"pc>0" using b2 False by blast
    let "?pc" = "pc-1"
    have b3:"fst a \<noteq> xpc"
    proof(rule ccontr)
      assume assm:"\<not> fst a \<noteq> xpc"
      hence "fst a = xpc" by simp
      hence "find_target_pc_in_l_pc2 (a#l_pc) xpc n = Some n" by simp
      thus "False" using False a2 by fastforce 
    qed
    have b4:"find_target_pc_in_l_pc2 l_pc xpc n = Some (?pc+n)" using b3
      by (smt (verit, best) Cons.hyps False a1 a2 add.commute add_Suc_right add_eq_if b0 b1 find_target_pc_in_l_pc2.simps(2) l_pc_index_corr_generic length_Cons linorder_not_less nat_add_left_cancel_le plus_1_eq_Suc) 
    have b4:"?pc <length l_pc" using b2_1 a1 by simp
    have "fst ((a#l_pc)!pc) = xpc"
      using Cons.hyps False b0 b1 b3 b4
      by (smt (verit, best) Cons.prems(2) a1 a2 a4 add_le_same_cancel1 find_target_pc_in_l_pc2.simps(2) l_pc_index_corr_generic not_one_le_zero nth_Cons' num_increases)
    then show ?thesis by simp
  qed
qed



lemma l_pc_index_corr2:
  "pc < length l_pc \<Longrightarrow> 
  distinct (map fst l_pc) \<Longrightarrow>
  is_increase_list_l_pc l_pc l1 \<Longrightarrow>
  find_target_pc_in_l_pc2 l_pc xpc 0 = Some pc \<Longrightarrow> 
  fst (l_pc!pc) = xpc"
  using l_pc_index_corr2_generic by (metis add_cancel_right_right)


end