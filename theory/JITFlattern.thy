theory JITFlattern

imports JITFlattern_def JITFlattern_aux JITFlattern_aux_l_jump JITFlattern_aux_well_formed 
  JITFlattern_prob JITPer
begin

lemma match_state1_prop:
  "xst1 = (exec_instr ins sz xpc1 xrs xm xss) \<Longrightarrow> 
  xst2 = (exec_instr ins sz xpc2 xrs xm xss) \<Longrightarrow>
  xst1 \<noteq> Stuck \<Longrightarrow>
  xst2 \<noteq> Stuck \<Longrightarrow>
  match_state1 xst1 xst2"
(*  apply(unfold exec_instr_def match_state1_def,simp_all)
  apply(cases ins,simp_all)
        apply(unfold exec_ret_def Let_def)
        apply(cases "loadv M64 xm (Vptr sp_block (xrs (IR SP) + u64_of_memory_chunk M64))",simp_all)
  subgoal for a by(cases a,simp_all)
  subgoal for x7 apply(unfold exec_push_def Let_def)
    by(cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR x7)))",simp_all)
  subgoal for x8 apply(unfold exec_pop_def Let_def)
    apply(cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))",simp_all)
    subgoal for a by(cases a,simp_all)
        done
      subgoal for x131 x132 apply(cases "eval_testcond x131 xrs",simp_all)
        done
      subgoal for x151 x152 x153
        apply(unfold exec_store_def,simp_all)
        by(cases "storev x153 xm (Vlong (eval_addrmode64 x151 xrs)) (Vlong (xrs (IR x152)))",simp_all)
      subgoal for x201 x202 x203 
        apply(unfold exec_load_def,simp_all)
        apply(cases "loadv x203 xm (Vlong (eval_addrmode64 x202 xrs))",simp_all)
        subgoal for a by(cases a,simp_all)
            done
          subgoal for x21a 
            apply(unfold exec_call_def Let_def,simp_all)
            by(cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (ucast x21a))",simp_all)
          done*)
  sorry

(*
lemma one_step_equiv_layer1:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, fxst) = fxst'" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xxst) = xxst'" and
   a3:"xxst = Next xpc xrs xm xss" and
   a4:"lt \<noteq> []" and
   a5:"JITFlattern_def.match_state (pc, xxst) (pc, fxst)" and
   a6:"snd xxst' \<noteq> Stuck" and
   a7:"unat pc < length lt \<and> unat pc \<ge> 0" and 
   a8:"well_formed_prog lt" and
   a9:"snd fxst' \<noteq> Stuck" and
   a10:"jitper insns = Some lt "
  shows"JITFlattern_def.match_state xxst' fxst'"
proof-
  have "\<exists> xpc1. fxst = Next xpc1 xrs xm xss" using a3 a5 
    apply(unfold JITFlattern_def.match_state_def match_state1_def) 
    apply(cases fxst,simp_all)
    done
  then obtain xpc1 where a11:"fxst = Next xpc1 xrs xm xss" by auto

  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst (lt!(unat pc))"
  let "?off" = "fst (snd (lt!(unat pc)))"
  let "?l" = "snd (snd (lt!(unat pc)))"
  (*have "\<exists> num off l. (num, off, l) = lt!(unat pc)" using a4 a7 by (metis prod.exhaust_sel) 
  then obtain num off l where b0_0:"(num, off, l) = lt!(unat pc)" by auto*)
  have b0:"(?num, ?off, ?l) = lt!(unat pc)" by simp
 
  let "?xpc" = "fst (l_pc ! (unat pc))"
  have c0:"list_in_list ?l (nat ?xpc) l_bin" 
    using flattern_l_bin0 init_second_layer_def a1 b0 a4 a7 a8 by metis
  let "?prefix" = "take (unat pc) lt"
  let "?suffix" = "drop (unat pc+1) lt"
  have "?prefix@[(?num,?off,?l)]@?suffix= lt" using append_take_drop_id init_second_layer_def
    by (simp add: Cons_nth_drop_Suc a7) 
  hence "?prefix@((?num,?off,?l)#?suffix)= lt" by simp


  have "fxst' = flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, Next xpc1 xrs xm xss)" using a0 a11
    by (metis One_nat_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) old.prod.exhaust) 
  hence c2:"fxst' = (
  if unat pc \<ge> length l_pc \<or> unat pc < 0 then (pc,Stuck) else 
  let num = snd (l_pc!(unat pc)) in 
  let old_xpc = nat (fst (l_pc!(unat pc))) in 
        if xpc1 \<noteq> old_xpc then (pc, Stuck) else 
        case x64_decode xpc1 l_bin of Some(_, Pcall_i _) \<Rightarrow>
         (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
                    rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
                let ss' = update_stack caller fp (pc+1) xss in
                  (case ss' of None \<Rightarrow> (pc, Stuck) | 
                  Some ra \<Rightarrow> (npc, (Next (nat (fst (l_pc!(unat npc)))) rs' xm ra)))))|
        Some(_, Pcmpq_rr src dst) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem num l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, Next xpc1 rs1 m1 ss1)
          ))|
       Some(_,Pret) \<Rightarrow>
          let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc1 rs' xm ss')
          \<comment>\<open> case: NOT BPF JMP \<close>
          \<comment>\<open> case: NOT BPF JMP \<close>|
       _  \<Rightarrow>
          (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))" 
    apply(unfold flat_bpf_one_step_def Let_def) 
    using a3 a11 apply(cases "Next xpc1 xrs xm xss",simp_all)
    subgoal for x11 by force
    done

  have c1:"nat ?xpc= xpc1" using a8 c2 a9 by (smt (verit, ccfv_SIG) snd_conv) 

  have "xxst' = perir_step lt (pc,xxst)" using a2 by (metis One_nat_def perir_sem.simps(1) perir_sem.simps(2) split_pairs)

  hence b1:"xxst' = (let (num,off,l) = lt!(unat pc) in 
       case x64_decode 0 l of
      Some(_,Pret) \<Rightarrow>
          (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss'))|
      Some(_, Pcall_i _) \<Rightarrow>
        (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (off, Next xpc rs' xm ra)))|
      Some(_, Pcmpq_rr src dst) \<Rightarrow>
        (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck))|      
      _ \<Rightarrow>
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          (pc+1, xst'))" using perir_step_def b0 a2 a3 apply(cases xxst,simp_all)
    done

  thus ?thesis
  proof(cases "\<exists> num. x64_decode 0 ?l = Some(num,Pret)")
    case True
    have b3:"xxst' = (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss'))"
      using b1 True b0 apply(cases "x64_decode (0::nat) ?l",simp_all)
      subgoal for a apply(cases "lt ! unat pc",simp_all)
        subgoal for aa b c 
          apply(cases a,simp_all)
          done
        done
      done
   have b2_1:"?l \<noteq> []"  using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
   have "?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 
   hence b2_2:"x64_decode 0 ?l \<noteq> None"  apply(cases "x64_decode 0 ?l",simp_all) using True by force
   hence b2_3:"x64_decode 0 ?l = x64_decode xpc1 l_bin" using b2_2 list_in_list_x64_decode by (metis True add.right_neutral c0 c1) 
   hence b2_4:"\<exists> num. x64_decode xpc1 l_bin = Some(num,Pret)" using b2_3 True by auto
   have b2:"fxst' =  (let (pc', ss', caller,fp) = update_stack2 xss in
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc1 rs' xm ss'))" using b2_4 c2 a9 a7
     apply(cases "x64_decode xpc1 l_bin",simp_all)
     subgoal for a
       apply(split if_splits,simp_all)
       subgoal for num
         apply(unfold Let_def,simp_all)
         apply(split if_splits,simp_all)
         done
       done
     done
    
   have "JITFlattern_def.match_state xxst' fxst'" 
     using  a6 a9 b2 b3 by(unfold JITFlattern_def.match_state_def match_state1_def Let_def update_stack2_def,simp_all) 
    then show ?thesis by simp
  next
    case False
    have b2:"\<not>(\<exists> num. x64_decode 0 ?l = Some(num,Pret))" using False by simp
    then show ?thesis   
    proof(cases "(\<exists> d num. x64_decode 0 ?l = Some(num, Pcall_i d))")
      case True
      have b3:"(\<exists> d num. x64_decode 0 ?l = Some(num, Pcall_i d))" using True by simp
      have b4:"xxst' = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (?off, Next xpc rs' xm ra)))" 
        using True b1 b0 b2 apply(cases "x64_decode 0 ?l",simp_all)
        subgoal for a
          apply(cases "lt ! unat pc",simp_all)
          subgoal for aa b c
            apply(cases a,simp_all)
            subgoal for ab ba apply(cases ba,simp_all)
              subgoal for x21a
                by (metis fst_conv snd_conv) 
              done
            done
          done
        done
              
      have b2_1:"?l \<noteq> []"  using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
      have "?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 
      hence b2_2:"x64_decode 0 ?l \<noteq> None" apply(cases "x64_decode 0 ?l",simp_all) using b3 by force 

      
      (*hence "\<forall> n. \<not> (x64_bin_is_sequential n ?l 0)" using x64_bin_is_sequential_x64_decode_pcall_false by blast*)
      have d3_1:"x64_decode 0 ?l = x64_decode xpc1 l_bin " 
        using list_in_list_x64_decode c0 by (metis add.right_neutral c1 b3) 
      hence d3:"fxst' = (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
                    rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
                let ss' = update_stack caller fp (pc+1) xss in
                  (case ss' of None \<Rightarrow> (pc, Stuck) | 
                  Some ra \<Rightarrow> (npc, (Next (nat (fst (l_pc!(unat npc)))) rs' xm ra)))))"
        using c2 a1 a7 a9 b0 b3 flattern_num split_pairs 
        apply(split if_splits,simp_all) (*by (smt (verit))*) 
        subgoal for d num
          apply(unfold Let_def,simp_all)
          apply(split if_splits,simp_all)
          done
        done
  
      thus ?thesis
        proof(cases "find_target_pc_in_l_pc l_jump (uint pc) \<noteq> None")
          case True
          have "\<exists> npc. find_target_pc_in_l_pc l_jump (uint pc) = Some npc" using True by simp
          then obtain npc where d5_1:"find_target_pc_in_l_pc l_jump (uint pc) = Some npc" by auto
          have d5_2:"distinct (map fst [])" by simp
          have d5_4:"is_increase_list [] []" using is_increase_list_empty by blast 
          hence d5:"npc = ?off" using a1 b0 d5_2 init_second_layer_def a7 b3 d5_4 d5_1 flattern_jump_index_2
            by (smt (verit, ccfv_threshold) int_ops(1) list.size(3)) 

          have d6_0:"fxst' = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
                    rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
                let ss' = update_stack caller fp (pc+1) xss in
                  (case ss' of None \<Rightarrow> (pc, Stuck) | 
                  Some ra \<Rightarrow> (?off, (Next (nat (fst (l_pc!(unat ?off)))) rs' xm ra))))" using d5 d3 d5_1 by auto
          hence d6: "JITFlattern_def.match_state xxst' fxst'" 
            using b4 d5 d3 True JITFlattern_def.match_state_def match_state1_def a9 a6
            by (smt (z3) case_prod_beta' option.case_eq_if outcome.simps(4) prod.collapse prod.inject) 
          then show ?thesis by simp             
        next
          case False
          have "find_target_pc_in_l_pc l_jump (uint pc) = None" using False by simp
           hence "fxst' = (pc,Stuck)" using d3 by simp
          then show ?thesis using a9 by auto
        qed
    next
      case False
      have b5:"(\<not> (\<exists> num. x64_decode 0 ?l = Some(num,Pret))) \<and> (\<not>(\<exists> num d. x64_decode 0 ?l = Some(num, Pcall_i d)))" using False b2 by simp
      hence bn_1:"?l \<noteq> []" using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
      have bn_2:"?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 

      have c3_0:"list_in_list ?l xpc1 l_bin" using c0 c1 by simp         
      have c3:"l_bin!xpc1 = ?l!0" using c3_0 bn_1 by (metis list.collapse list_in_list.simps(2) nth_Cons_0)
      then show ?thesis      
      proof(cases "(\<exists> num src dst. x64_decode 0 ?l = Some(num, Pcmpq_rr src dst))")
        
        case True
        
        hence d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (?off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck) )" using True b1 b0 b5 apply(cases "x64_decode 0 ?l",simp_all)
        subgoal for a
          apply(cases "lt ! unat pc",simp_all)
          subgoal for aa b c
            apply(cases a,simp_all)
            subgoal for ab ba apply(cases ba,simp_all)
              subgoal for x21a
                by (metis fst_conv snd_conv) 
              done
            done
          done
        done
        
        have d1_1:"\<exists> num src dst. x64_decode xpc1 l_bin = Some(num, Pcmpq_rr src dst)" 
          using list_in_list_x64_decode c3_0 True by fastforce 
        hence d1:"fxst' = (case x64_sem (snd (l_pc!(unat pc))) l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, Next xpc1 rs1 m1 ss1)
          )) " using True a0 c2 a7 a9 c1 by auto 
        
        have d4:"(snd (l_pc!(unat pc))) = ?num"
            by (metis (mono_tags, lifting) a1 a7 b0 flattern_num)         
        have "\<exists> fxst1. fxst1 = x64_sem ?num l_bin (Next xpc1 xrs xm xss)" by fastforce
        then obtain fxst1 where d2_0:"fxst1 = x64_sem ?num l_bin (Next xpc1 xrs xm xss)" by auto
        have "\<exists> xxst1. xxst1 = x64_sem ?num ?l (Next 0 xrs xm xss)" by fastforce
        then obtain xxst1 where d2_1:"xxst1 = x64_sem ?num ?l (Next 0 xrs xm xss)" by auto
        have d2_5_1:"xxst1 \<noteq> Stuck" using a6 d1 d2_1 d4 d0 by force
        hence d2_5:"x64_decode 0 ?l \<noteq> None" using d2_1 apply(cases "x64_decode 0 ?l",simp_all)
          by (metis (no_types, lifting) Suc_diff_1 bn_2 option.simps(4) x64_sem.simps(3)) 

        have b7_0:"\<exists> num src dst. x64_decode 0 ?l = Some(num, Pcmpq_rr src dst)" using True bn_1 d2_5 by simp
        have b7:"?num = 1" using a10 b7_0 by (metis a7 b0 jit_prog_prop4)  
        hence d2_2:"fxst1 = (case x64_decode xpc1 l_bin of
          None \<Rightarrow> Stuck |
          Some (sz, ins) \<Rightarrow>
            x64_sem 0 l_bin (exec_instr ins sz xpc1 xrs xm xss)
          )" using d2_0 by simp
        have d2_3_1:"fxst1 \<noteq> Stuck" using a9 d1 d2_0 b0 d4 by auto
        hence d2_3:"x64_decode xpc1 l_bin \<noteq> None" using d2_2 by(cases "x64_decode xpc1 l_bin",simp_all)
        hence d2_4:"fxst1 = (case x64_decode xpc1 l_bin of Some (sz, ins) \<Rightarrow> (exec_instr ins sz xpc1 xrs xm xss))" 
          using d2_2 by force

      
        have d2_6:"xxst1 = (case x64_decode 0 ?l of Some (sz, ins) \<Rightarrow> (exec_instr ins sz 0 xrs xm xss))"
          using b7 d2_1 d2_5 by force 
        
        have d2_7:"x64_decode 0 ?l = x64_decode xpc1 l_bin" using list_in_list_x64_decode d2_3 d2_5 c3_0 by fastforce 
        have "\<exists> sz ins. x64_decode 0 ?l = Some (sz, ins)" using d2_5 by simp
        then obtain sz ins where "x64_decode 0 ?l = Some (sz, ins)" by auto
        hence d2_8:"xxst1 = (exec_instr ins sz 0 xrs xm xss)" using d2_6 by simp
        hence d2_9:"fxst1 =(exec_instr ins sz xpc1 xrs xm xss)" using d2_0 d2_1 d2_6 d2_4 d2_7
          by (metis \<open>x64_decode (0::nat) (snd (snd ((lt::(nat \<times> 64 word \<times> 8 word list) list) ! unat (pc::64 word)))) = Some (sz::nat, ins::instruction)\<close> case_prod_conv option.simps(5)) 
        have d2:"match_state1 fxst1 xxst1" using match_state1_prop d2_3_1 d2_5_1 d2_8 d2_9 by blast
          
          have d3:"\<exists> xpc' xrs1 xm1 xss1. Next xpc' xrs1 xm1 xss1 = fxst1" 
            using d2 match_state1_def by (smt (verit, ccfv_threshold) outcome.exhaust outcome.simps(5)) 
          then obtain xpc' xrs1 xm1 xss1 where d4_0:"Next xpc' xrs1 xm1 xss1 = fxst1" by auto
          have "\<exists> xpc''. Next xpc'' xrs1 xm1 xss1 = xxst1" 
            using d3 match_state1_def d4_0 by (smt (verit, ccfv_SIG) d2 outcome.exhaust outcome.simps(4) outcome.simps(5))
          then obtain xpc'' where d4_1:"Next xpc'' xrs1 xm1 xss1 = xxst1" by auto
          
          thus ?thesis
          proof(cases "xrs1 (CR ZF) = 1")
            case True
            have d5_0: "xrs1 (CR ZF) = 1" using True by auto
            thus ?thesis
            proof(cases "find_target_pc_in_l_pc l_jump (uint pc) \<noteq> None")
              case True
                have "\<exists> npc. find_target_pc_in_l_pc l_jump (uint pc) = Some npc" using True by simp
                then obtain npc where d5_1:"find_target_pc_in_l_pc l_jump (uint pc) = Some npc" by auto
                have d5_2:"distinct (map fst [])" by simp
                have d5_4:"is_increase_list [] []" using is_increase_list_empty by blast 
                hence d5:"npc = ?off+pc" using a1 a4 b0 a7 flattern_jump_index_1 init_second_layer_def d5_2 d5_1 b7_0
                  by (metis (mono_tags, lifting) Abs_fnat_hom_0 add_0 int_ops(1) list.size(3))
                                                 
                have d6_0:"fxst' =  (npc, (Next (nat (fst (l_pc!(unat npc)))) xrs1 xm1 xss1))" 
                  using d5_0 d5_1 True d4_0 d1 d2_0 d4 by (smt (verit, best) option.simps(5) outcome.simps(4))
                have d6_1:"xxst' = (?off+pc, xxst1)"
                  by (smt (verit, ccfv_threshold) d0 d2_1 d4_1 d5_0 outcome.simps(4)) 

                have "JITFlattern_def.match_state fxst' xxst'" 
                  using d6_0 d6_1 JITFlattern_def.match_state_def d4_1 d5 match_state1_def by auto
                then show ?thesis using JITFlattern_def.match_state_def d6_0 d6_1 match_state1_def \<open>\<And>thesis::bool. (\<And>xpc''::nat. Next xpc'' (xrs1::preg \<Rightarrow> 64 word) (xm1::nat \<Rightarrow> int \<Rightarrow> 8 word option) (xss1::stack_state) = (xxst1::outcome) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by fastforce 
               next
                 case False
                 have "find_target_pc_in_l_pc l_jump (uint pc) = None" using False by simp
                 hence "fxst' = (pc,Stuck)" using a9
                   by (smt (verit, ccfv_SIG) d1 d2_0 d4 d4_0 d5_0 option.case_eq_if outcome.simps(4)) 
                then show ?thesis using a9 by auto
              qed
            next
              case False
              have d5_0:"xrs1 (CR ZF) \<noteq> 1" using False by simp
              have d5_1:"xxst' = (pc+1, xxst1)" by (smt (verit) d0 d2_1 d4_1 d5_0 outcome.simps(4)) 
              have d5_2:"fxst' = (pc+1, fxst1)" 
                using d5_0 by (smt (verit, ccfv_threshold) d1 d2_0 d4 d4_0 outcome.simps(4)) 
            then show ?thesis using d5_1 d5_2 JITFlattern_def.match_state_def d2 d3 d4_1 by force 
        qed

      next
        case False
        have b6:"(\<not>(\<exists> num. x64_decode 0 ?l = Some(num,Pret))) \<and> (\<not>(\<exists> num d. x64_decode 0 ?l = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num src dst. x64_decode 0 ?l = Some(num, Pcmpq_rr src dst)))" 
          using b5 False by force 
          have d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          (pc+1, xst'))" using b6 b0 b1 apply(cases "x64_decode 0 ?l",simp_all)
            apply(cases "lt ! unat pc",simp_all)
            subgoal for a apply(cases "lt ! unat pc",simp_all)
              subgoal for aa b c
                apply(cases a,simp_all)
                subgoal for ab ba apply(cases ba,simp_all)
                  done
                done
              done
            done
          hence bn_0:"x64_decode 0 ?l \<noteq> None" using d0 a6 bn_2 apply(cases "x64_decode 0 ?l",simp_all)
            by (smt (verit) Suc_diff_1 option.simps(4) x64_sem.simps(3))
          hence "x64_decode 0 ?l \<noteq> Some(1,Pret) \<and> (\<forall> d. x64_decode 0 ?l \<noteq> Some(5, Pcall_i d)) \<and> (\<forall> src dst. x64_decode 0 ?l \<noteq> Some(3, Pcmpq_rr src dst))"
            using  bn_1 b6 by simp

          have "(\<not>(\<exists> num. x64_decode xpc1 l_bin = Some(num,Pret))) \<and> (\<not>(\<exists> num d. x64_decode xpc1 l_bin = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num src dst. x64_decode xpc1 l_bin = Some(num, Pcmpq_rr src dst)))" 
            using b6 list_in_list_x64_decode bn_0 c3_0 by fastforce
          hence c4:"fxst' = (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))"
            using c2 b6  a1 a7 add.right_neutral c1 init_second_layer_def l_pc_length_prop a9 a9 c2 snd_conv
          apply(cases "x64_decode xpc1 l_bin",simp_all)
            apply(cases "lt ! unat pc",simp_all)
            subgoal for a apply(cases "lt ! unat pc",simp_all)
              subgoal for aa
                apply(split if_splits,simp_all)
                done
              done
            subgoal for a
              apply(split if_splits,simp_all)
                apply(cases a,simp_all)                
                subgoal for aa b apply(cases b,simp_all)
                  done
                done
              done           
           
          have c5_1:"l_pc \<noteq> []"  using a1 a4 apply(unfold init_second_layer_def) using num_corr by fastforce 

          have c5:"fxst' = (pc+1, x64_sem ?num l_bin (Next xpc1 xrs xm xss))"using b0 c5_1 a1 init_second_layer_def c4 a6 a7
            by (metis (mono_tags, lifting) flattern_num)

          hence c6:"x64_bin_is_sequential (length ?l) ?l 0" using a10 x64_bin_is_sequential_x64_decode2 b6 a7 b0 bn_0 by metis
          
          have cn:"match_state1 (snd xxst') (snd fxst')" using c5 d0 c3_0 list_in_list_prop3 c6 a6 a9 by (metis add.right_neutral snd_conv) 
            
          have "fst fxst' = pc+1" using c5 by auto
          moreover have d2:"fst xxst' = pc+1" using d0 by auto
          hence "fst xxst' = fst fxst'" using calculation by presburger 
          hence "JITFlattern_def.match_state xxst' fxst'" using cn JITFlattern_def.match_state_def match_state1_def 
            apply(cases "snd xxst'",simp_all)
            apply(cases "snd fxst'",simp_all)
            by (simp add: case_prod_beta')                    
          then show ?thesis by (simp add: c5 d0) 
        qed
      qed
    qed
  qed
*)
lemma one_step_equiv_layer1:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, fxst) = fxst'" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xxst) = xxst'" and
   a3:"xxst = Next xpc xrs xm xss" and
   a4:"lt \<noteq> []" and
   a5:"JITFlattern_def.match_state (pc, xxst) (pc, fxst)" and
   a6:"snd xxst' \<noteq> Stuck" and
   a7:"unat pc < length lt \<and> unat pc \<ge> 0" and 
   a8:"well_formed_prog lt" and
   a9:"snd fxst' \<noteq> Stuck" and
   a10:"jitper insns = Some lt "
  shows"JITFlattern_def.match_state xxst' fxst'"
proof-
  have "\<exists> xpc1. fxst = Next xpc1 xrs xm xss" using a3 a5 
    apply(unfold JITFlattern_def.match_state_def match_state1_def) 
    apply(cases fxst,simp_all)
    done
  then obtain xpc1 where a11:"fxst = Next xpc1 xrs xm xss" by auto

  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst (lt!(unat pc))"
  let "?off" = "fst (snd (lt!(unat pc)))"
  let "?l" = "snd (snd (lt!(unat pc)))"
  (*have "\<exists> num off l. (num, off, l) = lt!(unat pc)" using a4 a7 by (metis prod.exhaust_sel) 
  then obtain num off l where b0_0:"(num, off, l) = lt!(unat pc)" by auto*)
  have b0:"(?num, ?off, ?l) = lt!(unat pc)" by simp
 
  let "?xpc" = "fst (l_pc ! (unat pc))"
  have c0:"list_in_list ?l (nat ?xpc) l_bin" 
    using flattern_l_bin0 init_second_layer_def a1 b0 a4 a7 a8 by metis
  let "?prefix" = "take (unat pc) lt"
  let "?suffix" = "drop (unat pc+1) lt"
  have "?prefix@[(?num,?off,?l)]@?suffix= lt" using append_take_drop_id init_second_layer_def
    by (simp add: Cons_nth_drop_Suc a7) 
  hence "?prefix@((?num,?off,?l)#?suffix)= lt" by simp


  have "fxst' = flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, Next xpc1 xrs xm xss)" using a0 a11
    by (metis One_nat_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) old.prod.exhaust) 
  hence c2:"fxst' = (
  if unat pc \<ge> length l_pc \<or> unat pc < 0 then (pc,Stuck) else 
  let num = snd (l_pc!(unat pc)) in 
  let old_xpc = nat (fst (l_pc!(unat pc))) in 
        if xpc1 \<noteq> old_xpc then (pc, Stuck) else 
         case x64_decode xpc1 l_bin of Some(sz, Pcall_i _) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> (
                let xst_temp = exec_instr (Pcall_i (of_int(fst (l_pc!(unat npc))))) sz xpc1 xrs xm xss in 
                  (case xst_temp of Stuck \<Rightarrow> (pc, Stuck) | 
                                    Next xpc' rs' m' ss' \<Rightarrow> (npc, (Next xpc' rs' m' ss'))))) |
        Some(sz, Pcmpq_rr src dst) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_decode (xpc1+sz) l_bin of Some (sz2,Pjcc _ _) \<Rightarrow>
          (case x64_sem num l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
          case find_target_pc_in_l_pc l_jump (uint pc) of
                      None \<Rightarrow> (pc, Stuck) |
                      Some npc \<Rightarrow>
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
             (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, Next (xpc1+sz2) rs1 m1 ss1)
          ))|
            _ \<Rightarrow> (pc, Stuck)) |
        Some(sz,Pret_anchor) \<Rightarrow>
          (case x64_decode (xpc1+sz) l_bin of Some (sz2,Pret) \<Rightarrow>
          let (pc', ss', caller,fp) = update_stack2 xss in 
          if find_target_pc_in_l_pc3 l_jump (uint pc) \<noteq> Some (uint pc') then (pc,Stuck) else
          let rs' = restore_x64_caller xrs caller fp in 
          let xst_temp = exec_instr Pret sz2 (xpc1+sz) rs' xm ss' in 
          (case xst_temp of Stuck \<Rightarrow> (pc,Stuck)| Next xpc1 rs1 m1 ss1 \<Rightarrow> 
            (if xpc1 = (nat (fst (l_pc!(unat pc')))+1) then (pc',Next xpc1 rs1 m1 ss1) else (pc,Stuck) ))|
          _ \<Rightarrow> (pc,Stuck)) |
       _  \<Rightarrow>
          (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))" 
    apply(unfold flat_bpf_one_step_def Let_def) 
    using a3 a11 a9 apply(cases "Next xpc1 xrs xm xss",simp_all)
    subgoal for x11 by fastforce     
    done

  have c1:"nat ?xpc= xpc1" using a8 c2 a9 by (smt (verit, ccfv_SIG) snd_conv) 

  have "xxst' = perir_step lt (pc,xxst)" using a2 by (metis One_nat_def perir_sem.simps(1) perir_sem.simps(2) split_pairs)

  hence b1:"xxst' = (let (num,off,l) = lt!(unat pc) in 
       case x64_decode 0 l of 
      Some(_, Pcall_i _) \<Rightarrow> (let xst_temp = Next 0 xrs xm xss in (off, x64_sem 1 l xst_temp))|
      Some(sz, Pret_anchor) \<Rightarrow> (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in 
          let xst_temp = Next sz rs' xm ss' in (pc', x64_sem 1 l xst_temp))|      
      Some(_, Pcmpq_rr src dst) \<Rightarrow> 
        (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem 1 l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck))|      
      _  \<Rightarrow>
        (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          (pc+1, xst')))" 
    using perir_step_def b0 a2 a3 apply(cases xxst,simp_all)
    done

  thus ?thesis
  proof(cases "\<exists> sz. x64_decode 0 ?l = Some(sz,Pret_anchor)")
    case True
    obtain sz where b3_0:"x64_decode 0 ?l = Some(sz,Pret_anchor)" using True by auto
    hence b3:"xxst' = (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in 
          let xst_temp = Next sz rs' xm ss' in (pc', x64_sem 1 ?l xst_temp))"
      using b1 True b0 apply(cases "x64_decode (0::nat) ?l",simp_all)
      apply(cases "lt ! unat pc",simp_all)
      subgoal for a b c 
        apply(cases "x64_decode sz c",simp_all)
        done
        done

   have b2_1:"?l \<noteq> []"  using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
   have "?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 
   hence b2_2:"x64_decode 0 ?l \<noteq> None"  apply(cases "x64_decode 0 ?l",simp_all) using True by force
   hence b2_3:"x64_decode 0 ?l = x64_decode xpc1 l_bin" using b2_2 list_in_list_x64_decode by (metis True add.right_neutral c0 c1) 
   hence b2_4:"\<exists> num. x64_decode xpc1 l_bin = Some(num,Pret_anchor)" using b2_3 True by auto
   hence b2_5:"x64_decode  xpc1 l_bin = Some(sz,Pret_anchor)" using b3 b2_3 b3_0 by argo 
   have b2:"fxst' = (case x64_decode (xpc1+sz) l_bin of Some (sz2,Pret) \<Rightarrow>
          let (pc', ss', caller,fp) = update_stack2 xss in 
          if find_target_pc_in_l_pc3 l_jump (uint pc) \<noteq> Some (uint pc') then (pc,Stuck) else
          let rs' = restore_x64_caller xrs caller fp in 
          let xst_temp = exec_instr Pret sz2 (xpc1+sz) rs' xm ss' in 
          (case xst_temp of Stuck \<Rightarrow> (pc,Stuck)| Next xpc1 rs1 m1 ss1 \<Rightarrow> 
            (if xpc1 = (nat (fst (l_pc!(unat pc')))+1) then (pc',Next xpc1 rs1 m1 ss1) else (pc,Stuck))))" using b2_4 c2 a9 a7 a3
     using b2_5 c2 
     apply(cases "x64_decode xpc1 l_bin",simp_all)
     subgoal for a
       apply(split if_splits,simp_all)
         apply(unfold Let_def,simp_all)
         apply(split if_splits,simp_all)
         apply(cases "x64_decode (nat (fst (l_pc ! unat pc)) + sz) l_bin",simp_all)
         subgoal for aa apply(cases aa,simp_all)
           subgoal for ab b apply(cases b,simp_all)
         done
         done
       done
     done

   have "\<exists> xpc'' xrs'' xm'' xss'' pc'. fxst' = (pc', Next xpc'' xrs'' xm'' xss'')" using a9
     by (metis eq_snd_iff outcome.exhaust) 
   then obtain xpc'' xrs'' xm'' xss'' pc' where b3_0:"fxst' = (pc', Next xpc'' xrs'' xm'' xss'')" by auto
   have b3_1:"Next xpc'' xrs'' xm'' xss'' \<noteq> Stuck" using b3_0 a9 by blast
   hence b4:"\<exists> sz2. x64_decode (xpc1+sz) l_bin = Some (sz2,Pret)" using a9 b2 b3_0 
     apply(cases "x64_decode (xpc1 + sz) l_bin",simp_all) 
     sorry


   then obtain sz2 where "x64_decode (xpc1+sz) l_bin = Some (sz2,Pret)" by auto
   hence b4_1:"fxst' = (let (pc', ss', caller,fp) = update_stack2 xss in 
          if find_target_pc_in_l_pc3 l_jump (uint pc) \<noteq> Some (uint pc') then (pc,Stuck) else
          let rs' = restore_x64_caller xrs caller fp in 
          let xst_temp = exec_instr Pret sz2 (xpc1+sz) rs' xm ss' in 
          (case xst_temp of Stuck \<Rightarrow> (pc,Stuck)| Next xpc1 rs1 m1 ss1 \<Rightarrow> 
            (if xpc1 = (nat (fst (l_pc!(unat pc')))+1) then (pc',Next xpc1 rs1 m1 ss1) else (pc,Stuck))))"
     using b2 apply(cases "update_stack2 xss",simp_all)
        done

   let "?ss'" = "(fst(snd(update_stack2 xss)))"
   let "?rs'" = "(restore_x64_caller xrs (fst(snd(snd(update_stack2 xss)))) (snd(snd(snd(update_stack2 xss)))))"
   let "?pc'" = "fst (update_stack2 xss)"

      have b4_2:"find_target_pc_in_l_pc3 l_jump (uint pc) = Some (uint (?pc'))" using b4_1 a9
       apply(cases "update_stack2 xss",simp_all)
       subgoal for a b c d 
         apply(split if_splits,simp_all)
          done
        done
      have b4_3:"exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' \<noteq> Stuck" 
        using b4_1 b4_2 apply(unfold Let_def,simp_all) apply(cases "update_stack2 xss",simp_all)
        subgoal for a b c d
          using a9 exec_instr_def by force 
        done
      hence "\<exists> xpc1 xrs1 xss1 xm1. exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' = Next xpc1 xrs1 xss1 xm1"
        by (meson outcome.exhaust) 
  (*    then obtain xpc1 xrs1 xss1 xm1 where b4_4:"exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' = Next xpc1 xrs1 xss1 xm1" by auto

          hence c0_6:"Next xpc1 xrs1 xss1 xm1 = Next xpc'' xrs'' xm'' xss''"
          using c0 c0_2 cn c0_3 apply(unfold Let_def,simp_all) 
          by(cases "update_stack2 xss",simp_all)
      
      have c0_4:"exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' = (
          let nsp =  (?rs' (IR SP)) + (u64_of_memory_chunk M64) in
            case Mem.loadv M64 xm (Vptr sp_block nsp) of
            None \<Rightarrow> Stuck |
            Some ra \<Rightarrow> (
              case ra of
              Vlong v \<Rightarrow> let rs1 = ?rs'#(IR SP) <- nsp in
                          Next (unat v) rs1 xm ?ss' |
              _ \<Rightarrow> Stuck)
        )" using exec_instr_def by (simp add: exec_ret_def) 

      hence "\<exists> v. Mem.loadv M64 xm (Vptr sp_block ((?rs' (IR SP)) + (u64_of_memory_chunk M64))) = Some (Vlong v)"
        using c0_3 c0_2
        by (smt (verit, ccfv_SIG) option.case_eq_if option.collapse val.case(1) val.case(2) val.case(3) val.case(4) val.case(6) val.exhaust) 

      then obtain v where c0_5:"Mem.loadv M64 xm (Vptr sp_block ((?rs' (IR SP)) + (u64_of_memory_chunk M64))) = Some (Vlong v)" by auto
      
      hence c0_7:"exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' = Next (unat v) (?rs'#(IR SP) <- ((?rs' (IR SP)) + (u64_of_memory_chunk M64))) xm ?ss'" 
        using c0_4 Let_def by simp
      hence c1:"snd fxst' = Next (unat v) (?rs'#(IR SP) <- ((?rs' (IR SP)) + (u64_of_memory_chunk M64))) xm ?ss'" 
        using c0_6 c0_3 a1 by argo 
*)
   have "JITFlattern_def.match_state xxst' fxst'" 
     using  a6 a9 b2 b3 by(unfold JITFlattern_def.match_state_def match_state1_def Let_def update_stack2_def,simp_all) 
    then show ?thesis by simp
  next
    case False
    have b2:"\<not>(\<exists> num. x64_decode 0 ?l = Some(num,Pret_anchor))" using False by simp

    then show ?thesis   
    proof(cases "(\<exists> d num. x64_decode 0 ?l = Some(num, Pcall_i d))")
      case True
      have b3:"(\<exists> d num. x64_decode 0 ?l = Some(num, Pcall_i d))" using True by simp
      then obtain sz d where b3_0:"x64_decode 0 ?l = Some(sz, Pcall_i d)" by auto
      have b4:"xxst' = (?off, (x64_sem 1 ?l (Next 0 xrs xm xss)))" 
        using True b1 b0 b2 apply(cases "x64_decode 0 ?l",simp_all)
        subgoal for a
          apply(cases "lt ! unat pc",simp_all)
          subgoal for aa b c
            apply(cases a,simp_all)
            subgoal for ab ba apply(cases ba,simp_all)
              done
            done
          done
        done
              
      have b2_1:"?l \<noteq> []"  using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
      have "?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 
      hence b2_2:"x64_decode 0 ?l \<noteq> None" apply(cases "x64_decode 0 ?l",simp_all) using b3 by force 

      
      (*hence "\<forall> n. \<not> (x64_bin_is_sequential n ?l 0)" using x64_bin_is_sequential_x64_decode_pcall_false by blast*)
      have d3_1:"x64_decode 0 ?l = x64_decode xpc1 l_bin " 
        using list_in_list_x64_decode c0 by (metis add.right_neutral c1 b3) 

      have d3_2:"x64_decode xpc1 l_bin = Some(sz, Pcall_i d)"
        using b3_0 d3_1 by auto 

      hence d3:"fxst' =  (case x64_decode (xpc1+sz) l_bin of Some (sz2,Pjcc _ _) \<Rightarrow>
            (case x64_sem ?num l_bin (Next xpc1 xrs xm xss) of
            Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
            Next xpc' rs1 m1 ss1 \<Rightarrow> (
              case find_target_pc_in_l_pc l_jump (uint pc) of
                None \<Rightarrow> (pc, Stuck) |
                Some npc \<Rightarrow>
              if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
                ((npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
              else \<comment>\<open> donot JUMP \<close>
                (pc+1, (Next (xpc'+sz2) rs1 m1 ss1))
            )))"
        using d3_2 a9 c2 a7 a3 a11 c1 apply(split if_splits,simp_all) sorry
        

      thus ?thesis
        proof(cases "find_target_pc_in_l_pc l_jump (uint pc) \<noteq> None")
          case True
          have "\<exists> npc. find_target_pc_in_l_pc l_jump (uint pc) = Some npc" using True by simp
          then obtain npc where d5_1:"find_target_pc_in_l_pc l_jump (uint pc) = Some npc" by auto
          have d5_2:"distinct (map fst [])" by simp
          have d5_4:"is_increase_list [] []" using is_increase_list_empty by blast 
          hence d5:"npc = ?off" using a1 b0 d5_2 init_second_layer_def a7 b3 d5_4 d5_1 flattern_jump_index_2
            by (smt (verit, ccfv_threshold) int_ops(1) list.size(3)) 

          have d6_0:"fxst' = (case x64_sem 1 l_bin fxst of  Next xpc' rs' m' ss' \<Rightarrow> (?off, (x64_sem 1 l_bin (Next (nat (fst (l_pc!(unat npc)))) rs' m' ss'))) )" using d5 d3 d5_1 sorry

          hence d6: "JITFlattern_def.match_state xxst' fxst'" 
            using b4 d5 d3 True JITFlattern_def.match_state_def match_state1_def a9 a6 sorry
          then show ?thesis by simp             
        next
          case False
          have "find_target_pc_in_l_pc l_jump (uint pc) = None" using False by simp
           hence "fxst' = (pc,Stuck)" using d3 by simp
          then show ?thesis using a9 by auto
        qed
    next
      case False
      have b5:"(\<not> (\<exists> num. x64_decode 0 ?l = Some(num,Pret_anchor))) \<and> (\<not>(\<exists> num d. x64_decode 0 ?l = Some(num, Pcall_i d)))" using False b2 by simp
      hence bn_1:"?l \<noteq> []" using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast
      have bn_2:"?num >0 " using a8 apply(unfold well_formed_prog_def) using b0 a4 a7 by blast 

      have c3_0:"list_in_list ?l xpc1 l_bin" using c0 c1 by simp         
      have c3:"l_bin!xpc1 = ?l!0" using c3_0 bn_1 by (metis list.collapse list_in_list.simps(2) nth_Cons_0)
      then show ?thesis      
      proof(cases "(\<exists> num src dst. x64_decode 0 ?l = Some(num, Pcmpq_rr src dst))")
        
        case True
        
        hence d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem 1 ?l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (?off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck) )" using True b1 b0 b5 apply(cases "x64_decode 0 ?l",simp_all)
        subgoal for a
          apply(cases "lt ! unat pc",simp_all)
          subgoal for aa b c
            apply(cases a,simp_all)
            subgoal for ab ba apply(cases ba,simp_all)
              subgoal for x21a
                by (metis fst_conv snd_conv) 
              done
            done
          done
        done
        
       have d1_1:"\<exists> sz src dst. x64_decode xpc1 l_bin = Some(sz, Pcmpq_rr src dst)" 
          using list_in_list_x64_decode c3_0 True by fastforce 
        then obtain sz src dst where d1_0:"x64_decode xpc1 l_bin = Some(sz, Pcmpq_rr src dst)" by auto
        hence d1:"fxst' = (case x64_decode (xpc1+sz) l_bin of Some (sz2,Pjcc _ _) \<Rightarrow>
          (case x64_sem (snd (l_pc!(unat pc))) l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
          case find_target_pc_in_l_pc l_jump (uint pc) of
                      None \<Rightarrow> (pc, Stuck) |
                      Some npc \<Rightarrow>
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
             (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, Next (xpc1+sz2) rs1 m1 ss1)
          ))|
            _ \<Rightarrow> (pc, Stuck))" using True a0 c2 a7 a9 c1 by auto 
        hence d1_2:"\<exists> sz2 cond d. x64_decode (xpc1+sz) l_bin = Some (sz2,Pjcc cond d)" 
          using a9 apply(cases "x64_decode (xpc1+sz) l_bin",simp_all)
          subgoal for a apply(cases a,simp_all)
            subgoal for aa b by(cases b,simp_all)
            done
          done
        then obtain sz2 cond d where d1_3:"x64_decode (xpc1+sz) l_bin = Some (sz2,Pjcc cond d)" by auto

        have d4:"(snd (l_pc!(unat pc))) = ?num"
          by (metis (mono_tags, lifting) a1 a7 b0 flattern_num)      
        have b7_0:"\<exists> num src dst. x64_decode 0 ?l = Some(num, Pcmpq_rr src dst)" using True bn_1 by simp
        have b7:"?num = 1" using a10 b7_0 by (metis a7 b0 jit_prog_prop4)  

        have "\<exists> fxst1. fxst1 = x64_sem 1 l_bin (Next xpc1 xrs xm xss)" by fastforce
        then obtain fxst1 where d2_0:"fxst1 = x64_sem 1 l_bin (Next xpc1 xrs xm xss)" by auto
        have "\<exists> xxst1. xxst1 = x64_sem 1 ?l (Next 0 xrs xm xss)" by fastforce
        then obtain xxst1 where d2_1:"xxst1 = x64_sem 1 ?l (Next 0 xrs xm xss)" by auto
        have d2_5_1:"xxst1 \<noteq> Stuck" using a6 d1 d2_1 d4 d0 by force
        hence d2_5:"x64_decode 0 ?l \<noteq> None" using d2_1 by(cases "x64_decode 0 ?l",simp_all)
                
        hence d2_2:"fxst1 = (case x64_decode xpc1 l_bin of
          None \<Rightarrow> Stuck |
          Some (sz, ins) \<Rightarrow>
            x64_sem 0 l_bin (exec_instr ins sz xpc1 xrs xm xss)
          )" using d2_0 by simp
        have d2_3_1:"fxst1 \<noteq> Stuck" using a9 d1 d2_0 b0 d4 d1_2 d1_3 b7 d1_0 sorry
        hence d2_3:"x64_decode xpc1 l_bin \<noteq> None" using d2_2 by(cases "x64_decode xpc1 l_bin",simp_all)
        hence d2_4:"fxst1 = (case x64_decode xpc1 l_bin of Some (sz, ins) \<Rightarrow> (exec_instr ins sz xpc1 xrs xm xss))" 
          using d2_2 by force

      
        have d2_6:"xxst1 = (case x64_decode 0 ?l of Some (sz, ins) \<Rightarrow> (exec_instr ins sz 0 xrs xm xss))"
          using b7 d2_1 d2_5 by force 
        
        have d2_7:"x64_decode 0 ?l = x64_decode xpc1 l_bin" using list_in_list_x64_decode d2_3 d2_5 c3_0 by fastforce 
        have "\<exists> sz ins. x64_decode 0 ?l = Some (sz, ins)" using d2_5 by simp
        then obtain sz ins where "x64_decode 0 ?l = Some (sz, ins)" by auto
        hence d2_8:"xxst1 = (exec_instr ins sz 0 xrs xm xss)" using d2_6 by simp
        hence d2_9:"fxst1 =(exec_instr ins sz xpc1 xrs xm xss)" using d2_0 d2_1 d2_6 d2_4 d2_7
          by (metis \<open>x64_decode (0::nat) (snd (snd ((lt::(nat \<times> 64 word \<times> 8 word list) list) ! unat (pc::64 word)))) = Some (sz::nat, ins::instruction)\<close> case_prod_conv option.simps(5)) 
        have d2:"match_state1 fxst1 xxst1" using match_state1_prop d2_3_1 d2_5_1 d2_8 d2_9 by blast
          
          have d3:"\<exists> xpc' xrs1 xm1 xss1. Next xpc' xrs1 xm1 xss1 = fxst1" 
            using d2 match_state1_def by (smt (verit, ccfv_threshold) outcome.exhaust outcome.simps(5)) 
          then obtain xpc' xrs1 xm1 xss1 where d4_0:"Next xpc' xrs1 xm1 xss1 = fxst1" by auto
          have "\<exists> xpc''. Next xpc'' xrs1 xm1 xss1 = xxst1" 
            using d3 match_state1_def d4_0 by (smt (verit, ccfv_SIG) d2 outcome.exhaust outcome.simps(4) outcome.simps(5))
          then obtain xpc'' where d4_1:"Next xpc'' xrs1 xm1 xss1 = xxst1" by auto
          
          thus ?thesis
          proof(cases "xrs1 (CR ZF) = 1")
            case True
            have d5_0: "xrs1 (CR ZF) = 1" using True by auto
            thus ?thesis
            proof(cases "find_target_pc_in_l_pc l_jump (uint pc) \<noteq> None")
              case True
                have "\<exists> npc. find_target_pc_in_l_pc l_jump (uint pc) = Some npc" using True by simp
                then obtain npc where d5_1:"find_target_pc_in_l_pc l_jump (uint pc) = Some npc" by auto
                have d5_2:"distinct (map fst [])" by simp
                have d5_4:"is_increase_list [] []" using is_increase_list_empty by blast 
                hence d5:"npc = ?off+pc" using a1 a4 b0 a7 flattern_jump_index_1 init_second_layer_def d5_2 d5_1 b7_0
                  by (metis (mono_tags, lifting) Abs_fnat_hom_0 add_0 int_ops(1) list.size(3))
                                                 
                have d6_0:"fxst' =  (npc, (Next (nat (fst (l_pc!(unat npc)))) xrs1 xm1 xss1))" 
                  using d5_0 d5_1 True d4_0 d1 d2_0 d4 d1_2 sorry
                have d6_1:"xxst' = (?off+pc, xxst1)"
                  by (smt (verit, ccfv_threshold) d0 d2_1 d4_1 d5_0 outcome.simps(4)) 

                have "JITFlattern_def.match_state fxst' xxst'" 
                  using d6_0 d6_1 JITFlattern_def.match_state_def d4_1 d5 match_state1_def by auto
                then show ?thesis using JITFlattern_def.match_state_def d6_0 d6_1 match_state1_def \<open>\<And>thesis::bool. (\<And>xpc''::nat. Next xpc'' (xrs1::preg \<Rightarrow> 64 word) (xm1::nat \<Rightarrow> int \<Rightarrow> 8 word option) (xss1::stack_state) = (xxst1::outcome) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by fastforce 
               next
                 case False
                 have "find_target_pc_in_l_pc l_jump (uint pc) = None" using False by simp
                 hence "fxst' = (pc,Stuck)" using a9 d1 d2_0 d4 d4_0 d5_0 d1_2 sorry
                   
                then show ?thesis using a9 by auto
              qed
            next
              case False
              have d5_0:"xrs1 (CR ZF) \<noteq> 1" using False by simp
              have d5_1:"xxst' = (pc+1, xxst1)" by (smt (verit) d0 d2_1 d4_1 d5_0 outcome.simps(4)) 
              have d5_2:"fxst' = (pc+1, fxst1)" 
                using d5_0 d1 d2_0 d4 d4_0 d1_2 sorry
            then show ?thesis using d5_1 d5_2 JITFlattern_def.match_state_def d2 d3 d4_1 by force 
        qed

      next
        case False
        have b6:"(\<not>(\<exists> num. x64_decode 0 ?l = Some(num,Pret_anchor))) \<and> (\<not>(\<exists> num d. x64_decode 0 ?l = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num src dst. x64_decode 0 ?l = Some(num, Pcmpq_rr src dst)))" 
          using b5 False by force 
          have d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          (pc+1, xst'))" using b6 b0 b1 apply(cases "x64_decode 0 ?l",simp_all)
            apply(cases "lt ! unat pc",simp_all)
            subgoal for a apply(cases "lt ! unat pc",simp_all)
              subgoal for aa b c
                apply(cases a,simp_all)
                subgoal for ab ba apply(cases ba,simp_all)
                  done
                done
              done
            done
          hence bn_0:"x64_decode 0 ?l \<noteq> None" using d0 a6 bn_2 apply(cases "x64_decode 0 ?l",simp_all)
            by (smt (verit) Suc_diff_1 option.simps(4) x64_sem.simps(3))
          hence "x64_decode 0 ?l \<noteq> Some(1,Pret_anchor) \<and> (\<forall> d. x64_decode 0 ?l \<noteq> Some(5, Pcall_i d)) \<and> (\<forall> src dst. x64_decode 0 ?l \<noteq> Some(3, Pcmpq_rr src dst))"
            using  bn_1 b6 by simp

          have "(\<not>(\<exists> num. x64_decode xpc1 l_bin = Some(num,Pret_anchor))) \<and> (\<not>(\<exists> num d. x64_decode xpc1 l_bin = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num src dst. x64_decode xpc1 l_bin = Some(num, Pcmpq_rr src dst)))" 
            using b6 list_in_list_x64_decode bn_0 c3_0 by fastforce
          hence c4:"fxst' = (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))"
            using c2 b6  a1 a7 add.right_neutral c1 init_second_layer_def l_pc_length_prop a9 a9 c2 snd_conv
          apply(cases "x64_decode xpc1 l_bin",simp_all)
            apply(cases "lt ! unat pc",simp_all)
            subgoal for a apply(cases "lt ! unat pc",simp_all)
              subgoal for aa
                apply(split if_splits,simp_all)
                done
              done
            subgoal for a
              apply(split if_splits,simp_all)
                apply(cases a,simp_all)                
                subgoal for aa b apply(cases b,simp_all)
                  done
                done
              done           
           
          have c5_1:"l_pc \<noteq> []"  using a1 a4 apply(unfold init_second_layer_def) using num_corr by fastforce 

          have c5:"fxst' = (pc+1, x64_sem ?num l_bin (Next xpc1 xrs xm xss))"using b0 c5_1 a1 init_second_layer_def c4 a6 a7
            by (metis (mono_tags, lifting) flattern_num)

          hence c6:"x64_bin_is_sequential (length ?l) ?l 0" using a10 x64_bin_is_sequential_x64_decode2 b6 a7 b0 bn_0 by metis
          
          have cn:"match_state1 (snd xxst') (snd fxst')" using c5 d0 c3_0 list_in_list_prop3 c6 a6 a9 by (metis add.right_neutral snd_conv) 
            
          have "fst fxst' = pc+1" using c5 by auto
          moreover have d2:"fst xxst' = pc+1" using d0 by auto
          hence "fst xxst' = fst fxst'" using calculation by presburger 
          hence "JITFlattern_def.match_state xxst' fxst'" using cn JITFlattern_def.match_state_def match_state1_def match_mem_def
            apply(cases "snd xxst'",simp_all)
            apply(cases "snd fxst'",simp_all)
            by (simp add: case_prod_beta')                    
          then show ?thesis by (simp add: c5 d0) 
        qed
      qed
    qed
  qed

lemma flat_bpf_sem_induct_aux1:
 "flat_bpf_sem (m+n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem m x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
 apply(induct m arbitrary: n x64_prog xst xst' )
   apply auto[1]
  subgoal for m n x64_prog xst xst'
    apply (simp add: Let_def)
    apply(cases xst;simp)
    done
  done

lemma flat_bpf_sem_induct_aux2:
"flat_bpf_sem (Suc n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem 1 x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
  using flat_bpf_sem_induct_aux1 by simp


lemma err_is_still_err:"perir_sem n lt (pc,Stuck) = (pc',s') \<Longrightarrow> s' = Stuck "
  apply(induct n, simp)
  using perir_step_def
  by auto

lemma intermediate_step_is_ok:"perir_sem n lt (pc,s) = s' \<Longrightarrow> n \<ge> 0 \<Longrightarrow> snd s' \<noteq> Stuck \<Longrightarrow> 
  \<exists> xpc xrs xm xss. s = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: lt pc s s')
  apply simp 
  using err_is_still_err
  apply (meson outcome.exhaust)
  by (metis JITFlattern.err_is_still_err outcome.exhaust prod.collapse) 


lemma n_steps_equiv_layer1:
  "flat_bpf_sem n prog (pc,fxst) = fxst' \<Longrightarrow>
  jitflat_bpf lt init_second_layer = prog \<Longrightarrow>
  perir_sem n lt (pc,xxst) = xxst' \<Longrightarrow>
  xxst = Next xpc xrs xm xss \<Longrightarrow>
  snd xxst' = Next xpc' xrs' xm' xss' \<Longrightarrow>
  JITFlattern_def.match_state (pc,xxst) (pc,fxst) \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow> 
  well_formed_prog lt \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitper insns = Some lt \<Longrightarrow>
  JITFlattern_def.match_state xxst' fxst'"
proof(induct n arbitrary: prog pc fxst fxst' lt xxst xxst' xpc xrs xm xss xxst' xpc' xrs' xm' xss' xpc'' xrs'' xm'' xss'' insns)
  case 0
  then show ?case apply(unfold JITFlattern_def.match_state_def,simp_all) 
    done
    
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) prog (pc,fxst) = fxst'" and 
  assm1:"jitflat_bpf lt init_second_layer = prog" and
  assm2:"perir_sem (Suc n) lt (pc,xxst) = xxst'" and
  assm3:"xxst = Next xpc xrs xm xss" and
  assm4:"snd xxst' = Next xpc' xrs' xm' xss'" and
  assm5:"lt \<noteq> []" and
  assm6:"JITFlattern_def.match_state (pc,xxst) (pc,fxst)" and
(*  assm7:"unat pc < length lt \<and> unat pc \<ge> 0" and*)
  assm7:"well_formed_prog lt" and
  assm8:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and
  assm9:"jitper insns = Some lt"
 
  have "\<exists> next_s. next_s = perir_sem 1 lt (pc,xxst)" by simp
  then obtain next_s pc' where b0:"next_s = perir_sem 1 lt (pc,xxst)" by auto
  have "\<exists> next_f. flat_bpf_sem 1 prog (pc,fxst) = next_f" by blast
  then obtain next_f where b1:"flat_bpf_sem 1 prog (pc,fxst) = next_f" by simp
  have a0:"perir_sem n lt next_s = xxst'" using x64_sem1_induct_aux3 assm2 b0
    using Suc.prems(3) by presburger 
  have "\<exists> pc' xrs1 xpc1 m1 xss1. (pc', Next xrs1 xpc1 m1 xss1) = next_s" using assm4 a0 intermediate_step_is_ok
    by (metis outcome.exhaust prod.collapse zero_le) 
  then obtain pc' xrs1 xpc1 m1 xss1 where a1:"(pc', Next xrs1 xpc1 m1 xss1) = next_s" by auto
                                                                                                            
  have c0_1:"snd next_f \<noteq> Stuck" using assm8 intermediate_step_is_ok3 b1
    by (metis assm0 bot_nat_0.extremum flat_bpf_sem_induct_aux2 outcome.distinct(1) prod.exhaust_sel) 

  have c0_2:"\<exists> xpc1 xrs xm xss. Next xpc1 xrs xm xss = fxst" 
    using assm6 assm3 JITFlattern_def.match_state_def apply(cases xxst,simp_all) 
    subgoal for x11 by(cases fxst,simp_all) done
  have c0_3:"(unat pc < length (fst(snd prog)) \<and> unat pc \<ge> 0)" 
  proof(rule ccontr)
    assume assm:"\<not> (unat pc < length (fst(snd prog)) \<and> unat pc \<ge> 0)"
    have "snd next_f = snd (let pair = flat_bpf_one_step prog (pc, fxst) in
    flat_bpf_sem 0 prog pair)" using b1 by auto 
    hence "snd next_f = snd (flat_bpf_one_step prog (pc, fxst))"
      by (metis flat_bpf_sem.simps(1) prod.collapse) 
    hence "snd next_f = Stuck" 
      using flat_bpf_one_step_def c0_2 assm apply(cases fxst,simp_all)
      subgoal for x11 x12 x13 x14 by(cases prog,simp_all) done
    thus "False" using c0_1 by blast
  qed

  hence c0:"(unat pc < length lt \<and> unat pc \<ge> 0)" using l_pc_length_prop init_second_layer_def assm1
    by (metis add.right_neutral list.size(3) prod.collapse) 
  have bn:"JITFlattern_def.match_state next_s next_f"
    using one_step_equiv_layer1 b1 assm1 b0 assm3 assm5 assm6 a1 c0 assm8 c0_1 assm7 assm9
    by (metis outcome.distinct(1) prod.collapse snd_conv) 

  have a2:"(pc', snd next_f) = next_f" using bn JITFlattern_def.match_state_def a1 b0 b1
    apply(cases "Next xrs1 xpc1 m1 xss1",simp_all)
    apply(cases "snd next_f",simp_all)
    subgoal for x11 x11a x12 x13 x14 by force
    subgoal for x11 by force
    done

  have c1:"flat_bpf_sem n prog next_f = fxst'" using flat_bpf_sem_induct_aux2 assm0 b1 by blast

  hence "JITFlattern_def.match_state xxst' fxst'" 
    using a0 a1 a2 Suc bn c1 assm5 assm4 by metis
  then show ?case by blast
qed

end