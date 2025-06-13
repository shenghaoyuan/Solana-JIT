theory JITFix_aux
  imports JITFlattern JITFix_prob JITFix_def
begin


lemma err_is_still_err4:"fix_bpf_sem n lp Stuck = s'\<Longrightarrow> s' = Stuck "
  apply(induct n, simp)
  subgoal for a using fix_bpf_one_step_def by auto
  done
   
lemma intermediate_step_is_ok4:
  "fix_bpf_sem n lp s = s' \<Longrightarrow> n \<ge> 0 \<Longrightarrow> s' \<noteq> Stuck \<Longrightarrow> 
  \<exists> xpc xrs xm xss. s = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: lp s s')
  apply simp 
  apply (meson outcome.exhaust)
  using err_is_still_err4
  by (metis outcome.exhaust) 


lemma length_of_decoded_instr1:
  "x64_decode pc l = Some(sz, Pcmpq_rr src dst) \<Longrightarrow> 
  sz = 3"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)+
   apply (cases "u32_of_u8_list [l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat)), l ! (pc + (5::nat))]",simp_all)
  subgoal for a apply(cases "cond_of_u8 (and (15::8 word) (l ! Suc pc))",simp_all)
    done
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
    apply(cases "l ! pc = (232::8 word)";simp)
    apply(cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]";simp)
    done
  apply (cases "l ! pc = (15::8 word)"; simp add: Let_def)
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (10::8 word)"; simp)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      done
    done
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (11::8 word)"; simp add: Let_def)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      done
    done
  apply (cases "l ! Suc pc = 1"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    subgoal for dst
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
      subgoal for src
        apply (cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
        done
      done
    done
  apply (cases "l ! Suc pc = (247::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word) \<and> and (7::8 word) (l ! Suc (Suc pc) >> (3::nat)) = (4::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    subgoal for a apply(cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc (0::nat))",simp_all)
      done
    done

    apply (cases "l ! Suc pc = (57::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    subgoal for a aa apply(cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc (0::nat))",simp_all)
      done
    done
    
  apply (cases "l ! Suc pc = (137::8 word)"; simp)
  apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
  subgoal for a aa apply(cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc (0::nat))",simp_all)
    done
  done

lemma length_of_decoded_instr2:
  "x64_decode pc l = Some(sz, Pjcc cond d) \<Longrightarrow> 
  sz = 6"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)+
   apply (cases "u32_of_u8_list [l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat)), l ! (pc + (5::nat))]",simp_all)
  subgoal for a apply(cases "cond_of_u8 (and (15::8 word) (l ! Suc pc))",simp_all)
    done
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
    apply(cases "l ! pc = (232::8 word)";simp)
    apply(cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]";simp)
    done
  apply (cases "l ! pc = (15::8 word)"; simp add: Let_def)
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (10::8 word)"; simp)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      done
    done
  apply (cases "and (31::8 word) (l ! Suc pc >> (3::nat)) = (11::8 word)"; simp add: Let_def)
  subgoal
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc pc)) (and 1 (l ! pc)))"; simp)
    subgoal for dst
      apply (cases "\<not> bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
      done
    done
  apply (cases "l ! Suc pc = 1"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    subgoal for dst
      apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
      subgoal for src
        apply (cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc 0)"; simp)
        done
      done
    done
  apply (cases "l ! Suc pc = (247::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word) \<and> and (7::8 word) (l ! Suc (Suc pc) >> (3::nat)) = (4::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    subgoal for a apply(cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (2::nat) \<and> \<not> bit (l ! pc) (Suc (0::nat))",simp_all)
      done
    done

    apply (cases "l ! Suc pc = (57::8 word)"; simp)
  subgoal
    apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
    apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
    subgoal for a aa apply(cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc (0::nat))",simp_all)
      done
    done
    
  apply (cases "l ! Suc pc = (137::8 word)"; simp)
  apply (cases "and (3::8 word) (l ! Suc (Suc pc) >> (6::nat)) = (3::8 word)"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc) >> (3::nat))) (and 1 (l ! pc >> (2::nat))))"; simp)
  apply (cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc 0) (and (7::8 word) (l ! Suc (Suc pc))) (and 1 (l ! pc)))"; simp)
  subgoal for a aa apply(cases "bit (l ! pc) (3::nat) \<and> \<not> bit (l ! pc) (Suc (0::nat))",simp_all)
    done
  done


lemma " x = 100 \<Longrightarrow> of_nat(unat x) = x"
  by (metis of_nat_unat ucast_id)

lemma " x = 100 \<Longrightarrow> unat((of_nat x)::u64)= x"
  by simp

lemma hhh:" (let nsp::64 word = xrs (IR SP) - u64_of_memory_chunk M64 in case storev M64 xm (Vptr sp_block nsp) (Vlong (word_of_nat xpc + (1::64 word))) of None \<Rightarrow> Stuck | Some (m'::nat \<Rightarrow> int \<Rightarrow> 8 word option) \<Rightarrow> let rs1::preg \<Rightarrow> 64 word = xrs(IR SP := nsp) in Next (unat n) rs1 m' xss)= exec_call xpc sz M64 xm xss xrs n"
  apply(unfold exec_call_def)
  by blast

lemma one_steps_equiv_layer2:
  assumes a0:"flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = fxst'" and 
    a1:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and 
    a2:"jitper insns = Some lt" and 
    a3:"xst = Next xpc xrs xm xss" and     
    a4:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and 
    a5:"well_formed_prog lt" and     
    a6:"unat pc < length lt \<and> unat pc \<ge> 0"
    shows "\<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')"
proof-
  have "snd fxst' =  snd (let pair = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst) in flat_bpf_sem 0 (l_bin0,l_pc,l_jump) pair)"
            using a0 by simp
  hence b0_1:"snd fxst' =  snd (flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst))" by (metis flat_bpf_sem.simps(1) prod.collapse)
  have b0_3:"unat pc < length l_pc" using l_pc_length_prop a4 init_second_layer_def
    by (metis Nat.add_0_right a6 list.size(3)) 
  have "fxst' = (let pair = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst) in flat_bpf_sem 0 (l_bin0,l_pc,l_jump) pair)" using a0 by simp
  hence b0_2:"fst (l_pc!(unat pc)) = xpc" using a1 b0_3 a3 apply(unfold flat_bpf_one_step_def Let_def,simp_all) by(split if_splits,simp_all)   

  thus ?thesis 

 proof(cases "\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)")
   case True
      have c0_0:"\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)" using True by simp
      then obtain sz src dst where c0_1:"x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)" by auto
      hence c0_2:"sz = 3" using length_of_decoded_instr1 by simp
      (*have "\<exists> l. list_in_list l xpc l_bin0 \<and> x64_decode 0 l = Some(sz, Pcmpq_rr src dst)" using c0_1 sorry
      then obtain l where c0_3:"list_in_list l xpc l_bin0 \<and> x64_decode 0 l = Some(sz, Pcmpq_rr src dst)" by auto*)
      have c0:"snd fxst' = snd (let num = snd (l_pc!(unat pc)) in 
        (case x64_decode (xpc+sz) l_bin0 of Some (sz2,Pjcc cond _) \<Rightarrow>
         (if num = 1 then case x64_sem num l_bin0 (Next xpc xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> 
         (case find_target_pc_in_l_pc l_jump (unat pc) of
                      None \<Rightarrow> (pc, Stuck) |
                      Some npc \<Rightarrow>
            if eval_testcond cond rs1 then \<comment>\<open> must JUMP \<close>            
                ((npc, (Next (fst (l_pc!(unat npc))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, (Next (xpc1+sz2) rs1 m1 ss1))
           )else (pc, Stuck))|
            _ \<Rightarrow> (pc, Stuck)))" using True a0 b0_1 a3 a6 b0_3 a1 c0_1
        apply(unfold flat_bpf_one_step_def Let_def,simp_all) 
        apply(cases "x64_decode xpc l_bin0",simp_all)
        subgoal for a by(split if_splits,simp_all)
        done

      let "?num" = "(snd (l_pc!(unat pc)))" 
      have c0_4:"\<exists> sz2 cond d. x64_decode (xpc + sz) l_bin0 = Some (sz2,Pjcc cond d)" 
        using c0 a1 apply(cases "x64_decode (xpc + sz) l_bin0",simp_all)
        subgoal for a apply(cases a,simp_all)
          subgoal for aa b apply(cases b,simp_all)
            done
          done
        done
      then obtain sz2 cond d where c0_5:"x64_decode (xpc + sz) l_bin0 = Some (sz2,Pjcc cond d)" by auto
      have c0_6:"?num = 1" using c0 a1 using c0_4 
        apply(cases "x64_decode (xpc + sz) l_bin0",simp_all) 
        subgoal for a apply(cases a,simp_all)
          subgoal for aa b apply(cases b,simp_all)
            subgoal for x131 x132
              using snd_conv by fastforce 
            done
          done
        done

      have "\<exists> fxst1. fxst1 = x64_sem ?num l_bin0 (Next xpc xrs xm xss)" by fastforce
      then obtain fxst1 where c1:"fxst1 = x64_sem ?num l_bin0 (Next xpc xrs xm xss)" by auto
      have c1_1:"fxst1 \<noteq> Stuck" using c0 a1 c1 using c0_4 c0_6
        apply(cases "x64_decode (xpc + sz) l_bin0",simp_all) 
        apply(cases "x64_sem ?num l_bin0 (Next xpc xrs xm xss)",simp_all) 
        subgoal for a apply(cases a,simp_all)
          subgoal for aa b apply(cases b,simp_all)
            done
          done
        done

      hence "\<exists> xpc1 xrs1 xm1 xss1. Next xpc1 xrs1 xm1 xss1 = fxst1"
        by (metis outcome.exhaust) 
      then obtain xpc1 xrs1 xm1 xss1 where c2:"Next xpc1 xrs1 xm1 xss1 = fxst1" by auto

      have bn:"find_target_pc_in_l_pc l_jump (unat pc) \<noteq> None"
      proof(rule ccontr)
        assume assm:"\<not> (find_target_pc_in_l_pc l_jump (unat pc) \<noteq> None)"
        hence "snd fxst' = Stuck" using c0 c0_5 c1_1 c1 assm c0_6 by(cases "x64_sem ?num l_bin0 (Next xpc xrs xm xss)",simp_all) 
        thus "False" using a1 by auto
      qed

      have c3_0:"snd fxst' = snd (case find_target_pc_in_l_pc l_jump (unat pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> if eval_testcond cond xrs1 then \<comment>\<open> must JUMP \<close>
              ((npc, (Next (fst (l_pc!(unat npc))) xrs1 xm1 xss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, (Next (xpc1+sz2) xrs1 xm1 xss1)))
          " using c2 c1 c0 c0_5 c0_6 apply(cases "x64_decode (xpc+sz) l_bin0",simp_all)
        by(cases "x64_sem ?num l_bin0 (Next xpc xrs xm xss)",simp_all)

      hence "fxst1 = x64_sem 0 l_bin0 (exec_instr (Pcmpq_rr src dst) sz xpc xrs xm xss)" 
        using c0_1 c1 c0_6 a3 by simp
      hence c5:"fxst1 = (exec_instr (Pcmpq_rr src dst) sz xpc xrs xm xss)" by simp

      have "fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = (
                 let pair = fix_bpf_one_step (l_bin0,l_pc,l_jump) xst in
                  fix_bpf_sem 1 (l_bin0,l_pc,l_jump) pair)"
                  by (metis Suc_1 fix_bpf_sem.simps(2)) 
                
      hence d0:"fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = (let pair = (
                      ((case x64_decode xpc l_bin0 of 
                                    Some(sz, Pcall_i imm) \<Rightarrow>
                                        let v = find_target_pc_in_l_pc2 l_pc xpc 0 in
                                        (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                                        (case find_target_pc_in_l_pc l_jump pc of
                                          None \<Rightarrow> Stuck |
                                          Some npc \<Rightarrow>
                                        exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss)) |
                                    Some(sz, Pjcc cond d) \<Rightarrow> 
                                      let v = find_target_pc_in_l_pc2 l_pc (xpc-3) 0 in
                                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                                        (case find_target_pc_in_l_pc l_jump pc of
                                          None \<Rightarrow> Stuck |
                                          Some npc \<Rightarrow>
                                            (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc+sz+1)))) sz xpc xrs xm xss))) |
                                    Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc xrs xm xss) |
                                    _ \<Rightarrow> Stuck 
                  ))) in fix_bpf_sem 1 (l_bin0,l_pc,l_jump) pair)" using fix_bpf_one_step_def a3 by auto

     hence "fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = (let pair = exec_instr (Pcmpq_rr src dst) sz xpc xrs xm xss in fix_bpf_sem 1 (l_bin0,l_pc,l_jump) pair)"
       using d0 a3 c0_1 by auto
     hence d2:"fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1"
       using c5 by auto
     have d2_1:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1 = (
                      ((case x64_decode xpc1 l_bin0 of 
                                    Some(sz, Pcall_i imm) \<Rightarrow>
                                         let v = find_target_pc_in_l_pc2 l_pc xpc1 0 in
                                        (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                                        (case find_target_pc_in_l_pc l_jump pc of
                                          None \<Rightarrow> Stuck |
                                          Some npc \<Rightarrow>
                                        exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc1 xrs1 xm1 xss1)) |
                                    Some(sz, Pjcc cond d) \<Rightarrow> 
                                      let v = find_target_pc_in_l_pc2 l_pc (xpc1-3) 0 in
                                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                                        (case find_target_pc_in_l_pc l_jump pc of
                                          None \<Rightarrow> Stuck |
                                          Some npc \<Rightarrow>
                                            (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc1+sz+1)))) sz xpc1 xrs1 xm1 xss1))) |
                                    Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc1 xrs1 xm1 xss1) |
                                    _ \<Rightarrow> Stuck 
                  )))" using c2 fix_bpf_one_step_def by auto

     have d1_0:"fst (l_pc!(unat pc)) = xpc" using a0 a1 a3 flat_bpf_one_step_def apply(cases xst,simp_all) subgoal for x11
         using b0_2 by fastforce done
     have d1_0_0:"\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> snd(snd (lt!idx)) \<noteq> []" using well_formed_prog_def a5 by blast 
     hence d1_0_1:"is_increase_list_l_pc l_pc l_bin0" 
       using l_pc_elem_increases init_second_layer_def is_increase_list_l_pc_def by (metis a4 less_nat_zero_code list.size(3))  
     hence d1_0_2:"distinct (map fst l_pc)" using l_pc_is_distinct init_second_layer_def a4 d1_0_0
       by (metis distinct.simps(1) is_increase_list_l_pc_def less_nat_zero_code list.simps(8) list.size(3)) 
     hence d1:"find_target_pc_in_l_pc2 l_pc xpc 0 = Some (unat pc)" 
       using l_pc_index_corr b0_3 d1_0 d1_0_1 d1_0_2 by metis 
     have d1_3:"sz+xpc =xpc1"  using c2 c0_1 c5 by(unfold exec_instr_def,simp_all)
     hence d1_1:"int xpc1-3 = int xpc" using c0_2 by simp
     hence d1_2:"find_target_pc_in_l_pc2 l_pc (xpc1-3) 0 = Some (unat pc)" using d1_1 d1 c0_2 d1_3 by force 
     have "x64_decode xpc1 l_bin0 = Some (sz2,Pjcc cond d)" 
       using c0_5 d1_3 by (simp add: add.commute)
     hence d5:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1 = (case find_target_pc_in_l_pc l_jump (unat pc) of
                                          None \<Rightarrow> Stuck |
                                          Some npc \<Rightarrow>
                                            (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc1+sz2+1)))) sz2 xpc1 xrs1 xm1 xss1))"
       using c0_5 d1_2 d2_1 c5 d2 d1_3 bn by(cases "x64_decode xpc1 l_bin0",simp_all)

      thus ?thesis
      proof(cases "eval_testcond cond xrs1")
        case True
        have b1:"eval_testcond cond xrs1" using True by simp

        have "\<exists> npc. find_target_pc_in_l_pc l_jump (unat pc) = Some npc" using bn by simp
        then obtain npc where c3_1:"find_target_pc_in_l_pc l_jump (unat pc) = Some npc" by auto                                 
        have c3:"snd fxst' = (Next (fst (l_pc!(unat npc))) xrs1 xm1 xss1)" 
          using True c3_0 c3_1 b1 by simp

        have d8:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1 = (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc1+sz2+1)))) sz2 xpc1 xrs1 xm1 xss1)" 
          using True d5 c3_1 by simp
        have "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1  = (let b =  eval_testcond cond xrs1 in
            if b then Next (unat (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc1+sz2+1))::i32)+xpc1+sz2+1) xrs1 xm1 xss1
            else Next (xpc1+sz2) xrs1 xm1 xss1)" using d8 True apply(unfold exec_instr_def,simp_all) done
                  
        hence d9:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1 = (Next (fst (l_pc!(unat npc))) xrs1 xm1 xss1)" using True apply(cases "eval_testcond cond xrs1",simp_all)
          sorry
        hence "fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst =  (Next (fst (l_pc!(unat npc))) xrs1 xm1 xss1)" using d2 by auto

        hence "\<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')" 
           using match_state2_def match_mem_def c3 a1 by auto
        thus ?thesis by simp
  
 next
   case False
   have b1:"\<not>(eval_testcond cond xrs1)" using False by simp
   have b1_1:"snd fxst' = (Next (xpc1+sz2) xrs1 xm1 xss1)" using b1 c3_0 c0_5 bn by fastforce   
   hence "\<exists> npc. find_target_pc_in_l_pc l_jump (unat pc) = Some npc" using bn by simp
   then obtain npc where b2:"find_target_pc_in_l_pc l_jump (unat pc) = Some npc" by auto
   have "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1 = (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc1+sz2+1)))) sz2 xpc1 xrs1 xm1 xss1)" using b2 d5 by simp
   
   hence b3:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) fxst1 = (Next (xpc1+sz2) xrs1 xm1 xss1)"  
     using b1_1 apply(unfold exec_instr_def,simp_all)
     using b1 by argo 
   
   hence "fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = Next (xpc1+sz2) xrs1 xm1 xss1" using b3 a2 d2 by simp
   hence "\<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')" 
   using match_state2_def match_mem_def b1_1 by auto

   then show ?thesis by simp
 qed
next
  case False
  have b1:"\<not>(\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst))" using False by simp
  then show ?thesis 
  proof(cases "\<exists> sz imm. x64_decode xpc l_bin0 = Some(sz, Pcall_i imm)")
    case True
    have b1:"\<exists> sz imm. x64_decode xpc l_bin0 = Some(sz, Pcall_i imm)" using True by auto
    then obtain sz imm where b2:"x64_decode xpc l_bin0 = Some(sz, Pcall_i imm)" by auto
    have c0:"snd fxst' = snd (let num = snd (l_pc!(unat pc)) in case x64_decode xpc l_bin0 of Some(_, Pcall_i _) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump (unat pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> (let xst_temp = exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss in 
                  (case xst_temp of Stuck \<Rightarrow> (pc, Stuck) | 
                                    Next xpc' rs' m' ss' \<Rightarrow> (npc, (Next xpc' rs' m' ss'))))))" 
      using b0_1 b0_3 b2 a3 b0_2 by(unfold flat_bpf_one_step_def,simp_all)
    hence c1:"find_target_pc_in_l_pc l_jump (unat pc) \<noteq> None" using a1 b2
      using split_pairs by fastforce 
    hence "\<exists> npc. find_target_pc_in_l_pc l_jump (unat pc) = Some npc" by simp
    then obtain npc where c2:"find_target_pc_in_l_pc l_jump (unat pc) = Some npc" by auto
    have c3_1:"exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss \<noteq> Stuck" using c2 c0 a1 b2 by fastforce
    hence c3:"snd fxst' = (case exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss of Next xpc' rs' m' ss' \<Rightarrow> 
              Next xpc' rs' m' ss')" 
      using c0 c2 True
      by (smt (z3) case_prod_conv exec_instr_def hhh instruction.simps(548) option.case_eq_if option.simps(5) outcome.simps(4) split_pairs) 
     
    have "Mem.storev M64 xm (Vptr sp_block ((xrs (IR SP))-(u64_of_memory_chunk M64)))  (Vlong (of_nat xpc+1)) \<noteq> None" using exec_call_def c3_1 Let_def
      by (simp add: storev_stack_some) 
    hence "\<exists> m'. storev M64 xm (Vptr sp_block ( xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (of_nat xpc + (1::64 word))) = Some m'" by auto
    then obtain m' where c3_2:"storev M64 xm (Vptr sp_block ( xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (of_nat xpc + (1::64 word))) = Some m'" by auto
    hence c4_0:"exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc)))::u32)) sz xpc xrs xm xss = Next (unat (of_nat(fst (l_pc!(unat npc)))::u32)) (xrs#(IR SP) <- ((xrs (IR SP))-(u64_of_memory_chunk M64))) m' xss" 
      using c3_2 apply (simp add: exec_call_def,simp_all)
      by (simp add: exec_call_def exec_instr_def) 
    have "fst (l_pc!(unat npc)) = 1000" sorry
    hence c4_1:"fst (l_pc!(unat npc)) = (unat ((of_nat(fst (l_pc!(unat npc))))::u32))" by simp
    hence c4:"snd fxst' = Next (fst (l_pc!(unat npc))) (xrs#(IR SP) <- ((xrs (IR SP))-(u64_of_memory_chunk M64))) m' xss" 
      using c3 c4_0 by simp 

    have "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = fix_bpf_one_step (l_bin0,l_pc,l_jump) xst" by simp
    hence d0:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = 
                      (let v = find_target_pc_in_l_pc2 l_pc xpc 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss)))" 
      using b2 a3 by(unfold fix_bpf_one_step_def,simp_all)
    
    let "?imm" = "(of_nat(fst (l_pc!(unat npc)))::u32)"
    have d1_0_0:"\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> snd(snd (lt!idx)) \<noteq> []" using well_formed_prog_def a5 by blast 
     hence d1_0_1:"is_increase_list_l_pc l_pc l_bin0" 
       using l_pc_elem_increases init_second_layer_def is_increase_list_l_pc_def by (metis a4 less_nat_zero_code list.size(3))  
     hence d1_0_2:"distinct (map fst l_pc)" using l_pc_is_distinct init_second_layer_def a4 d1_0_0
       by (metis distinct.simps(1) is_increase_list_l_pc_def less_nat_zero_code list.simps(8) list.size(3)) 
     hence d1:"find_target_pc_in_l_pc2 l_pc xpc 0 = Some (unat pc)" 
       using l_pc_index_corr b0_3 d1_0_1 d1_0_2 b0_2 by blast 
    hence d2:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = exec_instr (Pcall_i ?imm) sz xpc xrs xm xss"
      using d1 c2 d0 by force
    hence "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = exec_call xpc sz M64 xm xss xrs ?imm"
      using exec_instr_def by auto
    
    have "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = (
           (let nsp::64 word = xrs (IR SP) - u64_of_memory_chunk M64 in case storev M64 xm (Vptr sp_block nsp) (Vlong (of_nat xpc + (1::64 word))) of None \<Rightarrow> Stuck | 
                Some (m'::nat \<Rightarrow> int \<Rightarrow> 8 word option) \<Rightarrow> let rs1::preg \<Rightarrow> 64 word = xrs(IR SP := nsp) in Next (unat ?imm) rs1 m' xss) 
  )" using exec_call_def of_nat_def of_int_def c3_2 c4_0 d2 by force 
    hence d3:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = Next (unat (of_nat (fst (l_pc ! unat npc))::u32)) (xrs#(IR SP) <- ((xrs (IR SP))-(u64_of_memory_chunk M64))) m' xss"
      using c3_2 by auto

   
    have "match_state2 (fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst) (snd fxst')" using match_state2_def match_mem_def d3 c4 c3_1 c4_0 c4_1 
      by (metis (no_types, lifting)) 
    hence "\<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')" by blast
    then show ?thesis by simp
  next
    case False
    have b2:"\<not> (\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)) \<and> \<not> (\<exists> sz imm. x64_decode xpc l_bin0 = Some(sz, Pcall_i imm))" using b1 False by simp
    then show ?thesis
    proof(cases "\<exists> sz. x64_decode xpc l_bin0 = Some(sz, Pret_anchor)")
      case True
      obtain sz where b2_0:"x64_decode xpc l_bin0 = Some(sz, Pret_anchor)" using True by auto
      have "\<exists> pc'. fxst' = (pc', Next xpc'' xrs'' xm'' xss'')" using a0 a1
        by (metis eq_snd_iff) 
      then obtain pc' where b2_1:"fxst' = (pc', Next xpc'' xrs'' xm'' xss'')" by auto
      hence "fxst' = (let pair = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst) in flat_bpf_sem 0 (l_bin0,l_pc,l_jump) pair)"using a0 by simp
      hence b0_1:"fxst' = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst)" by (metis flat_bpf_sem.simps(1) prod.collapse)
      have "\<exists> sz2. x64_decode (xpc+sz) l_bin0 = Some (sz2,Pret)" using b2_0 b2_1 b0_1 a3 b0_3 b0_2 apply(unfold flat_bpf_one_step_def Let_def,simp_all) 
        apply(cases "x64_decode (xpc + sz) l_bin0",simp_all)
        subgoal for a apply(cases a,simp_all)
          subgoal for aa b apply(cases b,simp_all)
            done
          done
        done
      then obtain sz2 where b2_2:"x64_decode (xpc+sz) l_bin0 = Some (sz2,Pret)" by auto
      hence c0:"(pc', Next xpc'' xrs'' xm'' xss'') = 
          (let (pc', ss', caller,fp) = update_stack2 xss in 
          if find_target_pc_in_l_pc3 l_jump (unat pc) \<noteq> Some (uint pc') then (pc,Stuck) else
          let rs' = restore_x64_caller xrs caller fp in let xst_temp = exec_instr Pret sz2 (xpc+sz) rs' xm ss' in 
          (case xst_temp of Stuck \<Rightarrow> (pc,Stuck)| Next xpc1 rs1 m1 ss1 \<Rightarrow> 
            (if xpc1 = (fst (l_pc!(unat pc'))+1) then (pc',Next xpc1 rs1 m1 ss1) else (pc,Stuck) )))" 
        using a6 a3 a0 a1 b0_3 b0_2 b2_0 b0_1 b2_1 by(unfold flat_bpf_one_step_def Let_def,simp_all) 
      
      let "?ss'" = "(fst(snd(update_stack2 xss)))"
      let "?rs'" = "(restore_x64_caller xrs (fst(snd(snd(update_stack2 xss)))) (snd(snd(snd(update_stack2 xss)))))"
      let "?pc'" = "fst (update_stack2 xss)"
      
      have cn:"find_target_pc_in_l_pc3 l_jump (unat pc) = Some (uint (?pc'))" using c0 apply(cases "update_stack2 xss",simp_all)
        subgoal for a b c d apply(split if_splits,simp_all)
          done
        done

      have c0_2:"exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' \<noteq> Stuck" using c0 cn apply(unfold Let_def,simp_all) apply(cases "update_stack2 xss",simp_all)
        subgoal for a b c d by fastforce 
        done
      hence "\<exists> xpc1 xrs1 xss1 xm1. exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' = Next xpc1 xrs1 xss1 xm1"
        by (meson outcome.exhaust) 
      then obtain xpc1 xrs1 xss1 xm1 where c0_3:"exec_instr Pret sz2 (xpc+sz) ?rs' xm ?ss' = Next xpc1 xrs1 xss1 xm1" by auto
      hence "xpc1 = (fst (l_pc!(unat ?pc'))+1)"
        using c0 cn apply(unfold Let_def,simp_all) apply(cases "update_stack2 xss",simp_all)
        subgoal for a b c d 
          by (smt (verit, ccfv_threshold) outcome.distinct(1) outcome.exhaust outcome.simps(4) split_pairs)
        done
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


      have "fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = fix_bpf_sem 1 (l_bin0,l_pc,l_jump) (fix_bpf_one_step (l_bin0,l_pc,l_jump) xst)"
        by (metis Suc_1 fix_bpf_sem.simps(2)) 
      hence d0:"fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = fix_bpf_sem 1 (l_bin0,l_pc,l_jump) (exec_instr Pret_anchor sz xpc xrs xm xss)"
        using b2_0 a3 b2 by(unfold fix_bpf_one_step_def Let_def,simp_all)
      hence d1:"fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = fix_bpf_sem 1 (l_bin0,l_pc,l_jump) (exec_ret_external xpc sz M64 xm xss xrs)" using exec_instr_def by simp
      have d2:" (\<exists> xpc1 xrs1 xm1 xss1. exec_ret_external xpc sz M64 xm xss xrs = Next xpc1 xrs1 xm1 xss1 \<and>
        (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in ss' = xss1 \<and> xm1 = xm \<and> xpc1 = xpc + sz \<and> xrs1 = rs'))"
        using exec_ret_external_prop by fastforce 

      then obtain xpc1 xrs1 xm1 xss1 where d3:"exec_ret_external xpc sz M64 xm xss xrs = Next xpc1 xrs1 xm1 xss1 \<and>
        (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in ss' = xss1 \<and> xm1 = xm \<and> xpc1 = xpc+sz \<and> xrs1 = rs')" by auto

      hence d3_0:"Next xpc1 xrs1 xm1 xss1 = Next (xpc+sz) (restore_x64_caller xrs (fst(snd(snd(update_stack2 xss)))) (snd(snd(snd(update_stack2 xss))))) xm (fst(snd(update_stack2 xss)))" 
              apply(unfold Let_def,simp_all)
        by(cases "update_stack2 xss",simp_all)

      hence d4:"fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = fix_bpf_sem 1 (l_bin0,l_pc,l_jump) (Next xpc1 xrs1 xm1 xss1)" using d1 d3 by argo 

      hence d4_0:"xpc1 = (xpc+sz) \<and> xm = xm1 \<and> xrs1 = ?rs' \<and> xss1 = ?ss'" 
        using d4 d3_0 by fastforce

      let "?pc" = "fst (update_stack2 xss)"
      have e0:"find_target_pc_in_l_pc3 l_jump (unat pc) = Some (uint ?pc)" using cn by simp

      have "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) (Next xpc1 xrs1 xm1 xss1) = fix_bpf_one_step (l_bin0,l_pc,l_jump) (Next xpc1 xrs1 xm1 xss1)" by fastforce
      hence d5:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) (Next xpc1 xrs1 xm1 xss1) =  (exec_instr Pret sz xpc1 xrs1 xm1 xss1)" 
        using b2_2 d4_0 apply(unfold fix_bpf_one_step_def,simp_all) by (simp add: exec_instr_def) 

      (*hence e1:"find_target_pc_in_l_pc2 l_pc (xpc1-sz) 0 = Some (unat pc)" 
        using l_pc_index_corr b0_3 b0_2
        by (metis add_diff_cancel_right' d4_0 less_nat_zero_code list.size(3)) *)

      hence "exec_instr Pret sz2 xpc1 xrs1 xm1 xss1 =  
        (let nsp =  (xrs1 (IR SP)) + (u64_of_memory_chunk M64) in
            case Mem.loadv M64 xm1 (Vptr sp_block nsp) of
            None \<Rightarrow> Stuck |
            Some ra \<Rightarrow> (
              case ra of
              Vlong v \<Rightarrow> let rs1 = xrs1#(IR SP) <- nsp in
                          Next (unat v) rs1 xm1 xss1 |
              _ \<Rightarrow> Stuck)
        )" by(unfold exec_instr_def exec_ret_def,simp_all)

      hence "exec_instr Pret sz2 xpc1 xrs1 xm1 xss1 = Next (unat v) (?rs'#(IR SP) <- ((?rs' (IR SP)) + (u64_of_memory_chunk M64))) xm1 xss1"
        using d4_0 c0_5
        using c0_7 by presburger 
      hence "fix_bpf_sem 2 (l_bin0,l_pc,l_jump) xst = snd fxst'"
        using d4 d5 c1 apply (simp add: exec_instr_def) using d4_0 by fastforce 
      hence "\<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')"
        using c1 match_state2_def match_mem_def
        by auto
        
      then show ?thesis by blast
    next
      case False
      have "\<not> (\<exists> sz src dst. x64_decode xpc l_bin0 = Some(sz, Pcmpq_rr src dst)) \<and> \<not> (\<exists> sz imm. x64_decode xpc l_bin0 = Some(sz, Pcall_i imm)) \<and> \<not>(\<exists> sz. x64_decode xpc l_bin0 = Some(sz, Pret_anchor))" using b2 False by simp
      hence c0:"snd fxst' = (let num = snd (l_pc!(unat pc)) in x64_sem num l_bin0 (Next xpc xrs xm xss))"
        using b0_1 b0_2 b0_3 a3 apply(unfold flat_bpf_one_step_def Let_def,simp_all)apply(cases "x64_decode xpc l_bin0",simp_all)
        subgoal for a apply(cases a,simp_all)
          subgoal for aa b apply(cases b,simp_all)
            done
          done
        done
      let "?num" = "snd (l_pc!(unat pc))"
      have cn:"x64_bin_is_sequential ?num l_bin0 xpc" by (meson False a4 a2 a5 b2 x64_bin_is_sequential_x64_decode3) 

      have d0:"x64_sem ?num l_bin0 (Next xpc xrs xm xss) = fix_bpf_sem ?num (l_bin0,l_pc,l_jump) xst" 
        using x64_bin_is_sequential_equivalence a3 cn by presburger 
      then show ?thesis using c0 a1 match_state2_def by (metis outcome.distinct(1)) 
    qed
  qed
 qed
qed


lemma fix_bpf_sem_induct:
  "fix_bpf_sem (Suc n) (l_bin0,l_pc,l_jump) xst = fst' \<Longrightarrow> 
  xst = (Next pc rs ms ss) \<Longrightarrow>
   \<exists> fst1. fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = fst1 \<and> 
         fix_bpf_sem n (l_bin0,l_pc,l_jump) fst1 = fst'"
  by simp

lemma fix_bpf_sem_induct2:
  "xst = (Next pc rs ms ss) \<Longrightarrow>
   \<exists> fst1. fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = fst1 \<and> 
         fix_bpf_sem n (l_bin0,l_pc,l_jump) fst1 = fst' \<Longrightarrow> 
fix_bpf_sem (Suc n) (l_bin0,l_pc,l_jump) xst = fst'"
  by simp

(*lemma fix_bpf_sem_stuck : 
" fix_bpf_sem (m+n) lt Stuck = fst' \<Longrightarrow>
  fix_bpf_sem n lt (fix_bpf_sem m lt Stuck) = fst'"
  apply (cases m,simp)
  subgoal for m
    apply(cases n,simp)              
    subgoal for nat 
  done*)

lemma fix_bpf_sem_induct3:
  "xst = (Next pc rs ms ss) \<Longrightarrow>
  fix_bpf_sem m (l_bin0,l_pc,l_jump) xst = fst1 \<Longrightarrow>
  fix_bpf_sem n (l_bin0,l_pc,l_jump) fst1 = fst' \<Longrightarrow> 
  fix_bpf_sem (m+n) (l_bin0,l_pc,l_jump) xst = fst'"
  sorry
(*  apply(induct m arbitrary: xst pc rs ms ss l_bin0 l_pc l_jump fst1 n fst')
  subgoal for xst pc rs ms ss l_bin0 l_pc l_jump fst1 pc' rs' 
    by simp 
  subgoal for m xst pc rs ms ss l_bin0 l_pc l_jump fst1 pc' rs'  *)

lemma n_steps_equiv_layer2:
  "flat_bpf_sem n (l_bin0,l_pc,l_jump) (pc,xst) = fxst' \<Longrightarrow> 
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow> 
  jitper insns = Some lt \<Longrightarrow> 
  xst = Next xpc xrs xm xss \<Longrightarrow> 
  jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow> 
  well_formed_prog lt \<Longrightarrow> 
  \<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')"
proof(induct n arbitrary:l_bin0 l_pc l_jump pc xst fxst' xpc'' xrs'' xm'' xss'' insns lt xpc xrs xm xss)
  case 0
  have "\<exists> num fst'. num = 0 \<and> fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')"
    using match_state2_def "0.prems"(2) JITPer_aux.match_mem_def "0.prems"(1) by fastforce 
  then show ?case by blast
next
  case (Suc n)
  assume a0:"flat_bpf_sem (Suc n) (l_bin0,l_pc,l_jump) (pc,xst) = fxst'" and 
    a1:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and 
    a2:"jitper insns = Some lt" and 
    a3:"xst = Next xpc xrs xm xss" and     
    a4:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and 
    a5:"well_formed_prog lt" 

  have "\<exists> next_f. flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = next_f" by blast
  then obtain next_f where b0:"flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = next_f" by auto
  have b1:"unat pc < length lt \<and> unat pc \<ge> 0" 
  proof(rule ccontr)
    assume assm:"\<not> (unat pc < length lt \<and> unat pc \<ge> 0)"
    have "snd next_f = snd (let pair = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst) in
    flat_bpf_sem 0 (l_bin0,l_pc,l_jump) pair)" 
      using b0 by fastforce
    hence "snd next_f = snd (flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst))"
      by (metis flat_bpf_sem.simps(1) prod.collapse) 
    hence "snd next_f = Stuck" 
      using flat_bpf_one_step_def assm a1 apply(cases xst,simp_all)
      subgoal for x11 x12 x13 x14 apply(cases "(l_bin0,l_pc,l_jump)",simp_all)
        subgoal for a 
          by (smt (z3) Suc.prems(5) add.right_neutral init_second_layer_def l_pc_length_prop list.size(3) nat_le_linear nat_less_le)
        done
      done
      thus "False" using a1
        by (metis a0 b0 err_is_still_err3 flat_bpf_sem_induct_aux2 outcome.distinct(1) prod.collapse) 
    qed
    have "\<exists> xpc1 xrs1 xm1 xss1. snd next_f = Next xpc1 xrs1 xm1 xss1" using flat_bpf_sem_induct_aux2 intermediate_step_is_ok3 a0 a3
      by (metis Suc.prems(2) b0 bot_nat_0.extremum outcome.distinct(1) prod.collapse) 
    then obtain xpc1 xrs1 xm1 xss1 where b2:"snd next_f = Next xpc1 xrs1 xm1 xss1" by auto
    hence "\<exists> num next_s. fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = next_s \<and> match_state2 next_s (snd next_f)"
      using one_steps_equiv_layer2 b0 a5 a1 a2 a3 a4 b1 by blast
    then obtain num1 next_s where b3:"fix_bpf_sem num1 (l_bin0,l_pc,l_jump) xst = next_s \<and> match_state2 next_s (snd next_f)" by auto
    have b4:"flat_bpf_sem n (l_bin0,l_pc,l_jump) next_f = fxst'" using flat_bpf_sem_induct_aux2 a0 b0 by blast
    hence "\<exists> num fst'. fix_bpf_sem num (l_bin0,l_pc,l_jump) (snd next_f) = fst' \<and> match_state2 fst' (snd fxst')"
      using fix_bpf_sem_induct match_state2_def jitflat_bpf_induct b2 a1 a4 a5 b3 b4
      by (metis Suc.hyps a2 prod.collapse) 
    then obtain num2 fst2 where b5:"fix_bpf_sem num2 (l_bin0,l_pc,l_jump) (snd next_f) = fst2 \<and> match_state2 fst2 (snd fxst')" by auto
    hence "fix_bpf_sem (num1+num2) (l_bin0,l_pc,l_jump) xst = fst2" using fix_bpf_sem_induct3
      using Suc.prems(4) b2 b3 match_state2_def by auto 
    hence "\<exists> num fst'. num = num1+num2 \<and> fst' = fst2 \<and> fix_bpf_sem num (l_bin0,l_pc,l_jump) xst = fst' \<and> match_state2 fst' (snd fxst')"
      using b5 by blast 
    then show ?case by blast 
  qed
(*lemma flat_bpf_sem_induct_aux2:
"flat_bpf_sem (Suc n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem 1 x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
  using flat_bpf_sem_induct_aux1 by simp*)


end
