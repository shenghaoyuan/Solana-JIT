(*
lemma jit_fix_change:
  "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow> 
  x64_decode xpc l_bin0 = Some v \<Longrightarrow>
  (\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d)) \<or> (\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pjcc cond d)) \<Longrightarrow>
  get_updated_l_bin x l l_pc 
  x64_decode xpc prog = x"
*)

(*
lemma jit_fix_not_change:
  "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow> 
  x64_decode xpc l_bin0 \<noteq> None \<Longrightarrow> 
  (\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pjcc cond d))) \<Longrightarrow>
  list_in_list l xpc l_bin0 \<longrightarrow> list_in_list l xpc prog"
  sorry
*)


(*
lemma jit_fix_change:
  "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow> 
  x64_decode xpc l_bin0 \<noteq> None \<Longrightarrow> 
  (\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d)) \<or> (\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pjcc cond d)) \<Longrightarrow>
  list_in_list l xpc l_bin0 \<longrightarrow> list_in_list l xpc prog"
  sorry


lemma list_in_list_prop4: "
  x64_sem num l_bin (Next xpc xrs xm xss) = fxst \<Longrightarrow>
  x64_sem num lt (Next xpc xrs xm xss) = xxst \<Longrightarrow>
  x64_bin_is_sequential (length l) l 0 \<Longrightarrow>
  list_in_list l xpc l_bin \<Longrightarrow>
  list_in_list l xpc lt \<Longrightarrow>
  fxst \<noteq> Stuck \<Longrightarrow>
  xxst = fxst"
  sorry
*)


(*
(*(l_bin0,l_pc,l_jump) *)
lemma n_steps_equiv_layer2:
  "flat_bpf_sem n (l_bin0,l_pc,l_jump) (pc,xst) = fxst' \<Longrightarrow>
  xst = Next xpc xrs xm xss \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>
  jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  well_formed_prog lt \<Longrightarrow>
  \<exists> num fst'. last_fix_sem num prog xst = fst' \<and> match_state2 fst' (snd fxst')"
proof(induct n arbitrary:l_bin0 l_pc l_jump pc xst fxst' xpc xrs xm xss xpc'' xrs'' xm'' xss'' prog lt)
  case 0 
  assume assm0:"flat_bpf_sem 0 (l_bin0,l_pc,l_jump) (pc,xst) = fxst'" and
    assm1:"xst = Next xpc xrs xm xss" and
    assm2:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and
    assm3:"jitfix l_jump l_bin0 l_pc = Some prog" and
    assm4:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and
    assm5:"well_formed_prog lt" 
  have a0:"last_fix_sem 0 prog xst = xst"  by (simp add: last_fix_sem_def) 
  have a1:"snd (flat_bpf_sem 0 (l_bin0,l_pc,l_jump) (pc,xst)) = xst" by simp

  have "\<exists> num fst'. num = 0 \<and> last_fix_sem num prog xst = fst'" using a0 by blast

  hence "\<exists> num fst'. num = 0 \<and> last_fix_sem num prog xst = fst' \<and> match_state2 fst' (snd fxst')"
  using a0 a1 apply(unfold match_state2_def last_fix_sem_def,simp_all) 
    using assm1 assm0 apply(cases fxst') 
    subgoal for a b apply(cases fxst')
      subgoal for aa ba apply(cases xst)
        subgoal for x11 x12 x13 x14 apply(cases xst,simp_all)
          subgoal for x11a by(cases b,simp_all)
          done
        apply(cases xst,simp_all)
          done
        done
      done
           
  then show ?case by blast
    (*by (smt (verit, ccfv_threshold) flat_bpf_sem.simps(1) last_fix_sem_def match_state2_def outcome.simps(4) snd_conv x64_sem.simps(1))*) 
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) (l_bin0,l_pc,l_jump) (pc,xst) = fxst'" and
    assm1:"xst = Next xpc xrs xm xss" and
    assm2:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and
    assm3:"jitfix l_jump l_bin0 l_pc = Some prog"
  have "\<exists> next_f. flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = next_f" by blast
  then obtain next_f where b0:"flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = next_f" by auto
  have "unat pc < length lt \<and> unat pc \<ge> 0" 
  proof(rule ccontr)
    assume assm:"\<not> (unat pc < length lt \<and> unat pc \<ge> 0)"
    have "snd next_f = snd (let pair = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst) in
    flat_bpf_sem 0 (l_bin0,l_pc,l_jump) pair)" 
      using b0 by fastforce
    hence "snd next_f = snd (flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst))"
      by (metis flat_bpf_sem.simps(1) prod.collapse) 
    hence "snd next_f = Stuck" 
      using flat_bpf_one_step_def assm assm2 apply(cases xst,simp_all)
      subgoal for x11 x12 x13 x14 apply(cases "(l_bin0,l_pc,l_jump)",simp_all)
        subgoal for a 
          by (smt (z3) Suc.prems(5) add.right_neutral init_second_layer_def l_pc_length_prop list.size(3) nat_le_linear nat_less_le)
        done
      done
      thus "False" using assm2
        by (metis assm0 b0 err_is_still_err3 flat_bpf_sem_induct_aux2 outcome.distinct(1) prod.collapse) 
  qed

  hence "\<exists> num next_s. last_fix_sem num prog xst = next_s \<and> match_state2 next_s (snd next_f)"
    using one_steps_equiv_layer2 b0 assm0 assm2 assm3 flat_bpf_sem_induct_aux2 intermediate_step_is_ok3
    by (metis (no_types, lifting) One_nat_def Suc.prems(2) Suc.prems(5) Suc.prems(6) less_eq_nat.simps(1) old.prod.exhaust snd_conv)  
  then obtain num next_s where b1:"last_fix_sem num prog xst = next_s \<and> match_state2 next_s (snd next_f)" by auto
  have "\<exists> xpc' xrs' xm' xss'. snd next_f = Next xpc' xrs' xm' xss'"
    by (metis Suc.prems(3) assm0 b0 flat_bpf_sem_induct_aux2 intermediate_step_is_ok3 less_eq_nat.simps(1) outcome.distinct(1) prod.collapse)
  then obtain xpc' xrs' xm' xss' where b2:"snd next_f = Next xpc' xrs' xm' xss'" by auto
  have b3:"flat_bpf_sem n (l_bin0,l_pc,l_jump) next_f = fxst'" using flat_bpf_sem_induct_aux2 b0 assm0 by blast 
  have "flat_bpf_sem n (l_bin0, l_pc, l_jump) (pc, xst) = fxst' \<Longrightarrow>
      xst = Next xpc xrs xm xss \<Longrightarrow> 
      snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow> 
      jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow> 
      \<exists>(num::nat) fst'::outcome. last_fix_sem num prog xst = fst' \<and> match_state2 fst' (snd fxst')" using Suc by simp
  hence "\<exists>(num::nat) fst'::outcome. last_fix_sem num prog (snd next_f) = fst' \<and> match_state2 fst' (snd fxst')" 
    using b2 b1 match_state2_def assm3 b0 assm2 b3
    by (metis Suc.hyps Suc.prems(5) Suc.prems(6) prod.collapse) 
    
  then show ?case
    by (metis Suc.prems(2) b1 last_fix_sem_def match_state2_def x64_sem_add) 
qed


lemma n_steps_equiv:
  assumes assm0:"perir_sem n lt (pc,xxst) = xxst'" and
  assm1:"xxst = Next xpc xrs xm xss" and
  assm2:"snd xxst' = Next xpc' xrs' xm' xss'" and
  assm3:"JITFlattern_def.match_state (pc,xxst) (pc,fxst)" and
  assm4:"lt \<noteq> []" and
  assm5:"well_formed_prog lt"and

  assm6:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and
  assm7:"flat_bpf_sem n (l_bin0,l_pc,l_jump) (pc,fxst) = fxst'" and
  assm8:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and

  assm9:"jitfix l_jump l_bin0 l_pc = Some prog" and
  (*assm10:"last_fix_sem n prog xst = fst'" and*)
  assm11:"jitper insns = Some lt"
  shows "\<exists> num fst'. last_fix_sem num prog fxst = fst' \<and> match_state1 fst' (snd xxst')"
proof-
  have b0:"JITFlattern_def.match_state xxst' fxst'" 
    using n_steps_equiv_layer1 assm3 assm0 assm1 assm2 assm4 assm5 assm11 assm6 assm7 assm8 by auto 
  have "\<exists> xpc1 xrs xm xss. fxst = Next xpc1 xrs xm xss" 
    using JITFlattern_def.match_state_def assm1 assm3 
    apply(cases xxst,simp_all) 
    apply(cases fxst,simp_all)
    done
  then obtain xpc1 xrs xm xss where b1:"fxst = Next xpc1 xrs xm xss" by auto
  have b2:"\<exists> num fst'. last_fix_sem num prog fxst = fst' \<and> match_state2 fst' (snd fxst')" 
    using n_steps_equiv_layer2 assm7 assm9 b1 assm8 assm6 assm5 by blast
  then obtain num fst' where b3:"last_fix_sem num prog fxst = fst' \<and> match_state2 fst' (snd fxst')" by auto
  hence b4:"match_state1 fst' (snd xxst')"
    apply(unfold JITFlattern_def.match_state_def match_state2_def,simp_all)
    using assm2 assm8 b0 b3
    apply(cases fst',simp_all)
    apply(cases "snd fxst'",simp_all)
    apply(cases "snd xxst'",simp_all) 
    subgoal for x11 x11a 
      apply(cases "snd fxst'",simp_all)
      subgoal for x11b
        apply(unfold JITFlattern_def.match_state_def match_state2_def match_state1_def,simp_all)
        apply(cases xxst',simp_all)
        subgoal for a b 
          apply(cases fxst',simp_all)
          done
        done
      done
    done
  have "\<exists> num fst'. last_fix_sem num prog fxst = fst' \<and> match_state1 fst' (snd xxst')" using b2 b4 b3 by blast
  thus ?thesis using b2 by auto
qed
*)


(*num = snd (l_pc!(unat pc))*)
(*
lemma one_steps_equiv_layer2:
  "flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = fxst' \<Longrightarrow>
  xst = Next xpc xrs xm xss \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>  
  jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  well_formed_prog lt \<Longrightarrow>
  unat pc < length lt \<and> unat pc \<ge> 0 \<Longrightarrow>
  \<exists> num fst'. last_fix_sem num prog xst = fst' \<and> match_state2 fst' (snd fxst')"
proof-
  assume a0:"flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = fxst'" and
  a1:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and
  a2:"jitfix l_jump l_bin0 l_pc = Some prog" and
  a3:"xst = Next xpc xrs xm xss" and
  a4:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and
  a5:"well_formed_prog lt" and
  a6:"unat pc < length lt \<and> unat pc \<ge> 0"

  have "snd fxst' =  snd (let pair = flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst) in flat_bpf_sem 0 (l_bin0,l_pc,l_jump) pair)"
            using a0 by simp
  hence b0_1:"snd fxst' =  snd (flat_bpf_one_step (l_bin0,l_pc,l_jump) (pc, xst))" by (metis flat_bpf_sem.simps(1) prod.collapse)
  have b0_3:"unat pc < length l_pc" using l_pc_length_prop a4 init_second_layer_def
    by (metis Nat.add_0_right a6 list.size(3)) 
  have b0_2:"nat (fst (l_pc!(unat pc))) = xpc" using a1 b0_1 b0_3 a3 flat_bpf_one_step_def sorry

  thus ?thesis 
  proof(cases "\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d)")
    case True
    then show ?thesis sorry
  next
    case False
    have b0:"\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))" using False by simp
    then show ?thesis
    proof(cases "\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pcmpq_rr src dst)")
      case True
      have c0_0:"\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pcmpq_rr src dst)" using True by simp
      then obtain num src dst where c0_1:"x64_decode xpc l_bin0 = Some(num, Pcmpq_rr src dst)" by auto
      have c0:"snd fxst' = snd (let num = snd (l_pc!(unat pc)) in case x64_sem num l_bin0 (Next xpc xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, (Next xpc1 rs1 m1 ss1))
          ))" using True a0 b0_1 a3 a6 b0_3 a1
        apply(unfold flat_bpf_one_step_def Let_def,simp_all) 
        apply(cases "x64_decode xpc l_bin0",simp_all)
        subgoal for a apply(split if_splits,simp_all)
          done
        done
      let "?num" = "(snd (l_pc!(unat pc)))"
      have "\<exists> fxst1. fxst1 = x64_sem ?num l_bin0 (Next xpc xrs xm xss)" by fastforce
      then obtain fxst1 where c1:"fxst1 = x64_sem ?num l_bin0 (Next xpc xrs xm xss)" by auto
      have "fxst1 \<noteq> Stuck" using c0 a1 c1 by(cases "x64_sem ?num l_bin0 (Next xpc xrs xm xss)",simp_all)
      hence "\<exists> xpc1 xrs1 xm1 xss1. Next xpc1 xrs1 xm1 xss1 = fxst1"
        by (metis outcome.exhaust) 
      then obtain xpc1 xrs1 xm1 xss1 where c2:"Next xpc1 xrs1 xm1 xss1 = fxst1" by auto
      have c3_0:"snd fxst' = snd (if xrs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) xrs1 xm1 xss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, (Next xpc1 xrs1 xm1 xss1))
          )" using c2 c1 c0
        by (metis (no_types, lifting) outcome.simps(4)) 
      thus ?thesis
      proof(cases "xrs1 (CR ZF) = 1")
        case True
        have b1:"xrs1 (CR ZF) = 1" using True by simp
        then show ?thesis
            proof(cases "find_target_pc_in_l_pc l_jump (uint pc) \<noteq> None")
              case True
                have "\<exists> npc. find_target_pc_in_l_pc l_jump (uint pc) = Some npc" using True by simp
                then obtain npc where c3_1:"find_target_pc_in_l_pc l_jump (uint pc) = Some npc" by auto                                 
                have c3:"snd fxst' = (Next (nat (fst (l_pc!(unat npc)))) xrs1 xm1 xss1)" 
                  using True c3_0 c3_1 b1 by simp
                have "distinct (map fst l_jump)" using init_second_layer_def a4 is_increase_list_empty
                  by (metis distinct.simps(1) l_jump_is_distinct list.simps(8)) 
                hence d0:"(uint pc,npc) \<in> set l_jump" using c3_1 search_l_jump by auto
                have d1_1:"l_bin0 \<noteq> []" using a2
                  by (metis True find_target_pc_in_l_pc.simps(1) jitfix.elims option.distinct(1)) 
                hence "jitfix [(uint pc,npc)] l_bin0 l_pc = get_updated_l_bin (uint pc,npc) l_bin0 l_pc" 
                  by(cases "get_updated_l_bin (uint pc,npc) l_bin0 l_pc",simp_all)
                hence d1:"jitfix [(uint pc,npc)] l_bin0 l_pc = (let fix_begin_addr = fst (l_pc!(nat(uint pc))); 
        (target_begin_addr,num2) = l_pc!(unat npc) in 
        (case x64_decode fix_begin_addr l_bin0 of 
              Some(sz, Pcall_i _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+of_nat sz+1)::i32) in 
                                     let u8_list = x64_encode (Pcall_i (ucast offset)) in
                                     Some (x64_bin_update (length u8_list) l_bin0 fix_begin_addr u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = nat fix_begin_addr+sz in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l_bin0 loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))" using get_updated_l_bin_def by simp

                let "?fix_begin_addr" = "fst (l_pc!(nat(uint pc)))"
                let "?target_begin_addr" = "fst (l_pc!(unat npc))"
                have d2:"nat ?fix_begin_addr = xpc" using b0_2 by auto
                hence "\<exists> sz src dst. x64_decode (nat ?fix_begin_addr) l_bin0 = Some(sz, Pcmpq_rr src dst)" using c0_0 by force 
                then obtain sz src dst where d3_1:"x64_decode (nat ?fix_begin_addr) l_bin0 = Some(sz, Pcmpq_rr src dst)" by auto
                hence d3:"jitfix [(uint pc,npc)] l_bin0 l_pc =  (let loc = nat ?fix_begin_addr+sz in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat ?target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l_bin0 loc u8_list) | 
                            _ \<Rightarrow> None ))" using d1 d2 d1_1
                  apply(cases "x64_decode (nat ?fix_begin_addr) l_bin0",simp_all)
                  subgoal for a apply(cases "l_pc ! unat npc",simp_all)
                    subgoal for aa b
                    proof -
                      assume "nat (fst (l_pc ! unat pc)) = xpc"
                      assume "(case get_updated_l_bin (uint pc, npc) l_bin0 l_pc of None \<Rightarrow> None | Some x \<Rightarrow> Some x) = 
                          (let loc = xpc + sz in case x64_decode loc l_bin0 of None \<Rightarrow> None | Some (sz2, Pjcc cond x) \<Rightarrow> 
                           let offset = word_of_int aa - (word_of_nat (loc + sz2) + (1::32 signed word)); 
                               u8_list = x64_encode (Pjcc cond (ucast offset)) in Some (x64_bin_update (length u8_list) l_bin0 loc u8_list) | Some (sz2, _) \<Rightarrow> None)"
                      assume a1: "l_pc ! unat npc = (aa, b)"
                      have "\<forall>i n. fst (i::int, n::nat) = i"
                        by simp
                      then show ?thesis
                        using a1 by presburger
                    qed 
                    done
                  done
                have "jitfix [(uint pc,npc)] l_bin0 l_pc \<noteq> None"
                proof(rule ccontr)
                  assume assm:"\<not> (jitfix [(uint pc,npc)] l_bin0 l_pc\<noteq> None)"
                  have "jitfix [(uint pc,npc)] l_bin0 l_pc = None" using assm by simp
                  hence "jitfix l_jump l_bin0 l_pc = None " using d0 sorry
                  thus "False" using a2 by simp
                qed
                hence "\<exists> prog'. Some prog' = jitfix [(uint pc,npc)] l_bin0 l_pc"
                  by force
                then obtain prog' where "Some prog' = jitfix [(uint pc,npc)] l_bin0 l_pc" by auto
                hence "prog' = (let loc = nat ?fix_begin_addr+sz in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat ?target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      (x64_bin_update (length u8_list) l_bin0 loc u8_list)))"
                  using d3 apply(cases "x64_decode (nat ?fix_begin_addr+sz) l_bin0",simp_all)
                  subgoal for a apply(cases a,simp_all)
                    subgoal for aa b apply(cases b,simp_all)
                      subgoal for x131 x132
                        by (meson option.inject)
                      done
                    done
                  done
                
                have "last_fix_sem 2 prog' xst = x64_sem 2 prog' xst" using last_fix_sem_def by simp
                hence e0_0:"last_fix_sem 2 prog' xst =  (
                  case x64_decode xpc prog' of
                  None \<Rightarrow> Stuck |
                  Some (sz, ins) \<Rightarrow>
                    x64_sem 1 prog' (exec_instr ins sz xpc xrs xm xss)
                )"  by (metis Suc_1 a3 x64_sem.simps(3)) 

               (* have "list_in_list (x64_encode(Pcmpq_rr src dst)) xpc l_bin0" using d2 d3_1 
                proof(rule ccontr)
                  assume assm:"\<not> (list_in_list (x64_encode(Pcmpq_rr src dst)) xpc l_bin0)"
                  have "\<not> (x64_decode xpc l_bin0 = Some (length (x64_encode(Pcmpq_rr src dst)), Pcmpq_rr src dst))" using x64_encode_decode_consistency assm 
                  have e0:"x64_decode xpc prog' = x64_decode xpc l_bin0" 
                  proof(rule ccontr)*)

                hence e1:"last_fix_sem 2 prog' xst =  (
                  case x64_decode xpc prog' of
                  Some (sz, Pcmpq_rr src dst) \<Rightarrow>
                    x64_sem 1 prog' (exec_instr (Pcmpq_rr src dst) sz xpc xrs xm xss)
                )" using c0_0 a3 e0_0 apply(cases "x64_decode xpc prog'",simp_all) sorry
                
                have "last_fix_sem 2 prog xst = x64_sem 2 prog xst" using last_fix_sem_def by simp
                hence e0:"last_fix_sem 2 prog xst =  (
                  case x64_decode xpc prog of
                  None \<Rightarrow> Stuck |
                  Some (sz, ins) \<Rightarrow>
                    x64_sem 1 prog (exec_instr ins sz xpc xrs xm xss)
                )"
                  by (metis Suc_1 a3 x64_sem.simps(3)) 
                have e1:"\<exists> num src dst. x64_decode xpc prog = Some(num, Pcmpq_rr src dst)" sorry
                hence "\<exists> src dst sz. last_fix_sem 2 prog xst = x64_sem 1 prog (exec_instr (Pcmpq_rr src dst) sz xpc xrs xm xss)"
                  using e0 e1 by force
                then obtain src dst sz where e2:"last_fix_sem 2 prog xst = x64_sem 1 prog (exec_instr (Pcmpq_rr src dst) sz xpc xrs xm xss)" by auto
                hence e3:"sz = 3" using x64_encode_decode_consistency x64_encode_def list_in_list_prop sorry

              then show ?thesis sorry
            next
              case False
              then show ?thesis sorry
            qed
      next
        case False
        then show ?thesis sorry
      qed
    next
      case False
      have b1:"(\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))) \<and> (\<not>(\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pcmpq_rr src dst)))"
        using False b0 by blast
      then show ?thesis
      proof(cases "\<exists> num. x64_decode xpc l_bin0 = Some(num, Pret)")
        case True
        then show ?thesis sorry
      next
        case False
        have b0_0:"(\<not>(\<exists> num. x64_decode xpc l_bin0 = Some(num,Pret))) \<and> (\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num src dst. x64_decode xpc l_bin0 = Some(num, Pcmpq_rr src dst)))"
          using b1 False by blast
        
        have b0_2:"x64_decode xpc l_bin0 \<noteq> None" 
        proof(rule ccontr)
          assume assm:"\<not> (x64_decode xpc l_bin0 \<noteq> None)"
          have "x64_decode xpc l_bin0 = None" using assm by blast          
          have c0:"snd fxst' =  snd (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin0 (Next xpc xrs xm xss)))" 
            using b0_0 a1 a3 b0_1 apply(unfold flat_bpf_one_step_def,simp_all)
            apply(cases "xst",simp_all)
            apply(split if_splits,simp_all)
            subgoal for x11 
            apply(cases "x64_decode xpc l_bin0",simp_all)
               apply (smt (z3) option.simps(4) outcome.simps(3) snd_conv)
              subgoal for a
                using assm by force
              done
            done            
          have "\<exists> num off l. lt!(unat pc) = (num,off,l)" by (metis surj_pair) 
          then obtain num off l where c0_1:"lt!(unat pc) = (num,off,l)" by auto
          hence c1:"(snd (l_pc ! unat pc)) = num" using flattern_num a6 a4 c0_1 by fastforce 
          have "num>0" using a5 well_formed_prog_def a6 c0_1 by force
          hence "(snd (l_pc ! unat pc)) > 0" using c1 by force
          hence "snd fxst' = Stuck" using c0 c1 apply(cases "x64_decode xpc l_bin0",simp_all)
             apply (smt (verit, del_insts) Suc_diff_1 option.simps(4) x64_sem.simps(3)) 
            subgoal for a using assm by auto
            done
          thus "False" using a1 by auto
        qed
       
        hence b0:"snd fxst' = x64_sem (snd (l_pc!(unat pc))) l_bin0 (Next xpc xrs xm xss)"
          using b0_0 b0_1 b0_2 a1 a3 b1 a6 b0_3 apply(unfold flat_bpf_one_step_def,simp_all)
            apply(cases "xst",simp_all)
          subgoal for x11 
            apply(unfold Let_def)
            apply(split if_splits,simp_all)
            apply(split if_splits,simp_all)
            subgoal for a b apply(cases b,simp_all)
              done
            done
          done
        have b1:"last_fix_sem (snd (l_pc!(unat pc))) prog xst = x64_sem (snd (l_pc!(unat pc))) prog xst" 
          using last_fix_sem_def by auto
        have "\<exists> l. list_in_list l xpc l_bin0 \<longrightarrow> list_in_list l xpc prog" using jit_fix_not_change b0_1 a2 b0_0
          using list_in_list.simps(1) by metis
        then obtain l where b2:"list_in_list l xpc l_bin0 \<longrightarrow> list_in_list l xpc prog" by auto
        thus ?thesis
        proof(cases "list_in_list l xpc l_bin0")
          case True
          have b2:"list_in_list l xpc l_bin0 = list_in_list l xpc prog" using True b2 by simp
          (*have "x64_decode 0 l = x64_decode xpc l_bin0 \<and> x64_decode 0 l = x64_decode xpc prog" using list_in_list_x64_decode b0_2 sorry
          hence "x64_decode xpc l_bin0 = x64_decode xpc prog " using list_in_list_x64_decode by argo *)
          have "x64_bin_is_sequential (length l) l 0" sorry
          hence "(last_fix_sem (snd (l_pc!(unat pc))) prog xst) = (snd fxst')" 
          using b0 b1 list_in_list_prop4 a1 by (metis True a3 b2)  
        hence "\<exists> num fst'. num = (snd (l_pc!(unat pc))) \<and> last_fix_sem num prog xst = fst' \<and> match_state2 fst' (snd fxst')"
          apply(unfold match_state2_def,simp_all) using a1 a3
          by(cases "snd fxst'",simp_all)           
        then show ?thesis by blast
        next
          case False
          then show ?thesis sorry
        qed
      qed
    qed
  qed
qed

*)



(*definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"flat_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
    let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 ; v2 = find_num_in_l_pc l_pc (int xpc) in 
      case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
        (case v2 of None \<Rightarrow> Stuck | Some num \<Rightarrow>
          (case x64_decode xpc l_bin of Some(sz, Pcall_i d) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump pc of 
              None \<Rightarrow> Stuck |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (of_int pc+1) ss in
                  (case ss' of None \<Rightarrow> Stuck | 
                  Some ra \<Rightarrow> (Next (nat (fst (l_pc!(unat npc)))) rs' m ra))))  |
              Some(_,Pret) \<Rightarrow>
                  let (pc', ss', caller,fp) = update_stack2 ss in 
                  let rs' = restore_x64_caller rs caller fp in Next (nat(fst(l_pc!(unat pc')))) rs' m ss' |
    _ \<Rightarrow> (x64_sem num l_bin (Next xpc rs m ss))
       
)))))"*)

(*
definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
    let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 ; v2 = find_num_in_l_pc l_pc (int xpc) in 
      case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
        (case v2 of None \<Rightarrow> Stuck | Some num \<Rightarrow>
          (case x64_decode xpc l_bin of Some(sz, Pcall_i d) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump pc of 
              None \<Rightarrow> Stuck |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (of_nat xpc) ss in
                  (case ss' of None \<Rightarrow> Stuck | 
                  Some ra \<Rightarrow> (Next (nat (fst (l_pc!(unat npc)))) rs' m ra))))  |
                  Some(_, Pjcc cond d) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
                          \<comment>\<open> case: BPF JMP \<close>
                          (case x64_sem num l_bin (Next xpc rs m ss) of
                          Stuck \<Rightarrow> Stuck | \<comment>\<open> if one step error, stop, it should be impossible \<close>
                          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
                            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
                              (case find_target_pc_in_l_pc l_jump pc of
                              None \<Rightarrow> Stuck |
                              Some npc \<Rightarrow>
                                (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
                            else \<comment>\<open> donot JUMP \<close>
                              (Next xpc1 rs1 m1 ss1)
                          )) |
              Some(_,Pret) \<Rightarrow>
                  let (xpc', ss', caller,fp) = update_stack2 ss in 
                  let rs' = restore_x64_caller rs caller fp in Next (unat xpc') rs' m ss' |
    _ \<Rightarrow> (x64_sem num l_bin (Next xpc rs m ss))
       
)))))"
*)

(*
definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
          (case x64_decode xpc l_bin of 
                  Some(sz, Pcall_i imm) \<Rightarrow>
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_int(fst (l_pc!(unat npc))))) sz xpc rs m ss)) |
                  Some(sz, Pjcc cond d) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_int (fst (l_pc!(unat npc)))-(of_nat (xpc+1)))) sz xpc rs m ss))) |
                  Some(sz, Pret) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case (exec_instr Pret sz xpc rs m ss) of Stuck \<Rightarrow> Stuck | 
                                          Next xpc1 rs1 m1 ss1 \<Rightarrow> let v2 = find_target_pc_in_l_pc3 l_jump pc in
                                            (case v2 of None \<Rightarrow> Stuck | Some pc'\<Rightarrow>
                                              (if xpc1 \<noteq> nat (fst (l_pc!(nat pc')))+1 then Stuck else Next xpc1 rs1 m1 ss1 )))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc rs m ss) |
                  _ \<Rightarrow> Stuck 
))))"*)


(*
definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
          (case x64_decode xpc l_bin of 
                  Some(sz, Pcall_i imm) \<Rightarrow>
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_int(fst (l_pc!(unat npc))))) sz xpc rs m ss)) |
                  Some(sz, Pjcc cond d) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_int (fst (l_pc!(unat npc)))-(of_nat (xpc+1)))) sz xpc rs m ss))) |
                  Some(sz, Pret) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case (exec_instr Pret sz xpc rs m ss) of Stuck \<Rightarrow> Stuck | 
                                          Next xpc1 rs1 m1 ss1 \<Rightarrow> let v2 = find_target_pc_in_l_pc3 l_jump pc in
                                            (case v2 of None \<Rightarrow> Stuck | Some pc'\<Rightarrow>
                                              (if xpc1 \<noteq> nat (fst (l_pc!(nat pc')))+1 then Stuck else Next xpc1 rs1 m1 ss1 )))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc rs m ss) |
                  _ \<Rightarrow> Stuck 
))))"
*)


(*
definition get_updated_l_bin::"(int\<times>u64) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin option"where
  "get_updated_l_bin x l l_pc \<equiv> 
    (let fix_begin_addr = fst (l_pc!(nat(fst x))); 
        (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
        (case x64_decode (nat fix_begin_addr) l of 
              Some(sz, Pcall_i _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+of_nat sz+1)::i32) in 
                                     let u8_list = x64_encode (Pcall_i (ucast offset)) in
                                     Some (x64_bin_update (length u8_list) l (nat fix_begin_addr) u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = nat fix_begin_addr+sz in 
                    (case x64_decode loc l of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"
*)


(*

definition x64_bin_update ::"x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
 "x64_bin_update l pc u8_list \<equiv>  ( let l1 = list_update l pc (u8_list!0);
                                       l2 = list_update l1 (pc+1) (u8_list!1);
                                       l3 = list_update l2 (pc+2) (u8_list!2);   
                                       l4 = list_update l3 (pc+3) (u8_list!3) in l4)"

definition get_updated_l_bin::"(int\<times>u64) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin"where
  "get_updated_l_bin x l l_pc \<equiv> 
    (let fix_begin_addr = fst (l_pc!(nat(fst x))); 
        (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
        (case x64_decode (nat fix_begin_addr) l of 
              Some(_, Pcall_i _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+5+1)::i32);
                              u8_list = u8_list_of_i32 offset in
                              x64_bin_update l (nat (fix_begin_addr+1)) u8_list | 
              _ \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+3+6+1)::i32);
                              u8_list = u8_list_of_i32 offset in                                                     
                             x64_bin_update l (nat (fix_begin_addr+3+2)) u8_list))"*)



(*definition update_l_jump_further::"flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> (hybrid_state \<times> flat_bpf_prog)" where
 "update_l_jump_further lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    (case xst of
    Stuck \<Rightarrow> ((pc, Stuck), lp) |
    Next xpc rs m ss \<Rightarrow> (
    if unat pc \<ge> length l_pc \<or> unat pc < 0 then ((pc, Stuck), lp) else 
    let num = snd (l_pc!(unat pc)) in 
    let old_xpc = nat (fst (l_pc!(unat pc))) in 
      if xpc \<noteq> old_xpc then ((pc, Stuck), lp) else 
        if (\<exists> d. x64_decode xpc l_bin = Some(5, Pcall_i d)) then
            (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> ((pc, Stuck), lp) |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (pc+1) ss in
                  (case ss' of None \<Rightarrow> ((pc, Stuck), lp) | 
                  Some ra \<Rightarrow> ((npc, (Next (nat (fst (l_pc!(unat npc)))) rs' m ra)), lp))))
        else if (\<exists> src dst. x64_decode xpc l_bin = Some(3, Pcmpq_rr src dst)) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem num l_bin (Next xpc rs m ss) of
          Stuck \<Rightarrow> ((pc, Stuck), lp) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> ((pc, Stuck), lp) |
              Some npc \<Rightarrow>
                ((npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1)),lp)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              ((pc+1, (Next xpc1 rs1 m1 ss1)), lp)
          ))
        else if x64_decode xpc l_bin = Some(1,Pret) then
          let (pc', ss', caller,fp) = update_stack2 ss in 
          let rs' = restore_x64_caller rs caller fp in ((pc', Next xpc rs' m ss'), lp)
          \<comment>\<open> case: NOT BPF JMP \<close>
        else
          ((pc+1, x64_sem num l_bin (Next xpc rs m ss)), lp)
)))"
*)

