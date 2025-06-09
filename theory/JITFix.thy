theory JITFix
  imports JITFix_aux JITFix_prob1
begin

  value "(((of_nat 0)::u32) - (of_nat 1)::u32)"
  value "((of_nat (0-1))::u32)"

lemma jitfix_induct:
  "jitfix (a#l_jump) l_bin0 l_pc = Some prog \<Longrightarrow> 
  \<exists> prog'. jitfix [a] l_bin0 l_pc = Some prog' \<and> jitfix l_jump prog' l_pc = Some prog"
  by (metis (no_types, lifting) jitfix.elims jitfix.simps(1) jitfix.simps(2) option.case_eq_if option.discI)
 

lemma jitfix_induct2:
  "\<exists> prog'. jitfix [a] l_bin0 l_pc = Some prog' \<and> jitfix l_jump prog' l_pc = Some prog \<Longrightarrow> jitfix (a#l_jump) l_bin0 l_pc = Some prog"
  by (metis (no_types, lifting) jitfix.elims jitfix.simps(1) jitfix.simps(2) option.case_eq_if option.discI option.inject)

lemma jit_fix_not_change_length:
  "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>
  length l_bin0 = length prog"
proof(induct l_jump arbitrary:l_bin0 l_pc prog)
  case Nil
  then show ?case by auto
next
  case (Cons a l_jump)
  assume assm0:"jitfix (a#l_jump) l_bin0 l_pc = Some prog"
  have "jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow> length l_bin0 = length prog" using Cons by blast
  have "\<exists> prog'. jitfix [a] l_bin0 l_pc = Some prog' \<and> jitfix l_jump prog' l_pc = Some prog" using jitfix_induct assm0 by simp 
  then obtain prog' where b0_0:"jitfix [a] l_bin0 l_pc = Some prog' \<and> jitfix l_jump prog' l_pc = Some prog" by auto
  hence b0_1:"jitfix [a] l_bin0 l_pc = Some prog'" by auto
  hence b0:"length prog' = length prog" using Cons b0_0 by blast 
  have b1:"length prog' = length l_bin0" 
    using b0_1 assm0 jitfix.simps apply(unfold Let_def get_updated_l_bin_def u8_list_of_i32_def,simp_all)
    apply(split if_splits,simp_all)
    apply(cases "l_pc ! unat (snd a)",simp_all)
    subgoal for aa b
      apply(cases "x64_decode (fst (l_pc ! nat (fst a))) l_bin0",simp_all)
       subgoal for ab apply(cases ab,simp_all)
        subgoal for ac ba
          apply(cases ba,simp_all)
           apply(cases "x64_decode (fst (l_pc ! nat (fst a)) + ac) l_bin0",simp_all)
          subgoal for x141 x142 ad apply(cases ad,simp_all)
            subgoal for ae bb apply(cases bb,simp_all) apply(unfold get_updated_l_bin_def x64_encode_def u8_list_of_u32_def bitfield_insert_u8_def,simp_all)
              subgoal for x131 x132               
                by (smt (z3) length_list_update)
              done
            done
          subgoal for x21a apply(unfold get_updated_l_bin_def x64_encode_def u8_list_of_u32_def bitfield_insert_u8_def,simp_all)
            by (smt (z3) length_list_update)
          done
        done
      done
    done
  then show ?case using Cons b0 b1 by argo
qed


(*lemma hh:
  "prog = x64_bin_update (length u8_list) l_bin0 xpc u8_list \<Longrightarrow>
  u8_list = x64_encode ins \<Longrightarrow>
  x64_decode xpc l_bin0 = Some (len,ins) \<Longrightarrow>
  x64_decode xpc prog = Some (len,ins)"
  sorry*)


lemma one_steps_equiv_layer3:
  "fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = fxst' \<Longrightarrow>
  xst = Next xpc xrs xm xss \<Longrightarrow>
  fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>  
  jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  well_formed_prog lt \<Longrightarrow>
  last_fix_sem 1 prog xst = fst' \<Longrightarrow>
  match_state2 fst' fxst'"
proof-
  assume a0:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = fxst'" and
  a1:"fxst' = Next xpc'' xrs'' xm'' xss''" and
  a2:"jitfix l_jump l_bin0 l_pc = Some prog" and
  a3:"xst = Next xpc xrs xm xss" and
  a4:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and
  a5:"well_formed_prog lt" and
  a7:"last_fix_sem 1 prog xst = fst'"

  have b0_1:"fxst' = fix_bpf_one_step (l_bin0,l_pc,l_jump) xst"
    using a0 by simp
  have c0_0:"fxst' = (case x64_decode xpc l_bin0 of 
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
                          (exec_instr (Pjcc cond (of_nat(fst (l_pc!(unat npc)))-(of_nat (xpc+sz+1)))) sz xpc xrs xm xss))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc xrs xm xss) |
                  _ \<Rightarrow> Stuck )"
          using b0_1 a3 by(unfold fix_bpf_one_step_def Let_def,simp_all) 
  thus ?thesis 
  proof(cases "\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d)")
    case True
    then obtain sz d where b1:"x64_decode xpc l_bin0 = Some(sz, Pcall_i d)" by auto
    have c0:"fxst' = (let v = find_target_pc_in_l_pc2 l_pc xpc 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss)))" using b1 c0_0 by simp
    
    hence "find_target_pc_in_l_pc2 l_pc xpc 0 \<noteq> None" using a1
      using option.simps(4) by fastforce 
    hence "\<exists> pc. find_target_pc_in_l_pc2 l_pc xpc 0 = Some pc" by simp
    then obtain pc where c1:"find_target_pc_in_l_pc2 l_pc xpc 0 = Some pc" by auto
    hence c2_0:"find_target_pc_in_l_pc l_jump pc \<noteq> None" using c0 a1
      using option.simps(4) by fastforce 
    hence "\<exists> npc. find_target_pc_in_l_pc l_jump pc = Some npc" by force 
    then obtain npc where c2:"find_target_pc_in_l_pc l_jump pc = Some npc" by auto
    have c3:"fxst' = exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss"
      using c0 c1 c2 by simp

    hence d0:"(int pc,npc) \<in> set l_jump" using c1 c2 search_l_jump
      by (metis a4 distinct.simps(1) init_second_layer_def is_increase_list_empty l_jump_is_distinct list.simps(8))
    have "l_bin0 \<noteq> []"
      by (metis c2_0 a2 find_target_pc_in_l_pc.simps(1) jitfix.elims option.simps(3)) 
    hence "jitfix [(int pc,npc)] l_bin0 l_pc = (let res = get_updated_l_bin (int pc,npc) l_bin0 l_pc in case res of None \<Rightarrow> None | 
                                                        Some l' \<Rightarrow> Some l')" by auto
    hence d1:"jitfix [(int pc,npc)] l_bin0 l_pc = get_updated_l_bin (int pc,npc) l_bin0 l_pc" 
      using a2 by(cases "get_updated_l_bin (int pc,npc) l_bin0 l_pc",simp_all)
    let "?prog" = "jitfix [(int pc,npc)] l_bin0 l_pc"
    have d2:"?prog = (let fix_begin_addr = fst (l_pc!pc); 
        (target_begin_addr,num2) = l_pc!(unat npc) in 
        (case x64_decode fix_begin_addr l_bin0 of 
              Some(sz, Pcall_i _) \<Rightarrow> let u8_list = x64_encode (Pcall_i (of_nat target_begin_addr)) in
                                     Some (x64_bin_update (length u8_list) l_bin0 fix_begin_addr u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = fix_begin_addr+sz in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l_bin0 loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"
      using get_updated_l_bin_def d1 by auto
    have d1_0_0:"\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> snd(snd (lt!idx)) \<noteq> []" using well_formed_prog_def a5 by blast 
    hence d1_0_1:"is_increase_list_l_pc l_pc l_bin0" 
       using l_pc_elem_increases init_second_layer_def is_increase_list_l_pc_def by (metis a4 less_nat_zero_code list.size(3))  
    hence d1_0_2:"distinct (map fst l_pc)" using l_pc_is_distinct init_second_layer_def a4 d1_0_0
       by (metis distinct.simps(1) is_increase_list_l_pc_def less_nat_zero_code list.simps(8) list.size(3)) 
     have d1_0_3:"pc < length l_pc" sorry
    have d2_1:"fst (l_pc!pc) = xpc" using l_pc_index_corr2 c1 d1_0_0 d1_0_1 d1_0_2 d1_0_3 by blast 
    have d2_2:"(fst (l_pc!pc)) = xpc" using d2_1 by presburger     
    let "?target_begin_addr" = "fst(l_pc!(unat npc))"
    have "?prog = (
        (case x64_decode xpc l_bin0 of 
              Some(sz, Pcall_i _) \<Rightarrow> let u8_list = x64_encode (Pcall_i (of_nat ?target_begin_addr)) in
                                     Some (x64_bin_update (length u8_list) l_bin0 xpc u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = xpc+sz in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat ?target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l_bin0 loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"
      using d2_1 d2_2 d2 by (simp add: case_prod_beta) 
    hence d3:"?prog = (let u8_list = x64_encode (Pcall_i (of_nat ?target_begin_addr)) in
                                     Some (x64_bin_update (length u8_list) l_bin0 xpc u8_list))"
      using b1 by(cases "x64_decode xpc l_bin0",simp_all)
    
    let "?u8_list" = "(of_nat ?target_begin_addr)"
    let "?len_u8_list" = "length(x64_encode (Pcall_i (of_nat ?target_begin_addr)))"
    have "\<exists> someprog. ?prog = Some someprog" using a2 by (meson d3) 
    then obtain someprog where d4:"?prog = Some someprog" by auto
    hence d4_1:"Some someprog = Some (x64_bin_update (length (x64_encode (Pcall_i ?u8_list))) l_bin0 xpc (x64_encode (Pcall_i ?u8_list)))"
      using d4 d3 by metis 
    have "last_fix_sem 1 someprog xst = (x64_sem 1 someprog xst)" using last_fix_sem_def by blast
    hence d5_1:"last_fix_sem 1 someprog xst = (case x64_decode xpc someprog of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
       (exec_instr ins sz xpc xrs xm xss))" using a3
      by (simp add: option.case_eq_if)  
(*
lemma x64_bin_update_decode_incode_consistency:
  "Some someprog = Some (x64_bin_update (length (x64_encode ins)) l_bin0 xpc (x64_encode ins)) \<Longrightarrow>
  x64_decode xpc someprog = Some (length (x64_encode ins),ins)"
  sorry
*)
    have "xpc + ?len_u8_list < length l_bin0" sorry
    hence d5:"x64_decode xpc someprog = Some (?len_u8_list,Pcall_i ?u8_list)" 
      using x64_encode_x64_decode_same d4_1 by blast
    hence "?len_u8_list = sz" using b1 d5 sorry
    (*exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc xrs xm xss"*)
    hence d5_2:"last_fix_sem 1 someprog xst = (exec_instr (Pcall_i ?u8_list) sz xpc xrs xm xss)"
      using d5_1 d5 by simp
    hence dn:"last_fix_sem 1 someprog xst = fxst'" using d5_2 c3 by metis

    have e0:"last_fix_sem 1 prog xst = (case x64_decode xpc prog of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
       (exec_instr ins sz xpc xrs xm xss))" using  a3 last_fix_sem_def by (simp add: option.case_eq_if)  

    have e1:"x64_decode xpc someprog = x64_decode xpc prog" 
      using x64_bin_update_is_disjoint a2 d0 d1 d3 d5 d4_1 by (smt (verit)) 
    have e2:"last_fix_sem 1 prog xst = (exec_instr (Pcall_i ?u8_list) sz xpc xrs xm xss)"
      using e0 e1 d5_1 d5_2 by argo 
    
    then show ?thesis using e2 dn match_state2_def a1 a7 d5_2 by fastforce 
  next
    case False
    have b0:"\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))" using False by simp
    then show ?thesis 
    proof(cases "\<exists> num cond d. x64_decode xpc l_bin0 = Some(num, Pjcc cond d)")
      case True 
      then obtain sz cond d where b1:"x64_decode xpc l_bin0 = Some(sz, Pjcc cond d)" by auto
      have c0:"fxst' = (let v = find_target_pc_in_l_pc2 l_pc (xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_nat(fst (l_pc!(unat npc)))-(of_nat (xpc+sz+1)))) sz xpc xrs xm xss))))"
        using c0_0 b1 by simp
      have "\<exists> pc. find_target_pc_in_l_pc2 l_pc (xpc-3) 0 = Some pc"
        using c0 a1 option.simps(4) by fastforce 
      then obtain pc where c1:"find_target_pc_in_l_pc2 l_pc (xpc-3) 0 = Some pc" by auto
      have "\<exists> npc. find_target_pc_in_l_pc l_jump pc = Some npc"
        using c0 c1 a1 option.exhaust_sel by fastforce
      then obtain npc where c2:"find_target_pc_in_l_pc l_jump pc = Some npc" by auto
      have c3:"fxst' = (exec_instr (Pjcc cond (of_nat(fst (l_pc!(unat npc)))-(of_nat (xpc+sz+1)))) sz xpc xrs xm xss)"
        using c0 c2 c1 by force

      have d0:"(int pc,npc) \<in> set l_jump" using c2 search_l_jump
        by (metis a4 distinct.simps(1) init_second_layer_def is_increase_list_empty l_jump_is_distinct list.simps(8)) 
      have d0_1:"l_bin0 \<noteq> []" using a2
        by (metis c2 find_target_pc_in_l_pc.simps(1) jitfix.simps(2) list.exhaust option.distinct(1)) 
       hence "jitfix [(int pc,npc)] l_bin0 l_pc = (let res = get_updated_l_bin (int pc,npc) l_bin0 l_pc in case res of None \<Rightarrow> None | 
                                                        Some l' \<Rightarrow> Some l')" by auto
    hence d1:"jitfix [(int pc,npc)] l_bin0 l_pc = get_updated_l_bin (int pc,npc) l_bin0 l_pc" 
      using a2 by(cases "get_updated_l_bin (int pc,npc) l_bin0 l_pc",simp_all)
    let "?prog" = "jitfix [(int pc,npc)] l_bin0 l_pc"
    have d2:"?prog = (let fix_begin_addr = fst (l_pc!pc); 
        (target_begin_addr,num2) = l_pc!(unat npc) in 
        (case x64_decode fix_begin_addr l_bin0 of 
              Some(sz, Pcall_i _) \<Rightarrow> let u8_list = x64_encode (Pcall_i (of_nat target_begin_addr)) in
                                     Some (x64_bin_update (length u8_list) l_bin0 fix_begin_addr u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = fix_begin_addr+sz in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l_bin0 loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"
      using get_updated_l_bin_def d1 by auto

    have d3_1:"?prog \<noteq> None" using x64_bin_update_is_disjoint2 a2 d0 by blast
    have d1_0_0:"\<forall> idx. idx \<ge>0 \<and> idx < length lt \<longrightarrow> snd(snd (lt!idx)) \<noteq> []" using well_formed_prog_def a5 by blast 
    hence d1_0_1:"is_increase_list_l_pc l_pc l_bin0" 
       using l_pc_elem_increases init_second_layer_def is_increase_list_l_pc_def by (metis a4 less_nat_zero_code list.size(3))  
    hence d1_0_2:"distinct (map fst l_pc)" using l_pc_is_distinct init_second_layer_def a4 d1_0_0
       by (metis distinct.simps(1) is_increase_list_l_pc_def less_nat_zero_code list.simps(8) list.size(3)) 
    have d1_0_3:"pc < length l_pc" sorry
    have d3_0_0:"fst (l_pc!pc) = xpc-3"
      using c1 l_pc_index_corr2 d1_0_1 d1_0_2 d1_0_3 by blast 
    hence d3_0_1:"fst (l_pc!pc)+3 = (xpc-3)+3" using d3_0_0 by presburger 
    moreover have d3_0_2:"xpc-3\<ge>0" by blast
    hence d3_0:"fst (l_pc!pc) +3 = xpc" using d3_0_1 d3_0_2 sorry
    have d3_2:"x64_decode (fst (l_pc!pc)) l_bin0 \<noteq> None" using d2 a2 d0_1 d3_1 by(cases "x64_decode (fst (l_pc!pc)) l_bin0",simp_all)
    hence "(\<exists> sz d. x64_decode (fst (l_pc!pc)) l_bin0 = Some(sz, Pcall_i d)) \<or> (\<exists> sz src dst. x64_decode (fst (l_pc!pc)) l_bin0 = Some(sz, Pcmpq_rr src dst))"
      using d2 a2 d0_1 d3_1 apply(cases "x64_decode (fst (l_pc!pc)) l_bin0",simp_all)
      subgoal for a apply(cases "get_updated_l_bin (int pc, npc) l_bin0 l_pc",simp_all)
        subgoal for aa apply(cases "l_pc ! unat npc",simp_all)
          subgoal for ab b apply(cases a,simp_all)
            subgoal for ac ba apply(cases ba,simp_all)
              done
            done
          done
        done
      done
    then obtain sz1 d sz2 src dst where d4:"x64_decode (fst (l_pc!pc)) l_bin0 = Some(sz1, Pcall_i d) \<or> x64_decode (fst (l_pc!pc)) l_bin0 = Some(sz2, Pcmpq_rr src dst)" by auto
    thus ?thesis 
    proof(cases "x64_decode (fst (l_pc!pc)) l_bin0 = Some(sz2, Pcmpq_rr src dst)")
      case True
      have d5:"?prog = (
        let (target_begin_addr,num2) = l_pc!(unat npc) in 
        (let loc = (fst (l_pc!pc))+sz2 in 
                    (case x64_decode loc l_bin0 of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l_bin0 loc u8_list))))"
        using d2 d3_1 True d0_1 d3_2 d4 apply(unfold Let_def,simp_all)
        apply(cases "get_updated_l_bin (int pc, npc) l_bin0 l_pc",simp_all)
        subgoal for a  apply(cases "l_pc ! unat npc",simp_all)
          subgoal for aa b apply(cases "x64_decode (fst (l_pc!pc)) l_bin0",simp_all)
            subgoal for ab apply(unfold Let_def,simp_all)
              apply(cases "x64_decode (fst (l_pc ! pc) + sz2) l_bin0",simp_all)
              subgoal for ac apply(cases ac,simp_all)
                subgoal for ad ba apply(cases ba,simp_all)
                  done
                done
              done
            done
          done
        done
      let "?target_begin_addr" = "fst(l_pc!(unat npc))"

      let "?loc" = "(fst (l_pc!pc))+sz2"
      have "sz2 = 3" sorry
      hence d5_1:"?loc = xpc" using d3_0 by force  
      let "?offset" = "((of_nat ?target_begin_addr)::i32) - ((of_nat (xpc+sz)+1)::i32)"
      let "?u8_list" = "Pjcc cond (ucast ?offset)"
      let "?len_u8_list" = "length(x64_encode (Pjcc cond (ucast ?offset)))"

      have d6:"?prog = Some (x64_bin_update (length (x64_encode ?u8_list)) l_bin0 ?loc (x64_encode ?u8_list))"
        using d5 d0_1 d3_1 b1 d5_1 apply(unfold Let_def,simp_all)
        apply(cases "get_updated_l_bin (int pc, npc) l_bin0 l_pc",simp_all)
        subgoal for a apply(unfold Let_def,simp_all)
          apply(cases "l_pc ! unat npc",simp_all)
          done
        done
        
      have "\<exists> someprog. ?prog = Some someprog" using a2 d3_1 by auto
      then obtain someprog where d4:"?prog = Some someprog" by auto
      have "xpc + ?len_u8_list < length l_bin0" sorry
      hence d7:"x64_decode xpc someprog = Some (?len_u8_list,?u8_list)"
        using d4 d5_1 d6 x64_encode_x64_decode_same2 by auto 
     
      have d8_1:"last_fix_sem 1 someprog xst = (x64_sem 1 someprog xst)" using last_fix_sem_def by blast
      hence d8_2:"last_fix_sem 1 someprog xst = (case x64_decode xpc someprog of
        None \<Rightarrow> Stuck |
        Some (sz, ins) \<Rightarrow>
         (exec_instr ins sz xpc xrs xm xss))" using a3
        by (simp add: option.case_eq_if)  

      have "?len_u8_list = sz" sorry
                                (* "fxst' = (exec_instr (Pjcc cond (of_nat(fst (l_pc!(unat npc)))-(of_nat (xpc+sz+1)))) sz xpc xrs xm xss)"*)
      hence dn:"last_fix_sem 1 someprog xst = ((exec_instr (Pjcc cond (ucast((of_nat ?target_begin_addr)::i32) - ((of_nat (xpc+sz)+1)::i32))) sz xpc xrs xm xss))" 
        using d7 d8_2 last_fix_sem_def by force 

      
      have e0:"last_fix_sem 1 prog xst = (case x64_decode xpc prog of
      None \<Rightarrow> Stuck |
      Some (sz, ins) \<Rightarrow>
       (exec_instr ins sz xpc xrs xm xss))" using a3 last_fix_sem_def by (simp add: option.case_eq_if)  

      have e1:"x64_decode xpc someprog = x64_decode xpc prog" using d7 a2 d0 d4 d5_1 d6 x64_bin_update_is_disjoint by presburger 

      have e2:"last_fix_sem 1 prog xst = (exec_instr (Pjcc cond (ucast((of_nat ?target_begin_addr)::i32) - ((of_nat (xpc+sz)+1)::i32))) sz xpc xrs xm xss)"
        using e0 e1 dn d8_2 by argo  

      then show ?thesis using match_state2_def c3 dn d4
        by (metis (mono_tags, lifting) a1 a7 of_nat_1 of_nat_add outcome.distinct(1) ucast_id) 
    next
      case False
      then show ?thesis sorry
    qed
    next
      case False
       have b0_0:"(\<not>(\<exists> num d. x64_decode xpc l_bin0 = Some(num, Pcall_i d))) \<and> (\<not> (\<exists> num cond d. x64_decode xpc l_bin0 = Some(num, Pjcc cond d)))"
          using False b0 by blast
        
       have b0_2:"x64_decode xpc l_bin0 \<noteq> None" 
        proof(rule ccontr)
          assume assm:"\<not> (x64_decode xpc l_bin0 \<noteq> None)"
          have "x64_decode xpc l_bin0 = None" using assm by blast   
          hence c0:"fxst' = Stuck" 
            using b0_0 b0_1 fix_bpf_one_step_def a3 by(cases "x64_decode xpc l_bin0",simp_all) 
          thus "False" using a1 by auto
        qed

        hence "\<exists> sz ins. x64_decode xpc l_bin0 = Some(sz,ins)" by auto
        then obtain sz ins where b2:"x64_decode xpc l_bin0 = Some(sz,ins)" by auto
        hence c1:"fxst' = exec_instr ins sz xpc xrs xm xss" 
          using b2 b0_0 c0_0 apply(cases "x64_decode xpc l_bin0",simp_all) by(cases ins,simp_all)
        have d0:"x64_decode xpc prog = Some(sz,ins)"
          using jit_fix_not_change b2 a2 b0_0 by blast
        hence d1:"fst' = (exec_instr ins sz xpc xrs xm xss)"
          using a3 a7 apply(unfold last_fix_sem_def) by(cases "x64_decode xpc prog",simp_all)
        thus ?thesis using c1 d1 match_state2_def a1 by fastforce
        qed
      qed
    qed



lemma n_steps_equiv_layer3:
  "fix_bpf_sem n (l_bin0,l_pc,l_jump) xst = fxst' \<Longrightarrow>
  xst = Next xpc xrs xm xss \<Longrightarrow>
  fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = Some prog \<Longrightarrow>  
  jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  well_formed_prog lt \<Longrightarrow>
  last_fix_sem n prog xst = fst' \<Longrightarrow>
  match_state2 fst' fxst'"
proof(induct n arbitrary:l_bin0 l_pc l_jump xst fxst' xpc xrs xm xss xpc'' xrs'' xm'' xss'' prog lt fst')
  case 0 
  then show ?case using last_fix_sem_def match_state2_def by auto 
    (*by (smt (verit, ccfv_threshold) flat_bpf_sem.simps(1) last_fix_sem_def match_state2_def outcome.simps(4) snd_conv x64_sem.simps(1))*) 
next
  case (Suc n)
  assume assm0:"fix_bpf_sem (Suc n) (l_bin0,l_pc,l_jump) xst = fxst'" and
    assm1:"xst = Next xpc xrs xm xss" and
    assm2:"fxst' = Next xpc'' xrs'' xm'' xss''" and
    assm3:"jitfix l_jump l_bin0 l_pc = Some prog" and
    assm4:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and
    assm5:"well_formed_prog lt" and
    assm6:"last_fix_sem (Suc n) prog xst = fst'"
 
  have "\<exists> next_f. fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = next_f" by blast
  then obtain next_f where b0:"fix_bpf_sem 1 (l_bin0,l_pc,l_jump) xst = next_f" by auto
  have "\<exists> xpc' xrs' xm' xss'. next_f = Next xpc' xrs' xm' xss'"
    using assm0 assm2 b0 by (metis One_nat_def err_is_still_err4 fix_bpf_sem.simps(1) fix_bpf_sem.simps(2) outcome.exhaust)
  then obtain xpc' xrs' xm' xss' where b2:"next_f = Next xpc' xrs' xm' xss'" by auto

  have "\<exists> next_s. last_fix_sem 1 prog xst = next_s" by blast
  then obtain next_s where b1:"last_fix_sem 1 prog xst = next_s" by auto
  hence bn:"match_state2 next_s next_f"
    using one_steps_equiv_layer3 assm0 assm2 assm3 assm5 b0 b1 b2 match_state2_def assm1 assm4 by blast 
 
  have b3:"fix_bpf_sem n (l_bin0,l_pc,l_jump) next_f = fxst'" using assm0 b0 by auto
    
  have b4:"last_fix_sem n prog next_s = fst'" using b1 assm6 last_fix_sem_def
    by (metis Suc.prems(2) plus_1_eq_Suc x64_sem_add) 

  then show ?case using match_state2_def b3 b4 b2
    by (metis Suc.hyps Suc.prems(3) assm3 assm4 assm5 bn) 
qed


lemma n_steps_equiv:
  assumes assm0:"perir_sem n lt (pc,xxst) = xxst'" and
  assm1:"xxst = Next xpc xrs xm xss" and
  assm2:"snd xxst' = Next xpc' xrs' xm' xss'" and
  assm3:"JITFlattern_def.match_state (pc,fxst) (pc,xxst)" and
  assm4:"lt \<noteq> []" and
  assm5:"well_formed_prog lt"and

  assm6:"jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump)" and
  assm7:"flat_bpf_sem n (l_bin0,l_pc,l_jump) (pc,fxst) = fxst'" and
  assm8:"snd fxst' = Next xpc'' xrs'' xm'' xss''" and

  assm9:"jitfix l_jump l_bin0 l_pc = Some prog" and
  assm10:"jitper insns = Some lt" and
  assm11:"jitper insns = Some lt"
  shows "\<exists> num fst'. last_fix_sem num prog fxst = fst' \<and> match_state1 fst' (snd xxst')" 
proof-
  have b0:"JITFlattern_def.match_state fxst' xxst'" 
    using n_steps_equiv_layer1 assm3 assm0 assm1 assm2 assm4 assm5 assm11 assm6 assm7 assm8 match_mem_def assm10 by simp
  have "\<exists> xpc1 xrs xm xss. fxst = Next xpc1 xrs xm xss" 
    using JITFlattern_def.match_state_def assm1 assm3 
    apply(cases xxst,simp_all) 
    apply(cases fxst,simp_all)
    done
  then obtain xpc1 xrs xm xss where b1:"fxst = Next xpc1 xrs xm xss" by auto
  have b2:"\<exists> num fst'. last_fix_sem num prog fxst = fst' \<and> match_state2 fst' (snd fxst')" 
    using n_steps_equiv_layer2 assm7 assm9 b1 assm8 assm6 assm5 by (metis assm11 match_state2_def n_steps_equiv_layer3)
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




end