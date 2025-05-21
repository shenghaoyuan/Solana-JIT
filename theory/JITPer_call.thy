theory JITPer_call
  imports JITPer_aux BitsOpMore3
begin

lemma mem_is_not_changed_by_call:
  "prog!(unat pc1) = BPF_CALL_IMM src imm \<Longrightarrow> 
  s2 = sbpf_step prog s1 \<Longrightarrow> s1 = (SBPF_OK pc1 rs1 m1 ss1) \<Longrightarrow> 
  s2 = (SBPF_OK pc2 rs2 m2 ss2) \<Longrightarrow> m1 = m2"
  apply(cases "prog!(unat pc1)", simp_all)
  apply(split if_splits,simp_all)
  apply(split if_splits,simp_all)
  apply(unfold eval_call_imm_def Let_def)
  apply(unfold push_frame_def Let_def update_stack_def)
  apply(split if_splits, simp_all)
  done

lemma call_reg_subgoal_aux1:
  "s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_CALL_IMM src imm \<Longrightarrow> 
  rs' BR10 = (stack_pointer ss)"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x171 
    apply(cases "eval_call_imm src imm rs ss pc",simp_all)
    subgoal for a apply(cases a,simp_all )
      apply(unfold eval_call_imm_def push_frame_def Let_def,simp_all)
      apply(cases "update_stack [eval_reg BR6 rs, eval_reg BR7 rs, eval_reg BR8 rs, eval_reg BR9 rs] (eval_reg BR10 rs) (pc + (1::64 word)) ss",simp_all)
      apply(unfold update_stack_def Let_def eval_reg_def, simp_all)
      apply(split if_splits,simp_all) by auto
    done
  done

lemma call_reg_subgoal_aux2:
  "s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_CALL_IMM src imm \<Longrightarrow> 
  \<forall> r. r\<noteq>BR10 \<longrightarrow> rs r = rs' r"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x171 
    apply(cases "eval_call_imm src imm rs ss pc",simp_all)
    subgoal for a apply(cases a,simp_all )
      apply(unfold eval_call_imm_def push_frame_def Let_def,simp_all)
      apply(cases "update_stack [eval_reg BR6 rs, eval_reg BR7 rs, eval_reg BR8 rs, eval_reg BR9 rs] (eval_reg BR10 rs) (pc + (1::64 word)) ss",simp_all)
      apply(unfold update_stack_def Let_def eval_reg_def, simp_all)
      apply(split if_splits,simp_all) by auto
    done
  done

lemma call_reg_subgoal_aux3:"s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_CALL_IMM src imm \<Longrightarrow> 
  call_depth ss +1 \<noteq> max_call_depth"
 apply(cases "prog!(unat pc)",simp_all)
  subgoal for x171 
    apply(cases "eval_call_imm src imm rs ss pc",simp_all)
    subgoal for a apply(cases a,simp_all )
      apply(unfold eval_call_imm_def push_frame_def Let_def,simp_all)
      apply(cases "update_stack [eval_reg BR6 rs, eval_reg BR7 rs, eval_reg BR8 rs, eval_reg BR9 rs] (eval_reg BR10 rs) (pc + (1::64 word)) ss",simp_all)
      apply(unfold update_stack_def Let_def eval_reg_def, simp_all)
        by (metis option.discI)
      done
    done

  
value "((ucast ((-1)::i32))::u32)"

value "((ucast (ucast ((-1)::i32)::u32))::u64)"

lemma pc_aux1:"(u32_of_u8_list(u8_list_of_u32 x)) = Some x "
  using u32_of_u8_list_same
  by metis
  

lemma pc_aux2:"(ucast((ucast (i::i32))::u32)::u64) = ((ucast i)::u64)"
  proof-

   have n:"take_bit LENGTH(32)  (uint i) = take_bit 32 (uint i)" by auto
   have m:"take_bit LENGTH(64)  (uint i) = take_bit 64 (uint i)" by auto

  have "((ucast ((word_of_int (uint i))::u32)) :: u64)  = (((word_of_int (uint i))::u64))"
    using n m 
    by (smt (verit, best) bintr_uint len_signed nat_le_linear numeral_Bit0_eq_double numeral_le_iff
         of_int_uint semiring_norm(69) take_bit_tightened_less_eq_int unsigned_ucast_eq)
   then show ?thesis by auto
 qed

lemma call_reg_subgoal_aux4:"s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_CALL_IMM src imm \<Longrightarrow> 
  l = (ucast imm) \<Longrightarrow> 
  pc' = l"
 apply(cases "prog!(unat pc)",simp_all)
  subgoal for x171 
    apply(cases "eval_call_imm src imm rs ss pc",simp_all)
    subgoal for a apply(cases a,simp_all )
      apply(unfold eval_call_imm_def push_frame_def Let_def,simp_all)
      apply(cases "update_stack [eval_reg BR6 rs, eval_reg BR7 rs, eval_reg BR8 rs, eval_reg BR9 rs] (eval_reg BR10 rs) (pc + (1::64 word)) ss",simp_all)
      done
    done
  done


lemma call_reg_subgoal_aux5:"Next xpc xrs' xm xss'  = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs;
                           xrs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
            let ss' = update_stack caller fp (pc+1) xss in
              (case ss' of
              Some ra \<Rightarrow> Next xpc xrs' xm ra)) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_CALL_IMM src imm \<Longrightarrow> 
  \<forall> r. xrs (IR (bpf_to_x64_reg r)) = rs r \<Longrightarrow>
  ss = xss \<Longrightarrow> 
  ss' = xss' "
 apply(cases "prog!(unat pc)",simp_all)
  subgoal for x171 
    apply(cases "eval_call_imm src imm rs ss pc",simp_all)
    subgoal for a apply(cases a,simp_all )
      apply(unfold eval_call_imm_def push_frame_def Let_def,simp_all)
      apply(cases "update_stack [eval_reg BR6 rs, eval_reg BR7 rs, eval_reg BR8 rs, eval_reg BR9 rs] (eval_reg BR10 rs) (pc + (1::64 word)) ss",simp_all)
        apply(unfold update_stack_def Let_def,simp_all)
        apply(split if_splits,simp_all)
        apply(unfold upate_x64_stack_pointer_def eval_reg_def bpf_to_x64_reg_def save_x64_frame_pointer_def save_x64_caller_def)
        apply(subgoal_tac " [xrs (IR R12), xrs (IR R13), xrs (IR R14), xrs (IR R15)] =  [rs BR6, rs BR7, rs BR8, rs BR9]")
         apply(subgoal_tac "xrs (IR RBP) = rs BR10")
          apply presburger
        using bpf_to_x64_reg_def  bpf_to_x64_reg_corr
         apply (metis bpf_ireg.simps(121))
        by (metis bpf_ireg.simps(117) bpf_ireg.simps(118) bpf_ireg.simps(119) bpf_ireg.simps(120))
      done
    done

lemma call_imm_one_step:
  assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_CALL_IMM src imm"
shows "\<exists> xst'. perir_sem 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
proof-
  have b0:"\<forall> r. r\<noteq>BR10 \<longrightarrow> rs r = rs' r" using a0 a1 a2 a6 a8 call_reg_subgoal_aux2 by simp 
  have b1:"rs' BR10 = (stack_pointer ss)" using a0 a1 a2 a6 a8 call_reg_subgoal_aux1 by simp


  let "?bpf_ins" = "prog!(unat pc)"
  let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
  have c1_0:"?l_bin = snd (snd (the (per_jit_call_reg src imm)))" using a8 per_jit_ins_def by auto
   have c0:"?l_bin = snd (snd (the (per_jit_call_reg src imm)))" using a8 per_jit_ins_def by fastforce
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto
  have c2:"l = ?l_bin" using a6 c0 a5 aux5 c_aux by fastforce
      
  let "?perir_step" = "perir_sem 1 x64_prog (pc,xst)"
  let "?st" = "snd ?perir_step"
  have c2_1:"?st = snd (perir_step x64_prog (pc,xst))" 
      by (metis One_nat_def prod.collapse perir_sem.simps(1) perir_sem.simps(2))

  have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
  hence c3:"x64_prog!(unat pc) = the (per_jit_call_reg src imm)" using a8 per_jit_ins_def by simp
  have c3_0:"per_jit_call_reg src imm = Some (num,off,l)" using c_aux c3
    by (simp add: per_jit_call_reg_def) 


  have c4_2:"l = x64_encode (Pcall_i 0)" using per_jit_call_reg_def c3_0 by simp
  hence c4_0:"off = ucast imm" using per_jit_call_reg_def c3_0 by simp

  have c4:"(l!0 = 0xe8)" using c_aux c3 c3_0 apply(unfold per_jit_call_reg_def x64_encode_def)
    apply(cases "Pcall_i (ucast imm)",simp_all) 
    subgoal for x16 by auto[1]
    done
  have "length l = 5" using c4_2 apply(unfold x64_encode_def Let_def,simp_all) apply(unfold u8_list_of_u32_def,simp_all) done
  hence c4_1:"x64_decode 0 l = Some (5,Pcall_i 0)" using c4 c4_2 x64_encode_decode_consistency list_in_list_prop by blast
  hence c4_3:"x64_decode 0 l \<noteq> Some(1,Pret)" by simp
  have c5:"?perir_step = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs;
                           xrs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
            let ss' = update_stack caller fp (pc+1) xss in
              (case ss' of None \<Rightarrow> (pc, Stuck) | 
              Some ra \<Rightarrow> (off, Next xpc xrs' xm ra)))" 
    using c4 c2_1 perir_step_def a3 c_aux c_aux c4_1 c4_3
    by (smt (verit) One_nat_def case_prod_conv fst_conv option.case_eq_if outcome.simps(4) perir_sem.simps(1) perir_sem.simps(2) snd_conv) 
    

  have d1_1:"xss = ss" using match_state_def a0 a1 a2 a3 a4 by auto
  have d2_0:"call_depth xss +1 \<noteq>  max_call_depth" using c5 update_stack_def call_reg_subgoal_aux3 a0 a1 a2 a6 d1_1 using a8 by auto
  have d2_1:"?st \<noteq> Stuck" using d2_0 c5 by (simp add: update_stack_def) 
  
  have "\<exists> xrs1 xss1. ?st = Next xpc xrs1 xm xss1" using c5 d2_1
      by (metis (no_types, lifting) option.case_eq_if snd_conv)
  then obtain xrs1 xss1 where c6:"?st = Next xpc xrs1 xm xss1" by auto
  have c7:"Next xpc xrs1 xm xss1 =  (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs;
                           xrs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
            let ss' = update_stack caller fp (pc+1) xss in
              (case ss' of
              Some ra \<Rightarrow> Next xpc xrs' xm ra))" using c5 c6 d2_1 
      by (metis (no_types, lifting) option.case_eq_if snd_conv)

  
  have d0:"match_mem m' xm " using mem_is_not_changed_by_call a4 match_state_def a0 a1 a2 a8 a3 by fastforce
    
  have d1_0:"\<forall> r. xrs (IR (bpf_to_x64_reg r)) = rs r" using match_state_def a4 a0 a1 a2 a3 match_reg_def by simp
   
  have d1_2:"xrs1 (IR RBP) = (stack_pointer xss)" using c5 upate_x64_stack_pointer_def c6 
       fun_upd_apply option.case_eq_if outcome.inject snd_conv by (metis (no_types, lifting) d2_1) 
  have d1_3:"xrs1 (IR (bpf_to_x64_reg BR10)) = rs' BR10" using call_reg_subgoal_aux1 a0 a1 a2 a6 d1_1 d1_2 b1 bpf_to_x64_reg_def bpf_to_x64_reg_corr by simp
  have d1_4:"\<forall> r. r\<noteq>BR10 \<longrightarrow> xrs  (IR (bpf_to_x64_reg r)) = xrs1  (IR (bpf_to_x64_reg r))" using c7 upate_x64_stack_pointer_def bpf_to_x64_reg_def bpf_to_x64_reg_corr
    by (metis (mono_tags, lifting) bpf_ireg.simps(121) c5 d2_1 fun_upd_other option.case_eq_if outcome.inject preg.inject(1) snd_conv) 
  hence d1:"match_reg rs' xrs1" using match_reg_def b0 d1_3 d1_4 d1_1 d1_0 match_reg_def by metis

  have d2:"xss1 = ss'" using c7 a0 a1 a2 call_reg_subgoal_aux5 d1_0 d1_1 a6 a8 by blast


  have d3_0:"xrs (IR RSP) = xrs1 (IR RSP)" using c7 upate_x64_stack_pointer_def c6 snd_conv 
    by (metis (no_types, lifting) c5 d2_1 fun_upd_other ireg.distinct(151) option.case_eq_if outcome.inject preg.inject(1)) 
  have d3:"match_stack xrs1" using d3_0 match_stack_def a4 match_state_def a3 a1 by auto

  have d4:"match_state s' (pc', ?st)" using a4 match_state_def match_mem_def match_stack_def match_reg_def c6 a0 a1 a2 a3 d0 d1 d2 d3 by force
                                                                                                      
  have "fst ?perir_step = off" using c5 by (metis (no_types, lifting) d2_1 option.case_eq_if split_pairs)
  hence "fst ?perir_step = pc'" using c4_0 call_reg_subgoal_aux4 a0 a1 a2 a6 a8 c_aux by blast
    thus ?thesis using d4 by (metis split_pairs)
  qed


end 
