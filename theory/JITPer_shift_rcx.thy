theory JITPer_shift_rcx
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma shiftq_lsh_one_step_match_reg:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0  \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) = RCX \<Longrightarrow>
     match_reg rs' (xrs (IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg dst)) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))))"
  apply (simp add: match_state_def match_reg_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  by (metis bpf_to_x64_reg_corr)
  

lemma shiftq_lsh_one_step_match_mem:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
   x64_encode (Pshlq_r (bpf_to_x64_reg dst)) ! Suc (0::nat) \<noteq> (57::8 word) \<Longrightarrow> match_mem m' xm"
  apply (simp add: match_state_def match_mem_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  done

lemma shiftq_lsh_one_step_match_stack:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    x64_encode (Pshlq_r (bpf_to_x64_reg dst)) ! Suc (0::nat) \<noteq> (57::8 word) \<Longrightarrow>
    match_stack (xrs(IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg dst)) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))))"
  apply (simp add:match_state_def match_stack_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  using reg_rsp_consist by blast

lemma shiftq_lsh_one_step_match_stack2:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    xss = ss'"
   apply(cases"prog!(unat pc)",simp_all)
  subgoal for x91 
    apply(cases "eval_alu BPF_LSH dst (SOReg src) rs",simp_all)
    apply(unfold match_state_def,simp_all)
    done
  done



lemma shiftq_lsh_one_step:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src)" and
  a9:"(bpf_to_x64_reg dst) = RCX" and
  a10:"(bpf_to_x64_reg src) = RCX"
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"

apply simp
(* 1. as BPF_LSH generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_shift_lsh_reg64 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_shift_lsh_reg64 dst src) = (1, 0, x64_encode(Pshlq_r (bpf_to_x64_reg src)))")
       prefer 2
      subgoal using per_jit_shift_lsh_reg64_def a9 a10 by simp
      apply (subgoal_tac "(x64_encode(Pshlq_r (bpf_to_x64_reg src))) !1 \<noteq> 0x39 \<and> (x64_encode(Pshlq_r (bpf_to_x64_reg src))) !0 \<notin> {0xc3, 0xe8}")
       prefer 2 subgoal  apply(unfold x64_encode_def) 
       (* apply(cases "bpf_to_x64_reg src"; cases "bpf_to_x64_reg dst",simp_all)*)
        apply simp
        apply(unfold Let_def x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def construct_modsib_to_u8_def u8_of_bool_def) 
        apply(cases False,simp_all)
          apply(cases "and (u8_of_ireg (bpf_to_x64_reg src)) (8::8 word) \<noteq> (0::8 word)",simp_all)
        done
      unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 5 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule subst)
        apply (simp only: x64_sem.simps)
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac " x64_decode (0::nat)
            (x64_encode (Pshlq_r (bpf_to_x64_reg src)))
            =  ( Some(length (x64_encode (Pshlq_r (bpf_to_x64_reg src))), Pshlq_r (bpf_to_x64_reg src)))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pshlq_r (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal
            using list_in_list_concat list_in_list_prop by blast
          subgoal by simp
          subgoal by simp
          done
        subgoal
          apply simp
          apply (erule subst)

(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
        apply (simp add: exec_instr_def)
        apply (rule conjI)
        subgoal
          by (metis a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3)

        unfolding a1 a2
        apply (simp add: match_state_def)
        apply (rule conjI)

(* 4.1  match_reg *)
        subgoal using shiftq_lsh_one_step_match_reg a0 a1 a2 a3 a4 a6 a8 a9 a10
          by metis

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using shiftq_lsh_one_step_match_mem a0 a1 a2 a3 a4 a6 a8 a9 a10  by metis
(* 4.2  match_stack *)
        subgoal using shiftq_lsh_one_step_match_stack a0 a1 a2 a3 a4 a6 a8 a9 a10 apply simp
          using shiftq_lsh_one_step_match_stack2 a0 a1 a2 a3 a4 a6 a8 a9 a10 by (metis (no_types, lifting)) 
        done
        done
      done
    done       


lemma shiftq_lsh_one_step_match_reg1:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) = RCX \<Longrightarrow>
    (bpf_to_x64_reg src) \<noteq> RCX \<Longrightarrow>
    match_reg rs'
     ((\<lambda>a::preg.
          if a = IR RCX then xrs (IR RCX) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
          else if a = IR (bpf_to_x64_reg src) then xrs (IR RCX) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
               else if a = IR (bpf_to_x64_reg src) then xrs (IR RCX)
                    else if a = IR RCX then xrs (IR (bpf_to_x64_reg src))
                         else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else xrs a)
      (IR SP := xrs (IR SP), IR (bpf_to_x64_reg src) := xrs (IR (bpf_to_x64_reg src))))"
  apply (simp add: match_state_def match_reg_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  by (metis bpf_to_x64_reg_corr)

  

lemma shiftq_lsh_one_step_match_mem1:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) = RCX \<Longrightarrow>
    (bpf_to_x64_reg src) \<noteq> RCX \<Longrightarrow>
     storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR (bpf_to_x64_reg src)))) = Some m1 \<Longrightarrow> 
     loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR (bpf_to_x64_reg src)))) \<Longrightarrow> 
     match_mem m' m1"
   apply (simp add: match_state_def)
    apply(subgoal_tac "m = m'")
   prefer 2 
    subgoal
      apply(cases "eval_alu BPF_LSH dst (SOReg src) rs ",simp_all)
    done
    using sp_block_def match_mem_def match_mem_store_1_equiv by metis


lemma shiftq_lsh_one_step_match_stack1:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) = RCX \<Longrightarrow>
    (bpf_to_x64_reg src) \<noteq> RCX \<Longrightarrow>
    storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR (bpf_to_x64_reg src)))) = Some m1 \<Longrightarrow> 
    loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR (bpf_to_x64_reg src)))) \<Longrightarrow>
   match_stack
     ((\<lambda>a::preg.
          if a = IR RCX then xrs (IR RCX) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
          else if a = IR (bpf_to_x64_reg src) then xrs (IR RCX) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
               else if a = IR (bpf_to_x64_reg src) then xrs (IR RCX)
                    else if a = IR RCX then xrs (IR (bpf_to_x64_reg src))
                         else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else xrs a)
      (IR SP := xrs (IR SP), IR (bpf_to_x64_reg src) := xrs (IR (bpf_to_x64_reg src))))"
  apply (simp add: match_state_def match_stack_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  done

lemma encode_aux:"(x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src)))!0 \<notin> {0xc3, 0xe8}"
  subgoal apply(unfold per_jit_mul_reg64_def x64_encode_def)
    apply(unfold construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def,simp_all)
    apply(cases "and (u8_of_ireg (bpf_to_x64_reg src)) (8::8 word) \<noteq> (0::8 word)",simp_all)
    apply(unfold bpf_to_x64_reg_def)
    by(cases src,simp_all)
  done

lemma encode_aux1:"(x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src))) !1 \<noteq> 0x39"
  apply(unfold x64_encode_def) 
  apply simp
  apply(unfold Let_def x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def construct_modsib_to_u8_def u8_of_bool_def bpf_to_x64_reg_def)  
  apply(cases False,simp_all)
  apply(cases "and (u8_of_ireg (case src of BR0 \<Rightarrow> RAX | BR1 \<Rightarrow> RSI | BR2 \<Rightarrow> RDX | BR3 \<Rightarrow> RCX | BR4 \<Rightarrow> R8 | BR5 \<Rightarrow> R9 | BR6 \<Rightarrow> R12 | BR7 \<Rightarrow> R13 | BR8 \<Rightarrow> R14 | BR9 \<Rightarrow> R15 | BR10 \<Rightarrow> RBP)) (8::8 word) \<noteq> (0::8 word) ",simp_all)
   apply(cases src,simp_all)
      apply(cases " and (u8_of_ireg (case dst of BR0 \<Rightarrow> RAX | BR1 \<Rightarrow> RSI | BR2 \<Rightarrow> RDX | BR3 \<Rightarrow> RCX | BR4 \<Rightarrow> R8 | BR5 \<Rightarrow> R9 | BR6 \<Rightarrow> R12 | BR7 \<Rightarrow> R13 | BR8 \<Rightarrow> R14 | BR9 \<Rightarrow> R15 | BR10 \<Rightarrow> RBP)) (8::8 word) \<noteq> (0::8 word)",simp_all)
  done

lemma shiftq_lsh_one_step1:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src)" and
  a9:"(bpf_to_x64_reg dst) = RCX" and
  a10:"(bpf_to_x64_reg src) \<noteq> RCX"
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  
  apply simp
(* 1. as BPF_LSH generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_shift_lsh_reg64 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_shift_lsh_reg64 dst src) = (5, 0, x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src)))")
       prefer 2
      subgoal using per_jit_shift_lsh_reg64_def a9 a10 by (cases "(bpf_to_x64_reg src)",simp_all)
      apply (subgoal_tac "(x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src))) !1 \<noteq> 0x39")
       prefer 2 subgoal using encode_aux1 by blast  
    apply(subgoal_tac "(x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src)))!0 \<notin> {0xc3, 0xe8}")
    prefer 2 using encode_aux apply blast
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 5 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 4 = (5::nat)") prefer 2 subgoal by simp
        apply (erule subst)
        apply (simp only: x64_sem.simps)
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac " x64_decode (0::nat)
            (x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) @
             x64_encode (Pshlq_r (bpf_to_x64_reg src)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src)) @ x64_encode (Ppopl (bpf_to_x64_reg src)))
            =  ( Some(length (x64_encode (Ppushl_r (bpf_to_x64_reg src))), Ppushl_r (bpf_to_x64_reg src)))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode (Ppushl_r (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal
            using list_in_list_concat list_in_list_prop by blast
          subgoal by simp
          subgoal by simp
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def exec_push_def Let_def)
        apply (insert storev_stack_some [of xm "(xrs (IR SP) - u64_of_memory_chunk M64)" "xrs (IR (bpf_to_x64_reg src))"])
        apply (erule exE)
        subgoal for m1
          apply simp
(* 3.2 *)
        apply (subgoal_tac "Suc 3 = (4::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 4])
        apply (simp only: x64_sem.simps)
        apply (subgoal_tac "x64_decode (length (x64_encode (Ppushl_r (bpf_to_x64_reg src))))
            (x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) @
             x64_encode (Pshlq_r (bpf_to_x64_reg src)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src)) @ x64_encode (Ppopl (bpf_to_x64_reg src)))
            = Some (length (x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))), Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
          apply (rule_tac l_bin = "x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal
            using list_in_list_prop_aux2 by blast
          subgoal by simp
          subgoal by simp
          subgoal
            apply simp
            apply (erule subst  [of _ "Some (length (x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))), Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))"]) 
            apply simp
            
        apply (simp add: exec_instr_def)
        apply(subgoal_tac "bpf_to_x64_reg src \<noteq> SP") 
         prefer 2 subgoal using reg_rsp_consist by blast
        apply (rule conjI)
         apply (rule impI)
             apply simp 
            apply(subgoal_tac "bpf_to_x64_reg dst \<noteq> SP")
             prefer 2
            subgoal using a9
              using ireg.distinct(67) by presburger
            apply simp
(* 3.3 *)
        apply (subgoal_tac "Suc 2 = (3::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 3])
        apply (simp only: x64_sem.simps)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (length (x64_encode (Ppushl_r (bpf_to_x64_reg src))) + length (x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))))
            (x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)) @
             x64_encode (Pshlq_r (bpf_to_x64_reg src)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src)) @ x64_encode (Ppopl (bpf_to_x64_reg src)))
            = Some (length (x64_encode (Pshlq_r (bpf_to_x64_reg src))), Pshlq_r (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
         apply (subgoal_tac "(length (x64_encode (Ppushl_r (bpf_to_x64_reg src))) + length (x64_encode (Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))) = length (x64_encode(Ppushl_r (bpf_to_x64_reg src))@x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)))")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
          apply (rule_tac l_bin = "x64_encode(Pshlq_r (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          apply simp
          apply (erule subst [of _ "Some (length (x64_encode (Pshlq_r (bpf_to_x64_reg src))), Pshlq_r (bpf_to_x64_reg src))"])
          apply (simp add: exec_instr_def)
          apply (subgoal_tac "RCX = bpf_to_x64_reg dst")
          prefer 2 subgoal using a9
            by presburger
          apply simp
          apply (subgoal_tac "RCX \<noteq> bpf_to_x64_reg src")
          prefer 2 subgoal using a10
            by presburger
          apply simp          
(* 3.4 *)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 2])
        apply (simp only: x64_sem.simps)
            apply (subgoal_tac "x64_decode (length (x64_encode (Ppushl_r (bpf_to_x64_reg src))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg src))) + length (x64_encode (Pshlq_r (bpf_to_x64_reg src))))
            (x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg src)) @
             x64_encode (Pshlq_r (bpf_to_x64_reg src)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src)) @ x64_encode (Ppopl (bpf_to_x64_reg src)))
            = Some (length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src))),Pmovq_rr RCX (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
           apply (subgoal_tac "(length (x64_encode (Ppushl_r (bpf_to_x64_reg src))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg src)))
                    + length (x64_encode (Pshlq_r (bpf_to_x64_reg src))))
               = length (x64_encode(Ppushl_r (bpf_to_x64_reg src))@x64_encode(Pxchgq_rr RCX (bpf_to_x64_reg src))@x64_encode(Pshlq_r (bpf_to_x64_reg src)))")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
             apply (rule_tac l_bin = "x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          apply simp
          apply (erule subst [of _ "Some (length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src))),Pmovq_rr RCX (bpf_to_x64_reg src))"])
          apply (simp add: exec_instr_def)
(* 3.5 *)
        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 1])
        apply (simp only: x64_sem.simps)
          apply (subgoal_tac "x64_decode (length (x64_encode (Ppushl_r (bpf_to_x64_reg src))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg src)))
                   + length (x64_encode (Pshlq_r (bpf_to_x64_reg src))) + length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src))))
            (x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg src)) @
             x64_encode (Pshlq_r (bpf_to_x64_reg src)) @ x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src)) @ x64_encode (Ppopl (bpf_to_x64_reg src)))
            = Some (length (x64_encode (Ppopl (bpf_to_x64_reg src))),Ppopl (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
           apply (subgoal_tac "(length (x64_encode (Ppushl_r (bpf_to_x64_reg src))) + length (x64_encode (Pxchgq_rr RCX (bpf_to_x64_reg src)))
                    + length (x64_encode (Pshlq_r (bpf_to_x64_reg src))) + length (x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src))))
               = length (x64_encode(Ppushl_r (bpf_to_x64_reg src))@x64_encode(Pxchgq_rr RCX (bpf_to_x64_reg src))@x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode (Pmovq_rr RCX (bpf_to_x64_reg src)))")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
             apply (rule_tac l_bin = "x64_encode(Ppopl (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2 append_assoc append.right_neutral length_append by metis
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce

          apply simp
          apply (erule subst [of _ "Some (length (x64_encode (Ppopl (bpf_to_x64_reg src))),Ppopl (bpf_to_x64_reg src))"])
          apply (simp add: exec_instr_def exec_pop_def)
          apply (frule store_load_consistency_m64)
          apply simp      

(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
        apply (rule conjI)
        subgoal
          by (metis a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3)

        unfolding a1 a2
        apply (simp add: match_state_def)
        apply (rule conjI)
(* 4.1  match_reg *)
        subgoal using shiftq_lsh_one_step_match_reg1 a0 a1 a2 a3 a4 a6 a8 a9 a10 by simp

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using shiftq_lsh_one_step_match_mem1 a0 a1 a2 a3 a4 a6 a8 a9 a10 by simp
(* 4.3  match_stack *)
        subgoal using shiftq_lsh_one_step_match_stack1 a0 a1 a2 a3 a4 a6 a8 a9 a10 by simp
        done
      done
    done
  done
  done
  done
end