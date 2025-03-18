theory JITPer_shift
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin


value "and (0b1111111000000::32 word) (0b111111::32 word)"
lemma shiftq_lsh_one_step_match_reg:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RCX \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RSP \<Longrightarrow>
     match_reg rs' 
     ((\<lambda>a::preg. 
        if a = IR (bpf_to_x64_reg dst) then xrs (IR (bpf_to_x64_reg dst)) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word)) 
        else if a = IR RCX then xrs (IR (bpf_to_x64_reg src)) else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else xrs a )
      (IR SP := xrs (IR SP), IR RCX := xrs (IR RCX)))"
  by (simp add: match_state_def match_reg_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  

lemma shiftq_lsh_one_step_match_mem:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RCX \<Longrightarrow>
     storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RCX))) = Some m1 \<Longrightarrow> 
     loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RCX))) \<Longrightarrow> 
     match_mem m' m1"
   apply (simp add: match_state_def)
    apply(subgoal_tac "m = m'")
   prefer 2 
    subgoal
      apply(cases "eval_alu BPF_LSH dst (SOReg src) rs ",simp_all)
    done
    using sp_block_def match_mem_def match_mem_store_1_equiv by metis


lemma shiftq_lsh_one_step_match_stack:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RCX \<Longrightarrow>
    storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RCX))) = Some m1 \<Longrightarrow> 
    loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RCX))) \<Longrightarrow>
    match_stack ((\<lambda>a::preg. 
      if a = IR (bpf_to_x64_reg dst) then xrs (IR (bpf_to_x64_reg dst)) << unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
      else if a = IR RCX then xrs (IR (bpf_to_x64_reg src)) 
      else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else xrs a)
    (IR SP := xrs (IR SP), IR RCX := xrs (IR RCX)))"
  by (simp add: match_state_def match_stack_def eval_alu_def eval_alu64_aux2_def eval_reg_def)


lemma encode_aux:"(x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX))!0 \<notin> {0xc3, 0xe8}"
  subgoal apply(unfold per_jit_mul_reg64_def x64_encode_def)
   by(unfold construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def,simp_all)
  done

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


lemma shiftq_lsh_one_step1:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src)" and
  a9:"(bpf_to_x64_reg dst) \<noteq> RCX"
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  apply simp
(* 1. as BPF_LDX generates a single list of jited x64 assembly, so we only need one step  *)
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
      apply (subgoal_tac "the (per_jit_shift_lsh_reg64 dst src) = (4, 0, x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX))")
       prefer 2
      subgoal using per_jit_shift_lsh_reg64_def a9 by(cases "(bpf_to_x64_reg dst)",simp_all)
      apply (subgoal_tac "(x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX)) !1 \<noteq> 0x39")
       prefer 2 subgoal apply(unfold per_jit_shift_lsh_reg64_def x64_encode_def) 
       (* using a9 apply(cases "bpf_to_x64_reg dst",simp_all) *)
        apply simp
          apply(unfold Let_def x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def construct_modsib_to_u8_def u8_of_bool_def)  
          apply(cases False,simp_all)
          apply(cases "and (u8_of_ireg (bpf_to_x64_reg src)) (8::8 word) \<noteq> (0::8 word)",simp_all)
        done
      apply(subgoal_tac "(x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX))!0 \<notin> {0xc3, 0xe8}")
      prefer 2 using encode_aux apply simp
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 6 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 3 = (4::nat)") prefer 2 subgoal by simp
        apply (erule subst)
        apply (simp only: x64_sem.simps)
        apply simp
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (0::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (1, Ppushl_r RCX)")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode(Ppushl_r x64Syntax.RCX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop
            using list_in_list_concat by blast
          subgoal by simp
          subgoal
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def exec_push_def Let_def)
        apply (insert storev_stack_some [of xm "(xrs (IR SP) - u64_of_memory_chunk M64)" "xrs (IR RCX)"])
        apply (erule exE)
        subgoal for m1
          apply simp
(* 3.2 *)
        apply (subgoal_tac "Suc 2 = (3::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 3])
        apply (simp only: x64_sem.simps)
        apply simp
        apply (subgoal_tac "x64_decode (1::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (3, Pmovq_rr RCX (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode(Ppushl_r RCX)) = 1")
          prefer 2 subgoal 
          using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
        subgoal
          apply (rule_tac l_bin = "x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by metis 
          subgoal by simp
          subgoal apply (erule subst) 
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3, Pmovq_rr RCX (bpf_to_x64_reg src))"])
        apply (simp add: exec_instr_def)
        apply(subgoal_tac "bpf_to_x64_reg src \<noteq> SP") 
         prefer 2 subgoal using reg_rsp_consist by blast
        apply (rule conjI)
         apply (rule impI)
         apply simp
        apply(rule impI)
(* 3.3 *)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 2])
        apply (simp only: x64_sem.simps)
        apply simp
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (4::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (3, Pshlq_r (bpf_to_x64_reg dst))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))) = 4")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode(Pshlq_r (bpf_to_x64_reg dst))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3::nat,Pshlq_r (bpf_to_x64_reg dst))"])
        apply (simp add: exec_instr_def)
(* 3.4 *)
        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 1])
        apply (simp only: x64_sem.simps)
        apply(subgoal_tac "bpf_to_x64_reg dst \<noteq> SP") 
         prefer 2 subgoal using reg_rsp_consist by blast
        apply (rule conjI)
         apply (rule impI)
         apply simp
        apply(rule impI)
        apply (rule conjI)
         apply(rule impI) using a9 apply simp
        apply(rule impI)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (7::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (1, Ppopl RCX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst)))) = 7")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode(Ppopl RCX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_eq_append_conv2)
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (Suc (0::nat), Ppopl RCX)"])
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
        subgoal using shiftq_lsh_one_step_match_reg a0 a1 a2 a3 a4 a6 a8 a9
          by simp

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using shiftq_lsh_one_step_match_mem a0 a1 a2 a3 a4 a6 a8 a9 by simp
(* 4.3  match_stack *)
        subgoal using shiftq_lsh_one_step_match_stack a0 a1 a2 a3 a4 a6 a8 a9 apply simp
          using shiftq_lsh_one_step_match_stack2 a0 a1 a2 a3 a4 a6 a8 a9 by (metis (no_types, lifting)) 
        done
      done
    done
  done
  done


lemma shiftq_rsh_one_step_match_reg:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RCX \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RSP \<Longrightarrow>
     match_reg rs' 
    ((\<lambda>a::preg. 
        if a = IR (bpf_to_x64_reg dst) then xrs (IR (bpf_to_x64_reg dst)) >> unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
        else if a = IR RCX then xrs (IR (bpf_to_x64_reg src)) 
        else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 
        else xrs a)
    (IR SP := xrs (IR SP), IR RCX := xrs (IR RCX)))"
  by (simp add: match_state_def match_reg_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
 
  

lemma shiftq_rsh_one_step_match_mem:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RCX \<Longrightarrow>
     storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RCX))) = Some m1 \<Longrightarrow> 
     loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RCX))) \<Longrightarrow> 
     match_mem m' m1"
  apply (simp add: match_state_def match_mem_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  using sp_block_def store_load_other_blk by (metis match_mem_def match_mem_store_1_equiv) 


lemma shiftq_rsh_one_step_match_stack:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RCX \<Longrightarrow>
    storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RCX))) = Some m1 \<Longrightarrow> 
    loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RCX))) \<Longrightarrow>
    match_stack ((\<lambda>a::preg. 
      if a = IR (bpf_to_x64_reg dst) then xrs (IR (bpf_to_x64_reg dst)) >> unat (and (ucast (xrs (IR (bpf_to_x64_reg src)))) (63::32 word))
      else if a = IR RCX then xrs (IR (bpf_to_x64_reg src)) 
      else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else xrs a)
    (IR SP := xrs (IR SP), IR RCX := xrs (IR RCX)))"
  by (simp add: match_state_def match_stack_def eval_alu_def eval_alu64_aux2_def eval_reg_def)


lemma encode_aux2:"(x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX))!0 \<notin> {0xc3, 0xe8}"
  subgoal apply(unfold per_jit_mul_reg64_def x64_encode_def)
   by(unfold construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def,simp_all)
  done


lemma shiftq_rsh_one_step_match_stack2:
  " (SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src) \<Longrightarrow>
    xss = ss'"
   apply(cases"prog!(unat pc)",simp_all)
  subgoal for x91 
    apply(cases "eval_alu BPF_RSH dst (SOReg src) rs",simp_all)
    apply(unfold match_state_def,simp_all)
    done
  done

lemma shiftq_rsh_one_step1:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src)" and
  a9:"(bpf_to_x64_reg dst) \<noteq> RCX"
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  apply simp
(* 1. as BPF_LDX generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_shift_rsh_reg64 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_shift_rsh_reg64 dst src) = (4, 0, x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX))")
       prefer 2
      subgoal using per_jit_shift_rsh_reg64_def a9 by(cases "(bpf_to_x64_reg dst)",simp_all)
      apply (subgoal_tac "(x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX)) !1 \<noteq> 0x39")
       prefer 2 subgoal apply(unfold per_jit_shift_lsh_reg64_def x64_encode_def) 
       (* using a9 apply(cases "bpf_to_x64_reg dst",simp_all) *)
        apply simp
          apply(unfold Let_def x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def construct_modsib_to_u8_def u8_of_bool_def)  
          apply(cases False,simp_all)
          apply(cases "and (u8_of_ireg (bpf_to_x64_reg src)) (8::8 word) \<noteq> (0::8 word)",simp_all)
        done
      apply(subgoal_tac "(x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX))!0 \<notin> {0xc3, 0xe8}")
      prefer 2 using encode_aux2 apply simp
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 6 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 3 = (4::nat)") prefer 2 subgoal by simp
        apply (erule subst)
        apply (simp only: x64_sem.simps)
        apply simp
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (0::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (1, Ppushl_r RCX)")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode(Ppushl_r x64Syntax.RCX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop
            using list_in_list_concat by blast
          subgoal by simp
          subgoal
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def exec_push_def Let_def)
        apply (insert storev_stack_some [of xm "(xrs (IR SP) - u64_of_memory_chunk M64)" "xrs (IR RCX)"])
        apply (erule exE)
        subgoal for m1
          apply simp
(* 3.2 *)
        apply (subgoal_tac "Suc 2 = (3::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 3])
        apply (simp only: x64_sem.simps)
        apply simp
        apply (subgoal_tac "x64_decode (1::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (3, Pmovq_rr RCX (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode(Ppushl_r RCX)) = 1")
          prefer 2 subgoal 
          using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
        subgoal
          apply (rule_tac l_bin = "x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by metis 
          subgoal by simp
          subgoal apply (erule subst) 
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3, Pmovq_rr RCX (bpf_to_x64_reg src))"])
        apply (simp add: exec_instr_def)
        apply(subgoal_tac "bpf_to_x64_reg src \<noteq> SP") 
         prefer 2 subgoal using reg_rsp_consist by blast
        apply (rule conjI)
         apply (rule impI)
         apply simp
        apply(rule impI)
(* 3.3 *)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 2])
        apply (simp only: x64_sem.simps)
        apply simp
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (4::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (3, Pshrq_r (bpf_to_x64_reg dst))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))) = 4")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode(Pshrq_r (bpf_to_x64_reg dst))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3::nat,Pshrq_r (bpf_to_x64_reg dst))"])
        apply (simp add: exec_instr_def)
(* 3.4 *)
        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 1])
        apply (simp only: x64_sem.simps)
        apply(subgoal_tac "bpf_to_x64_reg dst \<noteq> SP") 
         prefer 2 subgoal using reg_rsp_consist by blast
        apply (rule conjI)
         apply (rule impI)
         apply simp
        apply(rule impI)
        apply (rule conjI)
         apply(rule impI) using a9 apply simp
        apply(rule impI)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (7::nat)
            (x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl RCX))
            = Some (1, Ppopl RCX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode(Ppushl_r RCX)@x64_encode(Pmovq_rr RCX (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst)))) = 7")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode(Ppopl RCX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_eq_append_conv2)
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (Suc (0::nat), Ppopl RCX)"])
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
        subgoal using shiftq_rsh_one_step_match_reg a0 a1 a2 a3 a4 a6 a8 a9
          by simp

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using shiftq_rsh_one_step_match_mem a0 a1 a2 a3 a4 a6 a8 a9 by simp
(* 4.3  match_stack *)
        subgoal using shiftq_rsh_one_step_match_stack a0 a1 a2 a3 a4 a6 a8 a9 apply simp
          using shiftq_rsh_one_step_match_stack2 a0 a1 a2 a3 a4 a6 a8 a9 by (metis (no_types, lifting)) 
        done
      done
    done
  done
  done



end