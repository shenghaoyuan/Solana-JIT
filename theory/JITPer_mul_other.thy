theory JITPer_mul_other
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma mulq_one_step_match_reg:
  " (SBPF_OK pc' rs' m') = sbpf_step prog (SBPF_OK pc rs m) \<Longrightarrow>
    xst = (Next xpc xrs xm) \<Longrightarrow>
    match_state (SBPF_OK pc rs m) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RAX \<Longrightarrow>
     (bpf_to_x64_reg dst) \<noteq> RDX \<Longrightarrow>
       match_reg rs'
     ((\<lambda>a::preg.
          if a = IR (bpf_to_x64_reg dst) then xrs (IR (bpf_to_x64_reg dst)) * xrs (IR (bpf_to_x64_reg src))
          else if a = IR RDX then xrs (IR RDX)
               else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64
                    else if a = IR RDX then xrs (IR (bpf_to_x64_reg dst)) * xrs (IR (bpf_to_x64_reg src)) div (4294967296::64 word)
                         else if a = IR RAX then xrs (IR (bpf_to_x64_reg dst)) * xrs (IR (bpf_to_x64_reg src))
                              else if a = IR SP then xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64
                                   else if a = IR RAX then xrs (IR (bpf_to_x64_reg dst))
                                        else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else if a = IR REG_SCRATCH then xrs (IR (bpf_to_x64_reg src)) else xrs a)
      (IR SP := xrs (IR SP), IR RAX := xrs (IR RAX)))"
  apply (simp add: match_state_def match_reg_def eval_alu_def eval_reg_def)
  using bpf_to_x64_reg_corr reg_r11_consist
  using reg_rsp_consist by presburger

lemma mulq_one_step_match_mem:
  " (SBPF_OK pc' rs' m') = sbpf_step prog (SBPF_OK pc rs m) \<Longrightarrow>
    xst = (Next xpc xrs xm) \<Longrightarrow>
    match_state (SBPF_OK pc rs m) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RAX \<Longrightarrow>
     (bpf_to_x64_reg dst) \<noteq> RDX \<Longrightarrow>
    storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RAX))) = Some m1 \<Longrightarrow>
    storev M64 m1 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) (Vlong (xrs (IR RDX))) = Some m2 \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RDX))) \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RAX))) \<Longrightarrow> match_mem m' m2"
  apply (simp add: match_state_def match_mem_def eval_alu_def eval_reg_def)
  using sp_block_def store_load_other_blk by auto
  
lemma mulq_one_step_match_stack:
  " (SBPF_OK pc' rs' m') = sbpf_step prog (SBPF_OK pc rs m) \<Longrightarrow>
    xst = (Next xpc xrs xm) \<Longrightarrow>
    match_state (SBPF_OK pc rs m) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
    (bpf_to_x64_reg dst) \<noteq> RAX \<Longrightarrow>
     (bpf_to_x64_reg dst) \<noteq> RDX \<Longrightarrow>
    storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RAX))) = Some m1 \<Longrightarrow>
    bpf_to_x64_reg dst \<noteq> REG_SCRATCH \<Longrightarrow>
    bpf_to_x64_reg dst \<noteq> SP \<Longrightarrow>
    storev M64 m1 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) (Vlong (xrs (IR RDX))) = Some m2 \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RDX))) \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RAX))) \<Longrightarrow>
    match_stack
     ((\<lambda>a::preg.
          if a = IR (bpf_to_x64_reg dst) then xrs (IR (bpf_to_x64_reg dst)) * xrs (IR (bpf_to_x64_reg src))
          else if a = IR RDX then xrs (IR RDX)
               else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64
                    else if a = IR RDX then xrs (IR (bpf_to_x64_reg dst)) * xrs (IR (bpf_to_x64_reg src)) div (4294967296::64 word)
                         else if a = IR RAX then xrs (IR (bpf_to_x64_reg dst)) * xrs (IR (bpf_to_x64_reg src))
                              else if a = IR SP then xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64
                                   else if a = IR RAX then xrs (IR (bpf_to_x64_reg dst))
                                        else if a = IR SP then xrs (IR SP) - u64_of_memory_chunk M64 else if a = IR REG_SCRATCH then xrs (IR (bpf_to_x64_reg src)) else xrs a)
      (IR SP := xrs (IR SP), IR RAX := xrs (IR RAX)))
     m2"
  apply (simp add: match_state_def match_stack_def eval_alu_def eval_reg_def)
  by (metis store_load_other_blk)

lemma todo_stack_overflow: "uint (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64) + memory_chunk_to_byte_int M64 < uint (xrs (IR SP) - u64_of_memory_chunk M64)"
  apply (simp add: u64_of_memory_chunk_def memory_chunk_to_byte_int_def)
  sorry

lemma mul_push_mem_prop : "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR RAX))) = Some m1 \<Longrightarrow>
    storev M64 m1 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) (Vlong (xrs (IR RDX))) = Some m2 \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RDX))) \<Longrightarrow>
    loadv M64 m1 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RAX))) \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RDX))) \<Longrightarrow>
    loadv M64 m2 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RAX)))"
  apply (insert store_load_other_blk2 [of sp_block sp_block 
          "(xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)" M64
          "xrs (IR SP) - u64_of_memory_chunk M64" M64 m2 m1 "(Vlong (xrs (IR RDX)))"
          "(Vlong (xrs (IR RAX)))"])
  apply (subgoal_tac "uint (xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64) + memory_chunk_to_byte_int M64 < uint (xrs (IR SP) - u64_of_memory_chunk M64)")
   apply simp
  using todo_stack_overflow by auto

lemma mulq_one_step_other:
assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src)" and
  a9:"(bpf_to_x64_reg dst) \<noteq> RAX " and
  a7:"(bpf_to_x64_reg dst) \<noteq> RDX "
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"

  apply simp
(* 1. as BPF_MUL generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_mul_reg64 dst src)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_mul_reg64 dst src) = (8, 0, x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))")
       prefer 2
      subgoal 
        apply (cases "bpf_to_x64_reg dst" ; simp add:per_jit_mul_reg64_def a9 a7)
        done
      apply(subgoal_tac "(x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))!1 \<noteq> 0x39")
        prefer 2 subgoal using per_jit_mul_reg64_def x64_encode_def by auto
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 6 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 7 = (8::nat)") prefer 2 subgoal by simp
        apply (erule subst)
        apply (simp only: x64_sem.simps)
        apply simp
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (0::nat)
            (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (3, Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop
            using list_in_list_concat by blast
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def)
(* 3.2 *)
        apply (subgoal_tac "Suc 6 = (7::nat)") prefer 2 subgoal by simp
        apply (erule subst)
        apply (simp only: x64_sem.simps)
        apply simp
        apply (subgoal_tac "x64_decode (3::nat)
           (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (1, Ppushl_r RAX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))) = 3")
         prefer 2 subgoal using x64_encode_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode (Ppushl_r RAX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by metis 
          subgoal by simp
          subgoal apply (erule subst) 
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def exec_push_def Let_def)
        apply (insert storev_stack_some [of xm "(xrs (IR SP) - u64_of_memory_chunk M64)" "xrs (IR RAX)"])
        apply (erule exE)
        subgoal for m1
          apply simp
(* 3.3 *)
        apply (subgoal_tac "Suc 5 = (6::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 6])
        apply (simp only: x64_sem.simps)
        apply simp
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (4::nat)
            (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (3, Pmovq_rr RAX (bpf_to_x64_reg dst))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX))) = 4")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3::nat, Pmovq_rr RAX (bpf_to_x64_reg dst))"])
        apply (simp add: exec_instr_def)
        apply (subgoal_tac "bpf_to_x64_reg dst \<noteq> REG_SCRATCH")
        prefer 2 subgoal using bpf_to_x64_reg_def
          using reg_r11_consist by presburger
        apply (subgoal_tac "bpf_to_x64_reg dst \<noteq> SP")
        prefer 2 subgoal using bpf_to_x64_reg_def
          using reg_rsp_consist by blast
        apply simp
(* 3.4 *)
        apply (subgoal_tac "Suc 4 = (5::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 5])
        apply (simp only: x64_sem.simps)
        apply simp
        apply (subgoal_tac "x64_decode (7::nat)
            (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (1, Ppushl_r RDX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @ x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))) = 7")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
         apply (rule_tac l_bin = "x64_encode (Ppushl_r RDX)" in x64_encode_decode_consistency)
         subgoal using list_in_list_prop_aux2
           by (metis append_assoc) 
         subgoal by simp
         subgoal apply (erule subst) 
           using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
           by fastforce
         done
        apply simp
        apply (erule subst [of _ "Some (Suc (0::nat), Ppushl_r RDX)"])
        apply (simp add: exec_instr_def exec_push_def Let_def)
        apply (insert storev_stack_some [of m1 "(xrs (IR SP) - (2::64 word) * u64_of_memory_chunk M64)" "xrs (IR RDX)"])
        apply (erule exE)
        subgoal for m2
          apply simp               
       
(* 3.5 *)
        apply (subgoal_tac "Suc 3 = (4::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 4])
        apply (simp only: x64_sem.simps)
        apply simp
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (8::nat)
            (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (3, Pmulq_r R11)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)))) = 8")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmulq_r REG_SCRATCH)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3::nat, Pmulq_r REG_SCRATCH)"])
        apply (simp add: exec_instr_def)
(* 3.6 *)
        apply (subgoal_tac "Suc 2 = (3::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 3])
        apply (simp only: x64_sem.simps)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (11::nat)
             (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (1, Ppopl RDX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)))) = 11")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode (Ppopl RDX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_eq_append_conv2)
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (Suc (0::nat), Ppopl RDX)"])
        apply (simp add: exec_instr_def exec_pop_def)
        apply (frule store_load_consistency [of _ _ _ m2])
        apply simp
(* 3.7 *)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 2])
        apply (simp only: x64_sem.simps)
        apply simp
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (12::nat)
            (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (3, Pmovq_rr (bpf_to_x64_reg dst) RAX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX)))) = 12")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_assoc)
          subgoal by simp
          subgoal using x64_encode_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (3::nat, Pmovq_rr (bpf_to_x64_reg dst) RAX) "])
        apply (simp add: exec_instr_def)
(* 3.8 *)
        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 1])
        apply (simp only: x64_sem.simps)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (15::nat)
            (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX)))
            = Some (1, Ppopl RAX)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)))) = 15")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by simp
        subgoal
          apply (rule_tac l_bin = "x64_encode (Ppopl RAX)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis append_eq_append_conv2)
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst [of _ "Some (Suc (0::nat), Ppopl RAX)"])
        apply (simp add: exec_instr_def exec_pop_def)
        apply (subgoal_tac "loadv M64 m2 (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) = Some (Vlong (xrs (IR RAX)))")
        prefer 2
        subgoal
          apply (frule store_load_consistency [of _ _ _ m1])
          apply (frule store_load_consistency [of _ _ _ m2])
          using mul_push_mem_prop by auto

        apply simp

(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
        apply (rule conjI)
        subgoal
          by (metis a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3)

        unfolding a1 a2
        apply (simp add: match_state_def)
        apply (rule conjI)
(* 4.1  match_reg *)
        subgoal using mulq_one_step_match_reg a0 a1 a2 a3 a4 a6 a8 a9 a7
          by simp

        apply (rule conjI)
(* 4.2  match_mem *)
        subgoal using mulq_one_step_match_mem a0 a1 a2 a3 a4 a6 a8 a9 a7 by simp
(* 4.2  match_stack *)
        subgoal using mulq_one_step_match_stack a0 a1 a2 a3 a4 a6 a8 a9 a7 by simp
        done
      done
    done
  done
  done
  done

end