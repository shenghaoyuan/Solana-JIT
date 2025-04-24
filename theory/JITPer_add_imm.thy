theory JITPer_add_imm
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma aluq_imm_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow>
     xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc rs m ss) = (SBPF_OK pc' rs' m' ss')  \<Longrightarrow>
     Next spc' reg' xm' xss' = exec_instr xins sz spc reg xm xss \<Longrightarrow>
     reg (IR (bpf_to_x64_reg dst)) = rs dst \<Longrightarrow>
     reg (IR (bpf_to_x64_reg src)) = rs src \<Longrightarrow>
     reg' (IR (bpf_to_x64_reg dst)) = (rs' dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply(cases "prog ! unat pc",simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done


lemma aluq_imm_subgoal_rr_aux2_1:"xins = Paddq_rr dst src \<Longrightarrow> 
  Next pc' reg' m' xss' = exec_instr xins sz pc reg m xss \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (IR r) = reg (IR r)"
  by (simp add: exec_instr_def)


lemma aluq_imm_subgoal_rr_aux2:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' xss' = exec_instr xins sz pc reg m xss \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))"
  using aluq_imm_subgoal_rr_aux2_1 by simp



lemma aluq_imm_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc rs m ss) = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow>
  \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases bins,simp_all)
  apply(cases "prog ! unat pc", simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done

lemma stack_is_not_changed_by_add:"Next spc' reg' m' xss' = exec_instr xins sz spc reg m xss \<Longrightarrow> xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> match_stack reg \<Longrightarrow> match_stack reg' "
proof-
  assume a0:"Next spc' reg' m' xss' = exec_instr xins sz spc reg m xss" and
  a1:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) " and
  a2:"match_stack reg"
  have b0:"bpf_to_x64_reg dst \<noteq> RSP" using bpf_to_x64_reg_def by (cases dst,simp_all)
  have b1:"reg (IR SP) = reg' (IR SP)" using exec_instr_def a0 a1 b0
    by (metis (no_types, opaque_lifting) aluq_imm_subgoal_rr_aux2_1)
  have "match_stack reg' " using b1 a2 match_stack_def by auto
  thus ?thesis by blast
qed

lemma mem_is_not_changed_by_add:"Next spc' reg' m' xss'= exec_instr xins sz spc reg m xss\<Longrightarrow> xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> m = m'"
  using exec_instr_def by simp

(*value "((scast (scast (-1::i32)::u32))::u64)"
value "((scast ((-1)::i32))::u64)"*)


lemma scast_aux1:"((scast (scast (imm::i32)::u32))::u64) = ((scast imm)::u64)"
  sorry

(*(\<And>(r::ireg) dst::bpf_ireg. r = bpf_to_x64_reg dst \<Longrightarrow> bpf_to_x64_reg dst \<noteq> REG_OTHER_SCRATCH) \<Longrightarrow> *)
lemma addq_imm_one_step_match_reg:
  " s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state s (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOImm (imm::i32)) \<Longrightarrow>
    bpf_to_x64_reg dst \<noteq> REG_OTHER_SCRATCH \<Longrightarrow> 
    match_reg rs' ((\<lambda>a::preg. if a = IR REG_OTHER_SCRATCH then (scast ((scast (imm::i32))::u32))::u64 else xrs a)(IR (bpf_to_x64_reg dst) := xrs (IR (bpf_to_x64_reg dst)) + (scast ((scast (imm::i32))::u32))::u64))"
  apply (simp add: match_state_def match_reg_def eval_alu_def eval_alu64_aux2_def eval_reg_def)
  apply rule apply rule 
  subgoal for r apply rule using scast_aux1 by presburger 
  subgoal for r apply rule apply rule using reg_r10_consist by simp
  done


lemma addq_imm_one_step:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOImm (imm::i32))" 
shows "\<exists> xst'. perir_sem 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  apply simp

(* 1. as BPF_ADD generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. perir_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold perir_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_add_imm64_1 dst (imm::i32))")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_add_imm64_1 dst (imm::i32)) = (2, 0, x64_encode (Pmovl_ri R10 (scast (imm::i32)))@x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10))")
       prefer 2
      subgoal by (simp add: per_jit_add_imm64_1_def)
      apply (subgoal_tac "(x64_encode (Pmovl_ri R10 (scast (imm::i32)::u32))@x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10)) !1 \<noteq> 0x39 \<and> 
        (x64_encode (Pmovl_ri R10 (scast (imm::i32)))@x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10)) !0 \<noteq> 0xc3 \<and> 
        (x64_encode (Pmovl_ri R10 (scast (imm::i32)))@x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10)) !0 \<noteq> 0xe8")
       prefer 2
      subgoal apply(unfold x64_encode_def) 
        apply(cases "Pmovl_ri R10 (scast (imm::i32)::u32)",simp_all) 
        subgoal for x11 apply(unfold per_jit_add_imm64_1_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_of_bool_def,simp_all)
          done
        done
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 2])
        apply (simp only: x64_sem.simps)
(* 3. here we get a simplified version, next step is to remove another case statement *)
        apply (subgoal_tac "x64_decode 0 (x64_encode (Pmovl_ri R10 (scast imm))@x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10)) = Some (7, Pmovl_ri R10 (scast imm))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "(x64_encode (Pmovl_ri R10 (scast imm)))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop  
            using list_in_list_concat by blast
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u32_def
            by fastforce
          done
        subgoal
          apply simp
          apply (erule subst)
          apply (simp add: exec_instr_def)
          apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
          apply (erule subst [of _ 1])
          apply (simp only: x64_sem.simps)

       apply (subgoal_tac "x64_decode (7::nat)
            (x64_encode (Pmovl_ri R10 (scast imm))@x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10))
            = Some (3, Paddq_rr (bpf_to_x64_reg dst) R10)")
           prefer 2
           apply(subgoal_tac "length(x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10)) = 3")
            prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u32_def by auto
          subgoal 
            apply (rule_tac l_bin = "x64_encode (Paddq_rr (bpf_to_x64_reg dst) R10)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis \<open>(x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast (imm::32 signed word))) @ x64_encode (Paddq_rr (bpf_to_x64_reg (dst::bpf_ireg)) REG_OTHER_SCRATCH)) ! Suc (0::nat) \<noteq> (57::8 word) \<and> (x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast imm)) @ x64_encode (Paddq_rr (bpf_to_x64_reg dst) REG_OTHER_SCRATCH)) ! (0::nat) \<noteq> (195::8 word) \<and> (x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast imm)) @ x64_encode (Paddq_rr (bpf_to_x64_reg dst) REG_OTHER_SCRATCH)) ! (0::nat) \<noteq> (232::8 word) \<Longrightarrow> x64_decode (0::nat) (x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast imm)) @ x64_encode (Paddq_rr (bpf_to_x64_reg dst) REG_OTHER_SCRATCH)) = Some (7::nat, Pmovl_ri REG_OTHER_SCRATCH (scast imm))\<close> append.right_neutral append_Nil list.size(3) option.sel prod.sel(1) x64_encode_decode_consistency)
          subgoal by simp
          subgoal apply (erule subst) 
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def)
        apply (subgoal_tac "bpf_to_x64_reg dst \<noteq> R10")
        prefer 2 subgoal
          using reg_r10_consist by simp
        apply simp

(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
          apply (rule conjI)
          subgoal
            using a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3 by metis
          subgoal
            unfolding a1 a2
            apply (simp add: match_state_def)
            apply (rule conjI) 
            subgoal using addq_imm_one_step_match_reg a0 a1 a2 a3 a4 a6 a8 by blast
            oops
          done
        done
      done
    done
  done


end