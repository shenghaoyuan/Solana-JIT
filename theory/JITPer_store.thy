theory JITPer_store

imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma length_of_addrmode_instr:
  assumes a0:"xins = (Pmov_mr (Addrmode (Some R11) None 0) R10 chk)" and
  a1:"l_bin = x64_encode xins" and
  a2:"chk = M64"
  shows "length l_bin = 4"
proof-
  let "?a" = "(Addrmode (Some R11) None 0)"
  let "?r1" =  "R10"
  let "?c" = "chk"
  have b1:"construct_rex_to_u8 (?c = M64) (and (u8_of_ireg ?r1) 0b1000 \<noteq> 0) False (and (u8_of_ireg R11) 0b1000 \<noteq> 0) \<noteq> 0x40"
    using a2 apply(unfold construct_rex_to_u8_def Let_def bitfield_insert_u8_def u8_of_bool_def,simp_all) 
    done
  have b3:"l_bin = (case ?a of Addrmode (Some rb) None dis \<Rightarrow> 
      let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> WRXB \<close>
        (?c = M64) \<comment> \<open> W \<close>
        (and (u8_of_ireg ?r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
        let (dis::u8) = scast dis in
        let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg ?r1) (u8_of_ireg rb) in
        ([rex, 0x89, rop, dis]))" using b1 using a0 a1 x64_encode_def a2 by(cases chk,simp_all)
  thus ?thesis by simp
qed

lemma cast_aux1:"\<forall> x y. ((scast(x::u64))::i64) + ((scast(y::u64))::i64) = (scast(x+y)::i64)"
  by (metis (mono_tags, opaque_lifting) of_int_add of_int_sint scast_id scast_nop2 scast_scast_id(2))

lemma cast_aux2:"(ucast ((scast(x::u64))::i64)::u64) = x"
  using  scast_nop1
  by (metis scast_scast_id(1) ucast_eq word_of_int_uint)

lemma cast_lemma1:"(ucast(((scast(x::u64))::i64) + ((scast(y::u64))::i64))::u64) = x+y"
  using cast_aux1 cast_aux2 by auto

lemma store_mem_one_step1:
 assumes a0:"(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss)" and
    a1:"xst = (Next xpc xrs xm xss)" and
    a2:"match_state (SBPF_OK pc rs m ss) (pc,xst)" and
    a3:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
    a4:"prog!(unat pc) = BPF_ST chk dst (SOReg src) off" and
    a5:"chk = M64"
  shows "storev chk xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg dst)))) (Vlong (xrs (IR (bpf_to_x64_reg src)))) \<noteq> None"
proof-

  have "\<exists> xm'. Some xm' = (let off = (xrs (IR (bpf_to_x64_reg dst)) + scast off); l = u8_list_of_u64 (ucast (xrs (IR (bpf_to_x64_reg src)))) in
               Some  (\<lambda> x i. if x = 0 \<and> i = (uint off)    then Some (l!(0)) else
                   if x = 0 \<and> i = (uint off)+1  then Some (l!(1)) else
                   if x = 0 \<and> i = (uint off)+2  then Some (l!(2)) else
                   if x = 0 \<and> i = (uint off)+3  then Some (l!(3)) else
                   if x = 0 \<and> i = (uint off)+4  then Some (l!(4)) else
                   if x = 0 \<and> i = (uint off)+5  then Some (l!(5)) else
                   if x = 0 \<and> i = (uint off)+6  then Some (l!(6)) else
                   if x = 0 \<and> i = (uint off)+4  then Some (l!(4)) else
                      m 0 i))" 
    using storev_def apply(cases "(xrs (IR (bpf_to_x64_reg src)))",simp_all)
    subgoal for n by metis done
  then obtain xm' where "Some (xm'::mem) = (let off = (xrs (IR (bpf_to_x64_reg dst)) + scast off); l = u8_list_of_u64 (ucast (xrs (IR (bpf_to_x64_reg src)))) in
               Some (\<lambda> x i. if x = 0 \<and> i = (uint off)    then Some (l!(0)) else
                   if x = 0 \<and> i = (uint off)+1  then Some (l!(1)) else
                   if x = 0 \<and> i = (uint off)+2  then Some (l!(2)) else
                   if x = 0 \<and> i = (uint off)+3  then Some (l!(3)) else
                   if x = 0 \<and> i = (uint off)+4  then Some (l!(4)) else
                   if x = 0 \<and> i = (uint off)+5  then Some (l!(5)) else
                   if x = 0 \<and> i = (uint off)+6  then Some (l!(6)) else
                   if x = 0 \<and> i = (uint off)+4  then Some (l!(4)) else
                      m 0 i))" by auto
  thus ?thesis using storev_def 
    by (metis (no_types, lifting) a5 memory_chunk.simps(16) option.distinct(1) val.simps(40))
qed

lemma store_match_reg_one_step:
    "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_ST chk dst (SOReg src) off  \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    match_reg rs' (\<lambda>a::preg. if a = IR REG_OTHER_SCRATCH then xrs (IR (bpf_to_x64_reg src)) else if a = IR REG_SCRATCH then scast off + xrs (IR (bpf_to_x64_reg dst)) else if a = IR REG_SCRATCH then scast off else xrs a)"
  apply (simp add: match_state_def match_reg_def eval_load_def)
  using bpf_to_x64_reg_corr reg_r11_consist reg_rsp_consist reg_r10_consist
  by (metis option.case_eq_if sbpf_state.inject(1) sbpf_state.simps(6))


lemma store_match_mem_one_step:
  assumes a0:"(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss)" and
    a1:"xst = (Next xpc xrs xm xss)" and
    a2:"match_state (SBPF_OK pc rs m ss) (pc,xst)" and
    a3:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
    a4:"prog!(unat pc) =  BPF_ST chk dst (SOReg src) off" and
    a5:"storev chk xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg dst)))) (Vlong (xrs (IR (bpf_to_x64_reg src)))) = Some xm'" and
    a6:"chk = M64"
    shows "match_mem m' xm' "
proof-        
  have c_old_mem_eqiv:"\<forall> addr v. m 0 addr = Some v \<longrightarrow> xm 0 addr = Some v"
    using a1 a2 match_state_def match_mem_def by simp
  have c_src_eqiv:"xrs (IR (bpf_to_x64_reg src)) = rs (src)" using match_state_def match_reg_def a2 a1 by simp
  have c_dst_eqiv:"xrs (IR (bpf_to_x64_reg dst)) = rs (dst)" using match_state_def match_reg_def a2 a1 by simp

  have b0:" Some m' = (let dv = (eval_reg dst rs) in (
  let vm_addr  = (dv + (scast off)) in (  
  let sv :: u64 = eval_snd_op_u64 (SOReg src) rs in (
  (storev chk m (Vlong vm_addr) (memory_chunk_value_of_u64 chk sv))))))" using a0 a3 a4 eval_store_def
  by (smt (z3) a6 bpf_instruction.case(3) memory_chunk.case(4) option.case_eq_if option.collapse sbpf_state.inject(1) sbpf_state.simps(6) sbpf_step.simps(1) snd_op.simps(6))


  let "?x_addr" = "(xrs (IR (bpf_to_x64_reg dst)) + scast off)"

  let "?b_addr" = "((rs dst) + (scast off))"

  have addr_eqiv: "?x_addr = ?b_addr"
    using c_dst_eqiv by force

  let "?x_val" = "xrs (IR (bpf_to_x64_reg src))"

  let "?b_val" = "rs src"
  
  have val_eqiv: "?x_val = ?b_val"
    using c_src_eqiv by force

  have "Some m' = storev chk m (Vlong ?b_addr) (memory_chunk_value_of_u64 chk (rs src) )"  using b0 eval_reg_def by force
  hence b2:"Some m' = storev chk m (Vlong ?b_addr) (Vlong ?b_val)" using memory_chunk_value_of_u64_def a6 by simp

  have b1:"match_mem m xm"  using a1 a2 match_state_def match_mem_def by simp
  have "match_mem m' xm'" using match_mem_store_equiv  a5 b2  b1 addr_eqiv val_eqiv 
    by (simp add: add.commute)

  thus ?thesis by simp
qed


value "uint (0::u64)"

value "uint (1::u64)"


lemma store_match_stack_one_step:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) =  BPF_ST chk dst (SOReg src) off   \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    storev chk xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg dst)))) (Vlong (xrs (IR (bpf_to_x64_reg src)))) = Some a \<Longrightarrow>
    match_stack(\<lambda>a::preg. if a = IR REG_OTHER_SCRATCH then xrs (IR (bpf_to_x64_reg src)) else if a = IR REG_SCRATCH then scast off + xrs (IR (bpf_to_x64_reg dst)) else if a = IR REG_SCRATCH then scast off else xrs a)"
  by (simp add: match_state_def match_stack_def eval_alu_def eval_reg_def)

lemma store_one_step5:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) =  BPF_ST chk dst (SOReg src) off   \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    xss = ss'"
  by (smt (z3) bpf_instruction.case(3) match_state_def memory_chunk.case(4) option.case_eq_if outcome.case(1) prod.sel(2) sbpf_state.case(1) sbpf_state.inject(1) sbpf_state.simps(6) sbpf_step.simps(1)) 

lemma scast_aux0:"((scast((scast (x::i16))::u32))::u64) = ((scast((scast (x::i16))::i32))::u64)"
  by (simp add: signed_scast_eq)

lemma scast_aux0_1:"((scast((scast (x::i16))::i32))::u64) = ((scast (x::i16))::u64)"
  apply (simp add: signed_scast_eq)
  apply (simp add: bit_eq_iff)
  apply (simp add: bit_signed_take_bit_iff)
  apply (rule allI)
  subgoal for n
  apply (simp add: bit_simps)
    by linarith 
  done

lemma scast_aux1:"((scast((scast (x::i16))::u32))::u64) = ((scast (x::i16))::u64)"
  using scast_aux0 scast_aux0_1
  by simp 


lemma store_one_step1:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_ST chk dst (SOReg src) off" and
  a9:"chk = M64"
shows "\<exists> xst'. perir_sem 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
(* 1. as BPF_ADD generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. perir_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold perir_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_store_reg64 dst src chk off)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_store_reg64 dst src chk off) = (4, 0, x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))")
       prefer 2
      subgoal by (simp add: per_jit_store_reg64_def Let_def)
      apply (subgoal_tac "(x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk)) !1 \<noteq> 0x39 \<and> 
    (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))!0 \<noteq> 0xc3 \<and>
    (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))!0\<noteq> 0xe8")
       prefer 2
      subgoal apply(unfold x64_encode_def) 
        apply(cases "Pmovl_ri REG_SCRATCH (scast off)",simp_all)
        using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
        by simp
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 6 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 3 = (4::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 4])
        apply (simp only: x64_sem.simps)
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (0::nat)
            (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))
            = Some (7, Pmovl_ri REG_SCRATCH (scast off))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmovl_ri REG_SCRATCH (scast off))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop
            using list_in_list_concat by blast
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u32_def
            by auto
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def)
(* 3.2 *)
        apply (subgoal_tac "Suc 2 = (3::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 3])
        apply (simp only: x64_sem.simps)
        apply (subgoal_tac "x64_decode (7::nat)
            (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))
            = Some (3, Paddq_rr R11 (bpf_to_x64_reg dst))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode (Pmovl_ri REG_SCRATCH (scast off))) = 7")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u32_def by auto
        subgoal
          apply (rule_tac l_bin = "x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by metis 
          subgoal by simp
          subgoal apply (erule subst) 
            using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
            by fastforce
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def)
        apply(subgoal_tac "bpf_to_x64_reg dst \<noteq> REG_SCRATCH") 
        prefer 2 using reg_r11_consist apply blast
         apply (rule conjI)
          apply (rule impI)
          apply simp
         apply (rule impI)
         apply (simp add: exec_instr_def Let_def)

(* 3.3 *)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 2])
        apply (simp only: x64_sem.simps)
        (*apply simp*)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (10::nat)
            (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))
            = Some (3, Pmovq_rr R10 (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst)))) = 10")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u32_def by auto
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis (no_types, opaque_lifting) append_eq_append_conv2)
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def by fastforce 
          done 
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def Let_def)
        apply(subgoal_tac "bpf_to_x64_reg src \<noteq> REG_SCRATCH") 
         prefer 2 subgoal using reg_r11_consist by blast
         apply (rule conjI)
         apply (rule impI)
         apply simp
        apply(rule impI)

        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 1])
        apply (simp only: x64_sem.simps)
        (*apply simp*)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (13::nat)
            (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk))
            = Some (4, Pmov_mr (Addrmode (Some R11) None 0) R10 chk)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode (Pmovl_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))) = 13")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u32_def by auto
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmov_mr (Addrmode (Some R11) None 0) R10 chk)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis (no_types, opaque_lifting) append_eq_append_conv2)
          subgoal by simp
          subgoal using length_of_addrmode_instr a9 by simp done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def exec_store_def eval_addrmode64_def Let_def)
        apply(subgoal_tac "bpf_to_x64_reg src \<noteq> REG_SCRATCH") 
         prefer 2 subgoal using reg_r11_consist by blast
         apply (rule conjI)
(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
        subgoal
          using a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3 by metis
        unfolding a1 a2
(* 4.1  match_reg *)
         apply (simp add: match_state_def)
         apply(cases "storev chk xm (Vlong (((scast ((scast off)::u32))::u64) + xrs (IR (bpf_to_x64_reg dst)))) (Vlong (xrs (IR (bpf_to_x64_reg src))))",simp_all)
         subgoal using store_mem_one_step1 a0 a1 a2 a3 a4 a5 a6 a8 a9 scast_aux1 by metis 
        subgoal for x5 apply (rule conjI) subgoal using scast_aux1 apply simp
          using  a9 a0 a1 a2 a3 a4 a5 a6 a8 match_reg_def store_match_reg_one_step  by (smt (verit)) 
        apply (rule conjI) subgoal using store_match_mem_one_step a9 a0 a1 a2 a3 a4 a5 a6 a8 scast_aux1 by simp
        apply (rule conjI) subgoal using store_match_stack_one_step a9 a0 a1 a2 a3 a4 a5 a6 a8 scast_aux1 match_stack_def by simp
        using store_one_step5 a9 a0 a1 a2 a3 a4 a5 a6 a8 by metis
          done
        done
      done
    done

end