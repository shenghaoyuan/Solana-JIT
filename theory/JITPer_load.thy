theory JITPer_load
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma length_of_addrmode_instr:
  assumes a0:"xins = (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk)" and
  a1:"l_bin = x64_encode xins" and
  a2:"chk = M64"
  shows "length l_bin = 4"
proof-
  let "?a" = "(Addrmode (Some R11) None 0)"
  let "?r1" =  "(bpf_to_x64_reg dst)"
  let "?c" = "chk"
  have b1:"construct_rex_to_u8 (?c = M64) (and (u8_of_ireg ?r1) 0b1000 \<noteq> 0) False (and (u8_of_ireg R11) 0b1000 \<noteq> 0) \<noteq> 0x40"
    using a2 apply(unfold construct_rex_to_u8_def Let_def bitfield_insert_u8_def u8_of_bool_def,simp_all) 
    apply(cases "and (u8_of_ireg (bpf_to_x64_reg dst)) (8::8 word) \<noteq> (0::8 word)",simp_all)
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


lemma load_m64_one_step_match_reg_1:
  assumes a0:"(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss)" and
    a1:"xst = (Next xpc xrs xm xss)" and
    a2:"match_state (SBPF_OK pc rs m ss) (pc,xst)" and
    a3:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
    a4:"prog!(unat pc) = BPF_LDX chk dst src off" and
    a5:"chk = M64"
  shows "\<exists> somev. loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vlong somev)"
proof-
  have c0:"match_mem m xm" using a0 a1 a2 match_state_def by auto
  have c1:"\<forall> addr v. m 0 addr = Some v \<longrightarrow> xm 0 addr = Some v" using a1 a2 match_state_def match_mem_def by simp
  (*hence c0:"\<forall> addr v. (Mem.loadv chk m (Vlong addr) = Some v) \<longrightarrow> (Mem.loadv chk xm (Vlong addr) = Some v)" *)
       
  have c2:"xrs (IR (bpf_to_x64_reg src)) = rs (src)" using match_state_def match_reg_def a2 a1 by simp


  have "\<exists> x. Mem.loadv chk m (Vlong ((rs src) + (scast off)))= Some x" 
    using a0 a3 a4 a5 eval_load_def
    using option.exhaust by fastforce 
  then obtain x where b0:"Mem.loadv chk m (Vlong ((rs src) + (scast off)))= Some x"by auto
  let "?off" = " ((rs src) + (scast off))"
  let "?uoff" = " uint((rs src) + (scast off))"
  have b1:"Mem.loadv chk m (Vlong ?off) = (option_val_of_u64 chk (option_u64_of_u8_8 (m 0 ?uoff) (m 0 (?uoff+1)) (m 0 (?uoff+2)) (m 0 (?uoff+3))
                        (m 0 (?uoff+4)) (m 0 (?uoff+5)) (m 0 (?uoff+6)) (m 0 (?uoff+7)) ))"using a5 loadv_def by simp
  let "?tmpres" = "(option_val_of_u64 chk (option_u64_of_u8_8 (m 0 ?uoff) (m 0 (?uoff+1)) (m 0 (?uoff+2)) (m 0 (?uoff+3))
                        (m 0 (?uoff+4)) (m 0 (?uoff+5)) (m 0 (?uoff+6)) (m 0 (?uoff+7))))"
  have b2_1:"?tmpres \<noteq> None" using b1 b0 option_val_of_u64_def memory_chunk_value_of_u64_def
    by (metis option.distinct(1))
  have b2:"\<exists> v. ?tmpres = Some (Vlong v)" using b2_1 memory_chunk_value_of_u64_def a5 
    by (metis (no_types, lifting) memory_chunk.simps(16) option.case_eq_if option_val_of_u64_def)
  then obtain v where b3:"?tmpres = Some (Vlong v)" by auto
  have b4:"Vlong v = x" using b3 b0 b1 by simp
  have "Mem.loadv chk xm (Vlong ?off) \<noteq> None" using  b0 b4 c0
    by (smt (z3) b2_1 loadv_def match_mem_def option.case_eq_if option.collapse option.simps(3) option_u64_of_u8_8_def option_val_of_u64_def val.case(5)) 
  hence b5:"Mem.loadv chk xm (Vlong ?off) = Some x" using match_mem_load_1_equiv b0 b4 c0 by blast
  have b6:"Mem.loadv chk xm (Vlong ?off) = Some (Vlong v)" using b5 b4 by blast
  have "Mem.loadv chk xm (Vlong (xrs (IR (bpf_to_x64_reg src)) + (scast off))) = Some (Vlong v)" using b6 c2 by argo
  thus ?thesis using a5 add.commute by metis
qed


lemma load_m64_one_step_match_reg_2:
  "(SBPF_OK pc' rs' m' xss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vbyte x2) \<Longrightarrow>
    chk = M64 \<Longrightarrow> False"
  using load_m64_one_step_match_reg_1 by fastforce

lemma val_type_unique2:"x = Vlong v \<longrightarrow> x \<notin> {Vshort (ucast v), Vint (ucast v)}"
  by blast

lemma load_m64_one_step_match_reg_3:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vshort x2) \<Longrightarrow>
    chk = M64 \<Longrightarrow> False"
  using load_m64_one_step_match_reg_1 by fastforce

lemma load_m64_one_step_match_reg_4:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vint x2) \<Longrightarrow>
    chk = M64 \<Longrightarrow> False"
  using load_m64_one_step_match_reg_1  by fastforce

lemma load_m64_one_step_match_reg_5:
   "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vptr x1 x2) \<Longrightarrow>
    chk = M64 \<Longrightarrow> False"
  using load_m64_one_step_match_reg_1  by fastforce

lemma load_M64_one_step_match_reg:
   "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vlong x5) \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    match_reg rs' 
    ((\<lambda>a::preg. 
        if a = IR REG_SCRATCH then scast off + xrs (IR (bpf_to_x64_reg src)) 
        else if a = IR REG_SCRATCH then scast off
        else xrs a)
    (IR (bpf_to_x64_reg dst) := x5)) "
  apply (simp add: match_state_def match_reg_def eval_load_def)
  using bpf_to_x64_reg_corr reg_r11_consist reg_rsp_consist 
  by (smt (verit, best) add.commute fun_upd_apply match_mem_load_1_equiv option.case_eq_if option.collapse option.sel sbpf_state.inject(1) sbpf_state.simps(6) val.simps(40)) 


lemma load_M64_one_step_match_mem:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vlong x5) \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    match_mem m' xm"
  apply (simp add: match_state_def eval_load_def) 
  by (metis (no_types, lifting) option.case_eq_if sbpf_state.inject(1) sbpf_state.simps(6))
  


lemma load_M64_one_step_match_stack:
  "(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vlong x5) \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow>
    match_stack ((\<lambda>a::preg. 
      if a = IR REG_SCRATCH then scast off + xrs (IR (bpf_to_x64_reg src)) 
      else if a = IR REG_SCRATCH then scast off 
      else xrs a)
     (IR (bpf_to_x64_reg dst) := x5)) "
  apply (simp add: match_state_def match_stack_def eval_alu_def eval_reg_def)
  using reg_rsp_consist by blast

lemma load_M64_one_step_match_stack2:"(SBPF_OK pc' rs' m' ss') = sbpf_step prog (SBPF_OK pc rs m ss) \<Longrightarrow>
    xst = (Next xpc xrs xm xss) \<Longrightarrow>
    match_state (SBPF_OK pc rs m ss) (pc,xst) \<Longrightarrow>
    prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow>
    loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src)))) = Some (Vlong x5) \<Longrightarrow>
    chk = M64 \<Longrightarrow>
    prog!(unat pc) = BPF_LDX chk dst src off  \<Longrightarrow> xss = ss'"
  apply(cases " prog!(unat pc)",simp_all)
  subgoal for x21
    apply(cases "eval_load M64 dst src off rs m",simp_all)
    apply(unfold match_state_def,simp_all)
    done
  done

lemma load_one_step1:
 assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_LDX chk dst src off" and
  a9:"chk = M64"
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
  
(* 1. as BPF_ADD generates a single list of jited x64 assembly, so we only need one step  *)
  apply(subgoal_tac "\<exists>xst'::outcome. one_step x64_prog (pc, xst) = (pc', xst') \<and> match_state s' (pc', xst')")
  subgoal
    by auto
  subgoal
    apply (unfold one_step_def Let_def)
(* 2. according to the code structure of JITPer, removing the first case statement *)
    apply(subgoal_tac "x64_prog ! unat (fst (pc, xst)) = the (per_jit_load_reg64 dst src chk off)")
     prefer 2
    subgoal
      using a5 a6 a8 aux5 per_jit_ins_def by fastforce
    subgoal
      apply (subgoal_tac "the (per_jit_load_reg64 dst src chk off) = (3, 0, x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))")
       prefer 2
      subgoal by (simp add: per_jit_load_reg64_def Let_def)
      apply (subgoal_tac "(x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))!1 \<noteq> 0x39 \<and> (x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))!0 \<noteq> 0xc3 \<and>  (x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))!0 \<noteq> 0xe8")
       prefer 2
      subgoal apply(unfold x64_encode_def) 
        apply(cases "Pmovq_ri REG_SCRATCH (scast off)",simp_all)
        using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def
        by simp
      subgoal
        unfolding a3
        apply simp
        apply (erule subst)
        apply (erule subst)
(* 3. here we get a simplified version, next step is to run the 6 x64 assembly one by one *)
(* 3.1 *)
        apply (subgoal_tac "Suc 2 = (3::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 3])
        apply (simp only: x64_sem.simps)
        apply simp
(* 3.1.1 using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (0::nat)
            (x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))
            = Some (10, Pmovq_ri REG_SCRATCH (scast off))")
         prefer 2
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmovq_ri REG_SCRATCH (scast off))" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop
            using list_in_list_concat by blast
          subgoal by simp
          subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u64_def
            by auto
          done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def)
(* 3.2 *)
        apply (subgoal_tac "Suc 1 = (2::nat)") prefer 2 subgoal by simp
        apply (erule subst [of _ 2])
        apply (simp only: x64_sem.simps)
        apply simp
        apply (subgoal_tac "x64_decode (10::nat)
            (x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))
            = Some (3, Paddq_rr R11 (bpf_to_x64_reg src))")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length (x64_encode (Pmovq_ri REG_SCRATCH (scast off))) = 10")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u64_def by auto
        subgoal
          apply (rule_tac l_bin = "x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))" in x64_encode_decode_consistency)
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

(* 3.3 *)
        apply (subgoal_tac "Suc 0 = (1::nat)") prefer 2 subgoal by simp
        apply (erule_tac subst [of _ 1])
        apply (simp only: x64_sem.simps)
        (*apply simp*)
(* using consistency to get x64 assembly *)
        apply (subgoal_tac "x64_decode (13::nat)
            (x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk))
            = Some (4, Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk)")
         prefer 2
(* this is necessary for later list_in_list_prop_aux2 *)
        apply (subgoal_tac "length ((x64_encode(Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src)))) = 13")
         prefer 2 subgoal using x64_encode_def construct_rex_to_u8_def bitfield_insert_u8_def Let_def u8_list_of_u64_def by auto
        subgoal
          apply (rule_tac l_bin = "x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk)" in x64_encode_decode_consistency)
          subgoal using list_in_list_prop_aux2
            by (metis (no_types, opaque_lifting) append_eq_append_conv2)
          subgoal by simp
          subgoal using length_of_addrmode_instr a9 by simp done
        apply simp
        apply (erule subst)
        apply (simp add: exec_instr_def exec_load_def eval_addrmode64_def Let_def)
        apply(subgoal_tac "bpf_to_x64_reg src \<noteq> REG_SCRATCH") 
         prefer 2 subgoal using reg_r11_consist by blast
         apply (rule conjI)
         apply (rule impI)
         apply simp
        apply(rule impI)
        using a9 apply(cases chk,simp_all)
        
(* 4. now we get exec_instr (one step of x64 add assembly), we prove the \<and>, first left, then right *)
         apply (rule conjI)
        subgoal
          using a0 a1 a2 a5 a6 a8 corr_pc_aux2 insert_iff prod_cases3 by metis
        unfolding a1 a2
(* 4.1  match_reg *)
         apply (simp add: match_state_def)
         apply(cases "loadv M64 xm (Vlong (scast off + xrs (IR (bpf_to_x64_reg src))))",simp_all)
        subgoal using load_m64_one_step_match_reg_1 a0 a1 a2 a3 a4 a5 a6 a8 a9 by (metis option.discI) 
        subgoal for a using a9 apply (cases a,simp_all) 
          subgoal using load_m64_one_step_match_reg_1 a0 a1 a2 a3 a4 a5 a6 a8 a9 apply (metis option.sel val.distinct(7)) done
          subgoal for x2 using load_m64_one_step_match_reg_2 a0 a1 a2 a3 a4 a5 a6 a8 a9 by metis
          subgoal for x3 using load_m64_one_step_match_reg_3 a0 a1 a2 a3 a4 a5 a6 a8 a9 by metis
          subgoal for x4 using load_m64_one_step_match_reg_4 a0 a1 a2 a3 a4 a5 a6 a8 a9 by metis
           prefer 2 subgoal for x61 x62 using load_m64_one_step_match_reg_5 a0 a1 a2 a3 a4 a5 a6 a8 a9 by metis
          subgoal for x5 
            apply(rule conjI)
            using load_M64_one_step_match_reg a0 a1 a2 a3 a4 a5 a6 a8 a9 apply auto[1]
(* 4.2  match_mem *)
            apply(rule conjI)
            using load_M64_one_step_match_mem a0 a1 a2 a3 a4 a5 a6 a8 a9 apply metis
(* 4.3  match_stack *)
            using load_M64_one_step_match_stack a0 a1 a2 a3 a4 a5 a6 a8 a9 apply auto
            using load_M64_one_step_match_stack2 a0 a1 a2 a3 a4 a5 a6 a8 a9 by (metis (no_types, lifting))
          done
        done
      done
    done
  done
end