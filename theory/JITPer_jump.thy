theory JITPer_jump
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux Proof1

begin


lemma jccq_subgoal_rr_aux3:"bins = BPF_JUMP cond dst (SOReg src) d \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m') \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow>
  \<forall> r. rs' r = rs r"
  apply(cases bins,simp_all)
  apply(cases "prog ! unat pc", simp_all)
  subgoal for x161 by(simp split:if_split_asm) 
  done


lemma jcc_subgoal_rr_generic:
  assumes a0:"bins = BPF_JUMP cond dst (SOReg src) d" and
       a1:"per_jit_jcc cond dst src (scast d) = Some (num, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (n, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = exec_instr xins sz spc reg xm" and
       a6:"match_state (SBPF_OK pc rs m) (pc, Next spc reg xm) " and
       a7:"prog!(unat pc) = bins" and
       a8:"cond = Eq"
  shows "match_state (SBPF_OK pc' rs' m') (pc', Next spc' reg' xm') "
proof -
  let "?tcond" = "Cond_e"
  have b0_1:"l_bin = (let ins1 = Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
      let ins2 = (Pjcc ?tcond 0) in x64_encode ins1@x64_encode ins2)" using a8 per_jit_jcc_def a1 a3 by simp 
  let "?l_bin1" = "x64_encode (Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))"
  let "?l_bin2" = "x64_encode (Pjcc ?tcond 0)"
  have d0:"list_in_list (?l_bin1@?l_bin2) (0::nat) l_bin" using list_in_list_prop b0_1 by metis
  have d0_0:"list_in_list l_bin 0 l_bin = list_in_list ?l_bin1 0 l_bin \<and> list_in_list ?l_bin2 (0 + length ?l_bin1) l_bin" 
       using list_in_list_concat d0 b0_1 list_in_list_prop by blast
  have d0_1:"list_in_list ?l_bin1 0 l_bin" using d0 d0_0 by auto
  hence b0:"xins = Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)"
      using x64_encode_decode_consistency a3 by (metis Pair_inject option.sel)
    
  moreover have b1:"(\<forall> r. (rs r) = reg (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def by simp
  have b2:"\<forall> r. reg' (IR (bpf_to_x64_reg r)) = reg (IR (bpf_to_x64_reg r))" using b0 a5 by (simp add: exec_instr_def compare_longs_def)
  have b3:"\<forall> r. (rs' r) = (rs r)" using a0 a4 a7 jccq_subgoal_rr_aux3 by blast
  have b4:"(\<forall> r. (rs' r) = reg' (IR (bpf_to_x64_reg r)))" using b1 b2 b3 by presburger
  have b8:"match_stack reg' xm'" using a6 match_state_def a5 b0 apply (simp add: exec_instr_def compare_longs_def) by(simp add:match_stack_def)
  have b9:"match_mem m' xm'" using match_state_def a6 a5 b0 apply (simp add: exec_instr_def) 
    using a4 mem_is_not_changed by blast
  thus ?thesis using b4  match_state_def b8 b9 match_reg_def by fastforce
qed

lemma jump_one_step:
  assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a8:"prog!(unat pc) = BPF_JUMP cond dst (SOReg src) x"
shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
proof-
    let "?bpf_ins" = "prog!(unat pc)"
    let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
    have c1_0:"?l_bin = snd (snd (the (per_jit_jcc cond dst src (scast x))))" using a8 per_jit_ins_def by auto
    let "?tcond" = "Cond_e"
    have c1_1:"cond = Eq" sorry
    have c1:"?l_bin = (let ins1 = Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src); ins2 = (Pjcc ?tcond 0) in x64_encode ins1@x64_encode ins2 )" 
      using c1_1 per_jit_jcc_def c1_0 by simp
    have c0:"?l_bin = snd (snd (the (per_jit_jcc cond dst src (scast x))))" using a8 per_jit_ins_def by fastforce

    have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
    then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto

    have c2:"l = ?l_bin" using a6 c0 a5 aux5 c_aux by fastforce
      
    let "?one_step" = "x64_sem1 1 x64_prog (pc,xst)"
    let "?st" = "snd ?one_step"
    have c2_1:"?st = snd (one_step x64_prog (pc,xst))" 
      by (metis One_nat_def prod.collapse x64_sem1.simps(1) x64_sem1.simps(2))

    have c3_0:"x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
    then have c3:"x64_prog!(unat pc) = the (per_jit_jcc cond dst src (scast x))" using a8 per_jit_ins_def by simp
    have c3_0:"per_jit_jcc cond dst src (scast x) = Some (num,off,l)" using c_aux c3 c1_1 per_jit_jcc_def by auto
    then have c3_1:"num = 1" using per_jit_jcc_def c1_1 c_aux by simp

    have e3_0:"off = scast x + 1" using c_aux per_jit_jcc_def c3 c1_1 by simp
    have e3:"off\<noteq>0" sorry
    have "?st = snd (let xst_temp = Next 0 xrs xm; xst' = x64_sem num l xst_temp in
        case xst' of Next xpc' rs' m' \<Rightarrow>
          if rs' (CR ZF) = 1 then (off+pc, xst')
          else (pc+1, xst') |
         Stuck \<Rightarrow> (pc, Stuck))" using c2_1 e3 a3 one_step_def c_aux by simp
    hence e3_1:"?st = x64_sem num ?l_bin (Next 0 xrs xm)" using c2_1 c_aux one_step_def e3 a3
      by (smt (verit, ccfv_threshold) c2 outcome.exhaust outcome.simps(4) outcome.simps(5) snd_conv) 

    let "?l_bin1" = "x64_encode (Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))"
    let "?l_bin2" = "x64_encode (Pjcc ?tcond 0)"
    have d0:"list_in_list (?l_bin1@?l_bin2) (0::nat) ?l_bin" using list_in_list_prop c1 by metis
    have d0_0:"list_in_list ?l_bin 0 ?l_bin = list_in_list ?l_bin1 0 ?l_bin \<and> list_in_list ?l_bin2 (0 + length ?l_bin1) ?l_bin" 
       using list_in_list_concat d0 c1 list_in_list_prop by blast
    have d0_1:"list_in_list ?l_bin1 0 ?l_bin" using d0 d0_0 by auto
    have d0_2:"list_in_list ?l_bin2 (0+length ?l_bin1) ?l_bin" using d0 d0_0 by auto
    hence "\<exists> xins1 sz1. x64_decode 0 ?l_bin = Some (sz1, xins1)" 
      by (metis c1 d0 list_in_list_concat x64_encode_decode_consistency)
    then obtain xins1 sz1 where d1:"x64_decode 0 ?l_bin = Some (sz1, xins1)" by auto
    have d2:"(sz1,xins1) = (3, Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))"  using d0_1 x64_encode_decode_consistency d1 by fastforce
    have c4:"?st = exec_instr xins1 (of_nat sz1) 0 xrs xm" using c3_1 d2 c1 c2 a3 d1 e3_1 by auto 
    have c6:"\<exists> xrs' xpc' xm'. ?st = Next xpc' xrs' xm'" using exec_instr_def spec c4 d2 by simp
    obtain xrs' xpc' xm' where c7:"?st = Next xpc' xrs' xm'" using c6 by auto
  
    have e0_1:"exec_instr xins1 (of_nat sz1) 0 xrs xm = Next (0+(of_nat sz1))(compare_longs (xrs (IR (bpf_to_x64_reg src))) (xrs (IR (bpf_to_x64_reg dst))) xrs) xm"
      using  exec_instr_def d2 a3 by simp
     
    hence e0:"let x = xrs (IR (bpf_to_x64_reg src)); y = xrs (IR (bpf_to_x64_reg dst)) in
     xrs' = ((((xrs#(CR ZF) <- (of_optbool (x = y)))
                            #(CR CF) <- (of_optbool (x < y)))
                            #(CR SF) <- (if scast(x-y) <s (0::i64) then 1 else 0))
                            #(CR OF) <- (sub_overflowi64 x y 0))"
      using c7 c4 d2 c4 a3 exec_instr_def of_optbool_def a8
      by (simp add: compare_longs_def)    
    hence e1:"xrs (IR (bpf_to_x64_reg dst)) = xrs (IR (bpf_to_x64_reg src)) \<longrightarrow>xrs' (CR ZF) = 1" 
      by (smt (verit, del_insts) crbit.distinct(1) crbit.distinct(5) crbit.distinct(7)  fun_upd_apply preg.inject(2) x64Semantics.of_optbool_def)
    have e2:"xrs (IR (bpf_to_x64_reg dst)) \<noteq> xrs (IR (bpf_to_x64_reg src)) \<longrightarrow>xrs' (CR ZF) = 0" 
      by (smt (verit, del_insts) crbit.distinct(1) crbit.distinct(5) crbit.distinct(7) e0 fun_upd_apply preg.inject(2) x64Semantics.of_optbool_def)

    have cn_1:"match_state s (pc,(Next 0 xrs xm))" using a4 match_state_eqiv a3 by blast  
    have cn:"x64_sem num l (Next 0 xrs xm) = ?st \<and> match_state s' (pc',?st)"
      using jcc_subgoal_rr_generic a0 a1 a2 c7 per_jit_jcc_def a8  c1_1 d1 c2 e3_1 c3_0 c3 c_aux e0_1 c4 cn_1 by metis
      
    have "x64_sem1 1 x64_prog (pc,xst) = (pc', Next xpc' xrs' xm')"
      using a8 e1 e2 cn a0 a1 a2 a3 a4 a5 a6 x64_sem1_pc_aux1 c_aux match_state_eqiv e3 c7 x64_sem1_pc_aux2 by auto
    then show ?thesis using a8 c2 match_state_eqiv c7 cn by fastforce
    qed

(*lemma ja_subgoal_rr_generic:
  assumes a0:"bins = BPF_JA d" and
       a1:"per_jit_ja (scast d) = Some (n, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = exec_instr xins sz spc reg xm" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg xm) " and
       a7:"prog!(unat pc) = bins"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' xm') "
proof -
    have b0:"xins = Pjmp 0" 
      using x64_encode_decode_consistency per_jit_ja_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def match_reg_def by simp
    have b2:"\<forall> r. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 by (simp add: exec_instr_def)
    have b3:"\<forall> r. (rs' r) = (rs r)" using a0 a4 a7 
      by (metis (no_types, lifting) bpf_instruction.simps(375) sbpf_state.distinct(3) sbpf_state.inject(1) sbpf_step.simps(1))
    have b4:"(\<forall> r. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b2 b3 by presburger
    have b8:"match_stack reg' xm'" using a6 match_state_def a5 b0 by (simp add: exec_instr_def)
    have b9:"match_mem m' xm'" using match_state_def a6 a5 b0 apply (simp add: exec_instr_def) 
      using a4 mem_is_not_changed by blast
    thus ?thesis using b4  match_state_def b8 b9 match_reg_def by fastforce
  qed*)
      
end