theory JITPer_exit
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
  JITPer_aux

begin

lemma exit_subgoal_aux1:"s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow> 
  \<forall> r. r  \<notin> {BR6, BR7, BR8, BR9, BR10} \<longrightarrow> rs' r = rs r"
   apply(cases "prog!(unat pc)",simp_all)
  apply(split if_splits,simp_all)
  apply(unfold update_stack2_def Let_def eval_exit_def Let_def,simp_all)
  done

lemma exit_subgoal_aux2:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  xst' = snd (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  \<forall> r. r  \<notin> {BR6, BR7, BR8, BR9, BR10} \<longrightarrow> xrs1 (IR (bpf_to_x64_reg r)) = xrs (IR (bpf_to_x64_reg r))"
  apply(unfold update_stack2_def Let_def restore_x64_caller_def Let_def,simp_all)
  using bpf_to_x64_reg_corr bpf_to_x64_reg_def
  by (smt (z3) bpf_ireg.simps(117) bpf_ireg.simps(118) bpf_ireg.simps(119) bpf_ireg.simps(120) bpf_ireg.simps(121) fun_upd_other preg.inject(1))
   

lemma exit_reg_subgoal_aux3:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  xst' = snd (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow> 
  \<forall> r. xrs (IR (bpf_to_x64_reg r)) = rs r \<Longrightarrow> ss = xss \<Longrightarrow> 
  \<forall> r. r \<notin> {BR6, BR7, BR8, BR9, BR10} \<longrightarrow> xrs1 (IR (bpf_to_x64_reg r)) = rs' r "
proof -
  assume a1: "xst' = Next xpc1 xrs1 xm1 xss1"
  assume a2: "xst' = snd (let (xpc', xss', caller, fp) = update_stack2 xss; xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss'))"
  assume a3: "s' = sbpf_step prog s"
  assume a4: "s = SBPF_OK pc rs m ss"
  assume a5: "s' = SBPF_OK pc' rs' m' ss'"
  assume a6: "prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc"
  assume a7: "prog ! unat pc = BPF_EXIT"
  assume a8: "\<forall>r. xrs (IR (bpf_to_x64_reg r)) = rs r"
    have "\<forall>f s w fa b. b \<in> {BR6, BR7, BR8, BR9, BR10} \<or> fa (IR (bpf_to_x64_reg b)) = xrs (IR (bpf_to_x64_reg b)) \<or> xst' \<noteq> Next w fa f s"
    using a2 exit_subgoal_aux2 by blast
    then show ?thesis
    using a8 a7 a6 a5 a4 a3 a1  exit_subgoal_aux1 by metis
qed


lemma exit_reg_subgoal_aux4:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  xst' = snd (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow> 
  \<forall> r. xrs (IR (bpf_to_x64_reg r)) = rs r \<Longrightarrow> ss = xss \<Longrightarrow> 
  \<forall> r. r \<in> {BR6, BR7, BR8, BR9, BR10} \<longrightarrow> xrs1 (IR (bpf_to_x64_reg r)) = rs' r "
 apply(cases "prog!(unat pc)",simp_all)
  apply(split if_splits,simp_all)
  apply(unfold update_stack2_def Let_def eval_exit_def Let_def,simp_all)
 apply(unfold restore_x64_caller_def Let_def,simp_all)
  using bpf_to_x64_reg_corr bpf_to_x64_reg_def
   apply(subgoal_tac "caller_saved_registers ((call_frames ss)!0) = caller_saved_registers ((call_frames xss)!0)")
    apply force
   apply blast
  done
 
lemma exit_reg_subgoal_aux5:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  xst' = snd (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow> 
  \<forall> r. xrs (IR (bpf_to_x64_reg r)) = rs r \<Longrightarrow> ss = xss \<Longrightarrow>
  \<forall> r. xrs1 (IR (bpf_to_x64_reg r)) = rs' r "
  apply(subgoal_tac  "\<forall> r. r \<in> {BR6, BR7, BR8, BR9, BR10} \<or> r \<notin> {BR6, BR7, BR8, BR9, BR10}" )
  prefer 2 apply blast
  using exit_reg_subgoal_aux4  exit_reg_subgoal_aux3 by metis
(*proof -
  assume a1: "xst' = Next xpc1 xrs1 xm1 xss1"
  assume a2: "xst' = snd (let (xpc', xss', caller, fp) = update_stack2 xss; xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss'))"
  assume a3: "s' = sbpf_step prog s"
  assume a4: "s = SBPF_OK pc rs m ss"
  assume a5: "s' = SBPF_OK pc' rs' m' ss'"
  assume a6: "prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc"
  assume a7: "prog ! unat pc = BPF_EXIT"
  assume a8: "\<forall>r. xrs (IR (bpf_to_x64_reg r)) = rs r"
  assume a9: "ss = xss"
  obtain bb :: "(preg \<Rightarrow> 64 word) \<Rightarrow> (bpf_ireg \<Rightarrow> 64 word) \<Rightarrow> bpf_ireg" where
    f10: "\<forall>X2 X3. (\<exists>X21. X3 (IR (bpf_to_x64_reg X21)) \<noteq> X2 X21) \<longrightarrow> X2 (bb X3 X2) \<noteq> X3 (IR (bpf_to_x64_reg (bb X3 X2)))"
    by (smt (z3)) (* failed *)
  obtain bba :: "(bpf_ireg \<Rightarrow> 64 word) \<Rightarrow> (preg \<Rightarrow> 64 word) \<Rightarrow> bpf_ireg" where
    f11: "\<forall>X3 X14. (\<exists>X21. X3 (IR (bpf_to_x64_reg X21)) \<noteq> X14 X21) \<longrightarrow> X14 (bba X14 X3) \<noteq> X3 (IR (bpf_to_x64_reg (bba X14 X3)))"
    by (smt (z3)) (* failed *)
  have "\<forall>z f fa fb fc fd w s wa fe bs sa wb ff sb sc fg wc sd se. \<not> 0 \<le> unat wb \<or> SBPF_OK w fc fd sb \<noteq> sa \<or> \<not> unat wb < length bs \<or> (\<forall>b. fc b = f (IR (bpf_to_x64_reg b)) \<or> b \<in> {BR6, BR7, BR8, BR9, BR10}) \<or> (\<exists>b. fb (IR (bpf_to_x64_reg b)) \<noteq> fa b) \<or> SBPF_OK wb fa fg sd \<noteq> s \<or> Next wc f fe se \<noteq> z \<or> sc \<noteq> sd \<or> snd (case update_stack2 sc of (w, s, ws, wb) \<Rightarrow> (w, Next wa (restore_x64_caller fb ws wb) ff s)) \<noteq> z \<or> sbpf_step bs s \<noteq> sa \<or> bs ! unat wb \<noteq> BPF_EXIT \<or> [] = bs"
    by (metis (no_types) exit_reg_subgoal_aux3)
  then obtain bbb :: "(preg \<Rightarrow> 64 word) \<Rightarrow> (bpf_ireg \<Rightarrow> 64 word) \<Rightarrow> bpf_ireg" where
    f12: "\<forall>z f fa fb fc fd w s wa fe bs sa wb ff sb sc fg wc sd se. \<not> 0 \<le> unat wb \<or> SBPF_OK w fc fd sb \<noteq> sa \<or> \<not> unat wb < length bs \<or> (\<forall>b. fc b = f (IR (bpf_to_x64_reg b)) \<or> b \<in> {BR6, BR7, BR8, BR9, BR10}) \<or> fa (bbb fb fa) \<noteq> fb (IR (bpf_to_x64_reg (bbb fb fa))) \<or> SBPF_OK wb fa fg sd \<noteq> s \<or> Next wc f fe se \<noteq> z \<or> sc \<noteq> sd \<or> snd (case update_stack2 sc of (w, s, ws, wb) \<Rightarrow> (w, Next wa (restore_x64_caller fb ws wb) ff s)) \<noteq> z \<or> sbpf_step bs s \<noteq> sa \<or> bs ! unat wb \<noteq> BPF_EXIT \<or> [] = bs"
    using f10 by (smt (z3)) (* > 1.0 s, timed out *)
  have "\<forall>f w s fa fb sa sb z fc bs wa fd sc fe ff wb fg sd wc se. SBPF_OK w fb fc sd \<noteq> se \<or> [] = bs \<or> BPF_EXIT \<noteq> bs ! unat wc \<or> s \<noteq> sa \<or> Next wb fg fd sc \<noteq> z \<or> snd (case update_stack2 s of (w, s, ws, wb) \<Rightarrow> (w, Next wa (restore_x64_caller fa ws wb) f s)) \<noteq> z \<or> (\<forall>b. b \<notin> {BR6, BR7, BR8, BR9, BR10} \<or> fb b = fg (IR (bpf_to_x64_reg b))) \<or> sbpf_step bs sb \<noteq> se \<or> \<not> 0 \<le> unat wc \<or> \<not> unat wc < length bs \<or> SBPF_OK wc ff fe sa \<noteq> sb \<or> (\<exists>b. fa (IR (bpf_to_x64_reg b)) \<noteq> ff b)"
    by (metis (no_types) exit_reg_subgoal_aux4)
  then obtain bbc :: "(bpf_ireg \<Rightarrow> 64 word) \<Rightarrow> (preg \<Rightarrow> 64 word) \<Rightarrow> bpf_ireg" where
    f13: "\<forall>f w s fa fb sa sb z fc bs wa fd sc fe ff wb fg sd wc se. SBPF_OK w fb fc sd \<noteq> se \<or> [] = bs \<or> BPF_EXIT \<noteq> bs ! unat wc \<or> s \<noteq> sa \<or> Next wb fg fd sc \<noteq> z \<or> snd (case update_stack2 s of (w, s, ws, wb) \<Rightarrow> (w, Next wa (restore_x64_caller fa ws wb) f s)) \<noteq> z \<or> (\<forall>b. b \<notin> {BR6, BR7, BR8, BR9, BR10} \<or> fb b = fg (IR (bpf_to_x64_reg b))) \<or> sbpf_step bs sb \<noteq> se \<or> \<not> 0 \<le> unat wc \<or> \<not> unat wc < length bs \<or> SBPF_OK wc ff fe sa \<noteq> sb \<or> ff (bbc ff fa) \<noteq> fa (IR (bpf_to_x64_reg (bbc ff fa)))"
    using f11 by (smt (z3)) (* > 1.0 s, timed out *)
  have f14: "\<forall>f sa b w wa fa sb fb fc fd bs wb. b \<in> {BR6, BR7, BR8, BR9, BR10} \<or> sbpf_step bs s \<noteq> SBPF_OK w fa f sa \<or> fb (IR (bpf_to_x64_reg b)) = fa b \<or> BPF_EXIT \<noteq> bs ! unat pc \<or> xm \<noteq> fc \<or> xpc \<noteq> wa \<or> xst' \<noteq> Next wb fb fd sb \<or> [] = bs \<or> \<not> unat pc < length bs"
    using f12 a9 a8 a6 a4 a2 by (metis (no_types))
  have "\<forall>f fa fb bs w wa sa fc b fd sb wb. [] = bs \<or> b \<notin> {BR6, BR7, BR8, BR9, BR10} \<or> xm \<noteq> fb \<or> f b = fc (IR (bpf_to_x64_reg b)) \<or> BPF_EXIT \<noteq> bs ! unat pc \<or> SBPF_OK wa f fa sb \<noteq> sbpf_step bs s \<or> xst' \<noteq> Next wb fc fd sa \<or> \<not> unat pc < length bs \<or> xpc \<noteq> w"
    using f13 a9 a8 a6 a4 a2 by (metis (no_types))
  then show ?thesis
    using f14 a7 a6 a5 a3 a1 by (metis (full_types))
qed *)


lemma exit_reg_subgoal_aux6:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  xst' = snd (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow> 
  match_mem m xm \<Longrightarrow>
  match_mem m' xm1"
 apply(cases "prog!(unat pc)",simp_all)
  apply(split if_splits,simp_all)
  apply(unfold update_stack2_def Let_def eval_exit_def Let_def,simp_all)
  done


lemma exit_reg_subgoal_aux7:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  xst' = snd (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow> 
  xss = ss \<Longrightarrow>
  xss1 = ss'"
 apply(cases "prog!(unat pc)",simp_all)
  apply(split if_splits,simp_all)
  apply(unfold update_stack2_def Let_def eval_exit_def Let_def,simp_all)
  done


lemma exit_reg_subgoal_aux8:"xst' = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow> 
  t_pc = fst (let (xpc', xss', caller,fp) = update_stack2 xss in 
          let xrs' = restore_x64_caller xrs caller fp in (xpc', Next xpc xrs' xm xss')) \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow> s = (SBPF_OK pc rs m ss) \<Longrightarrow> s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> prog!(unat pc) = BPF_EXIT \<Longrightarrow>
  xss = ss \<Longrightarrow>  
  pc' = t_pc "
 apply(cases "prog!(unat pc)",simp_all)
  apply(split if_splits,simp_all)
  apply(unfold update_stack2_def Let_def eval_exit_def Let_def pop_frame_def ,simp_all)
  done
 
lemma exit_one_step:
  assumes a0:"prog!(unat pc) = BPF_EXIT" and
       a1:"jitper prog = Some x64_prog" and
       a2:"s = SBPF_OK pc rs m ss" and
       a3:"s' = SBPF_OK pc' rs' m' ss'" and
       a4:"sbpf_step prog s = s'" and
       a5:"xst = Next xpc xrs xm xss" and
       a6:"match_state s (pc,xst) " and
       a7:"prog!(unat pc) = bins" and
       a8:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0"
     shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
proof-
  have b0:"\<not> (call_depth ss = 0)" using a0 a4 a7 a8 a4 a3 a2 by auto

  let "?bpf_ins" = "prog!(unat pc)"
  let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
  have c1_0:"?l_bin = snd (snd (the (per_jit_exit)))" using a0 per_jit_ins_def by auto
   have c0:"?l_bin = snd (snd (the (per_jit_exit)))" using a0 per_jit_ins_def by fastforce
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto
  have c2:"l = ?l_bin" using a8 c0 a1 aux5 c_aux by fastforce
      
  let "?one_step" = "x64_sem1 1 x64_prog (pc,xst)"
  let "?st" = "snd ?one_step"
  have c2_1:"?st = snd (one_step x64_prog (pc,xst))" 
      by (metis One_nat_def prod.collapse x64_sem1.simps(1) x64_sem1.simps(2))

  have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a1 a8 by blast
  hence c3:"x64_prog!(unat pc) = the (per_jit_exit)" using a0 per_jit_ins_def by simp
  have c3_0:"per_jit_exit = Some (num,off,l)" using c_aux c3 by (simp add: per_jit_exit_def) 

  have c4: "l!0 = 0xc3 " using c_aux c3 c3_0 apply(unfold per_jit_exit_def x64_encode_def)
    apply(cases Pret,simp_all) by auto

  have c4_1:"\<not>(l!0 = 0xff \<or> (l!0 = 0x40 \<and> l!1 = 0xff))" using c4 by simp

  have c5:"?one_step = (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss'))" using c4 c4_1 one_step_def a5 c_aux c2_1 
    by (smt (z3) One_nat_def case_prod_conv fst_conv outcome.simps(4) snd_conv update_stack2_def x64_sem1.simps(1) x64_sem1.simps(2))

  have "\<exists> xpc1 xrs1 xm1 xss1. Next xpc1 xrs1 xm1 xss1 = ?st" using a5 c5 restore_x64_caller_def update_stack2_def c2_1 
    by (metis (mono_tags, lifting) case_prod_conv snd_conv)
  then obtain xpc1 xrs1 xm1 xss1 where c6:"Next xpc1 xrs1 xm1 xss1 = ?st" by auto
  
  have d0:"ss = xss" using a0 a4 a6 match_state_def a5 a2 by simp

  have d1:"(call_frames ss)!0 = (call_frames xss)!0" using d0 by blast

  have d2:"(\<forall> r. (rs  r) = xrs (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def a4 a5 a2 by simp
  
  have "\<forall> r. xrs1 (IR (bpf_to_x64_reg r)) = rs' r " using exit_reg_subgoal_aux5 a4 c6 c5 c2_1 a0 a4 a5 d2 d0 a8 a2 a3 by metis
  hence e1:"match_reg rs' xrs1" using match_reg_def by auto

  have e2:"ss' = xss1" using  exit_reg_subgoal_aux7 c6 c5 a2 a3 a4 a0 d0 a8 by metis
    
  have e3_1:"xrs1 (IR SP) = xrs (IR SP)" using c6 c5 a5 by(unfold update_stack2_def restore_x64_caller_def Let_def,simp_all) 
  have e3_2:"match_stack xrs" using a6 a2 a5  by (simp add: match_state_def)
  have e3:"match_stack xrs1" using e3_1 e3_2 match_stack_def by simp

  have e4_1:"match_mem m xm" using a6 a2 a5  by (simp add: match_state_def)
  have e4:"match_mem m' xm1" using exit_reg_subgoal_aux6 a4 c6 c5 a0 a8 a2 a3 e4_1 by metis

  have e5:"match_state s' (pc',?st)" using c6 a4 e1 e2 e3 e4 match_state_def a3 match_mem_def match_stack_def match_reg_def a0 a2 a3 a4 a5 
      by (smt (verit) fst_conv outcome.simps(4) sbpf_state.simps(9) snd_conv)

  let "?t_pc" = "fst ?one_step"
  have e6_1:"?t_pc = fst(let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss'))" using c5 by simp
  have e6:"?t_pc = pc'" using exit_reg_subgoal_aux8 c6 e6_1 a2 a3 a4 a0 d0 a8 by fast
  then show ?thesis using e5 by (metis split_pairs)
qed
(*
lemma exit_subgoal_rr_generic:
  assumes a0:"prog!(unat pc) = BPF_EXIT" and
       a1:"jitper prog = Some x64_prog" and
       a4:"sbpf_step prog (SBPF_OK pc rs m ss) = st'" and
       a5:"xst = Next xpc xrs xm xss" and
       a6:"match_state (SBPF_OK pc rs m ss) (pc,xst) " and
       a7:"prog!(unat pc) = bins" and
       a8:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0"
     shows "\<exists> xst'. x64_sem1 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state st' (pc',xst')"
proof-
  have "st' =  (if call_depth ss = 0 then SBPF_Success (rs BR0)
      else (let (pc', rs', ss') = eval_exit rs ss in SBPF_OK pc' rs' m ss'))"  using a0 a4 a7 a8 by simp
  hence b0:"st' = SBPF_Success (rs BR0) \<or> (\<exists> pc' rs' m' ss'. st' = SBPF_OK pc' rs' m' ss')"
    using a0 a4 a7 a8 eval_exit_def 
    by (metis (no_types, lifting) case_prod_conv old.prod.exhaust)

  let "?bpf_ins" = "prog!(unat pc)"
  let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
  have c1_0:"?l_bin = snd (snd (the (per_jit_exit)))" using a0 per_jit_ins_def by auto
   have c0:"?l_bin = snd (snd (the (per_jit_exit)))" using a0 per_jit_ins_def by fastforce
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where c_aux:"x64_prog!(unat pc) = (num,off,l)" by auto
  have c2:"l = ?l_bin" using a8 c0 a1 aux5 c_aux by fastforce
      
  let "?one_step" = "x64_sem1 1 x64_prog (pc,xst)"
  let "?st" = "snd ?one_step"
  have c2_1:"?st = snd (one_step x64_prog (pc,xst))" 
      by (metis One_nat_def prod.collapse x64_sem1.simps(1) x64_sem1.simps(2))

  have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a1 a8 by blast
  hence c3:"x64_prog!(unat pc) = the (per_jit_exit)" using a0 per_jit_ins_def by simp
  have c3_0:"per_jit_exit = Some (num,off,l)" using c_aux c3
    by (simp add: per_jit_exit_def) 

  have c4: "l!0 = 0xc3" using c_aux c3 c3_0 apply(unfold per_jit_exit_def x64_encode_def)
    apply(cases Pret,simp_all) by auto

  have c5:"?one_step = (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss'))" using c4 one_step_def a5 c_aux c2_1 sorry

  have "\<exists> xpc1 xrs1 xm1 xss1. Next xpc1 xrs1 xm1 xss1 = ?st" using a5 c5 restore_x64_caller_def update_stack2_def c2_1 
    by (metis (mono_tags, lifting) case_prod_conv snd_conv)
  then obtain xpc1 xrs1 xm1 xss1 where c6:"Next xpc1 xrs1 xm1 xss1 = ?st" by auto

  
  have d0:"ss = xss" using a0 a4 a6 match_state_def a5 by simp

  have d1:"(call_frames ss)!0 = (call_frames xss)!0" using d0 by blast

  have d2:"(\<forall> r. (rs  r) = xrs (IR (bpf_to_x64_reg r)))" using a6 spec match_state_def match_reg_def a4 a5 by simp
  
  thus ?thesis
  proof(cases "call_depth ss = 0")
    case True
    have c1:"call_depth xss = 0" using True d0 by blast
    have c2:"st' = SBPF_Success (rs BR0)" using True a0 a6 a7 a8 
      using \<open>st' = (if call_depth ss = 0 then SBPF_Success (rs BR0) else let (pc', rs', ss') = eval_exit rs ss in SBPF_OK pc' rs' m ss')\<close> by argo
    have d3:"(rs BR0) = xrs (IR (bpf_to_x64_reg BR0))" using a6 spec d2 by simp  
    have d4:"xrs (IR (bpf_to_x64_reg BR0)) =  xrs1 (IR (bpf_to_x64_reg BR0))" using exit_subgoal_aux2 c5 c6 by fastforce
   
    (*hence b5_1:"\<exists> v. Mem.loadv M64 m (Vlong ((reg (IR SP)) + (u64_of_memory_chunk M64))) = Some (Vlong v)" using match_state_def a6 match_stack_def True try
    obtain v where b5_2:"Mem.loadv M64 m (Vlong ((reg (IR SP)) + (u64_of_memory_chunk M64))) = Some (Vlong v)" using b5_1 by blast*)    
    (*let "?reg'" = "(reg#(IR SP) <- ((reg (IR SP)) + (u64_of_memory_chunk M64)))"
    have b5_3:"xst' = Next v ?reg' m" using exec_instr_def exec_ret_def a5 b1 b5_2 by simp
    hence b5:"?reg' (IR (bpf_to_x64_reg BR0)) = reg (IR (bpf_to_x64_reg BR0))" by (simp add: bpf_to_x64_reg_def)
    thus ?thesis using exec_instr_def b3 b1 b0 a5 using b5_2 exec_ret_def match_state_def by force*)
      then show ?thesis using d4 d3 c2 match_state_def c6 sorry
  next
    case False
    have "\<exists> pc' rs' m' ss'. SBPF_OK pc' rs' m' ss' = st'" using False b0 
      by (metis (no_types, lifting) \<open>st' = (if call_depth ss = 0 then SBPF_Success (rs BR0) else let (pc', rs', ss') = eval_exit rs ss in SBPF_OK pc' rs' m ss')\<close> case_prod_conv old.prod.exhaust)
    then obtain pc' rs' m' ss' where e0:"SBPF_OK pc' rs' m' ss' = st'" by auto
    have "\<forall> r. xrs1 (IR (bpf_to_x64_reg r)) = rs' r " using exit_reg_subgoal_aux5 e0 c6 c5 c2_1 a0 a4 a5 d2 d0 a8 by metis
    hence e1:"match_reg rs' xrs1" using match_reg_def by auto
    have e2:"ss' = xss1" using d0 c5 c6 e0 False \<open>st' = (if call_depth ss = 0 then SBPF_Success (rs BR0) else let (pc', rs', ss') = eval_exit rs ss in SBPF_OK pc' rs' m ss')\<close> sorry
    have e3:"match_stack xrs1" sorry
    have e4:"match_mem m' xm1" sorry
    have e5:"fst ?one_step = pc'" sorry
    then show ?thesis using c6 e0 e1 e2 e3 e4 e5 match_state_def sorry
  qed
  
qed
*)
end