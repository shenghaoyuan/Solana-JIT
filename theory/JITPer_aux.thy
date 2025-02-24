theory JITPer_aux
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler Proof1
  JIT_def
begin

record JitProgram =
page_size     :: usize
pc_section    :: "usize list"
text_section  :: "x64_bin"

record jit_state =
jit_result :: JitProgram 
offset_in_text_section :: usize 
jit_pc :: usize

abbreviation "REG_SCRATCH::ireg \<equiv> R11"

definition bpf_to_x64_reg:: "bpf_ireg \<Rightarrow> ireg" where
  "bpf_to_x64_reg br = (
  case br of
  BR0 \<Rightarrow> RAX |
  BR1 \<Rightarrow> RDI |
  BR2 \<Rightarrow> RSI |
  BR3 \<Rightarrow> RDX |
  BR4 \<Rightarrow> RCX |
  BR5 \<Rightarrow> R8  |
  BR6 \<Rightarrow> RBX |
  BR7 \<Rightarrow> R13 |
  BR8 \<Rightarrow> R14 |
  BR9 \<Rightarrow> R15 |
  BR10 \<Rightarrow> RBP
)"

lemma bpf_to_x64_reg_corr2[simp]:" bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2  \<longrightarrow> r1 \<noteq> r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(cases r1; cases r2; simp)
  done

lemma bpf_to_x64_reg_corr[simp]:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(cases r1; cases r2; simp)
  done

definition update_pc_section_aux ::"usize list \<Rightarrow> nat \<Rightarrow> usize \<Rightarrow> usize list" where
"update_pc_section_aux pc_sec pc x = list_update pc_sec pc x"

subsection \<open> JIT rule \<close>

text \<open> return 
  - the number of jited x64 assembly code
  - the offset pointing to next pc
  - the jited x64 binary code \<close>
definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> i64 \<times> x64_bin) option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 1, x64_encode ins) 
)"

definition per_jit_exit :: "(nat \<times> i64 \<times> x64_bin) option" where
"per_jit_exit = (
  let ins = Pret in
    Some (1, 1, x64_encode ins) 
)"


(*definition per_jit_mul_reg64::"bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_mul_reg64 dst src \<equiv> let ins_list = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX] in
   map_option (\<lambda> l. (5, 1, l)) (x64_encodes_func_suffix ins_list)"*)

definition per_jit_mul_reg64::"bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> i64 \<times> x64_bin) option" where
"per_jit_mul_reg64 dst src \<equiv> 
  let ins_list = case (bpf_to_x64_reg dst) of 
      RAX \<Rightarrow> (x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))) |
      
      RDX \<Rightarrow> (x64_encode (Pmovq_rr R11 (bpf_to_x64_reg src))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX RDX)) 
                  @ (x64_encode (Pmulq_r R11))@ (x64_encode (Pmovq_rr RDX RAX))@ (x64_encode (Ppopl RAX)))|
      
      _   \<Rightarrow> (x64_encode(Pmovq_rr R11 (bpf_to_x64_reg src)))@(x64_encode (Ppushl_r RAX)) @ (x64_encode (Pmovq_rr RAX (bpf_to_x64_reg dst)))
                  @ (x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX))
                  @ (x64_encode (Pmovq_rr (bpf_to_x64_reg dst) RAX)) @ (x64_encode (Ppopl RAX))
  in let len = case (bpf_to_x64_reg dst) of 
    RAX \<Rightarrow> 4 |
    RDX \<Rightarrow> 6 |
    _ \<Rightarrow> 8
    in Some (len, 1, ins_list)"

definition per_jit_ja ::"i64 \<Rightarrow> (nat \<times> i64 \<times> x64_bin) option" where
  "per_jit_ja off \<equiv> let ins = (Pjmp (scast off)) in Some (1,off,x64_encode ins )"
                                               
fun per_jit_ins ::" bpf_instruction \<Rightarrow> (nat \<times> i64 \<times> x64_bin) option" where
"per_jit_ins bins = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  BPF_ALU64 BPF_MUL dst (SOReg src) \<Rightarrow> (per_jit_mul_reg64 dst src) |
  BPF_JA off \<Rightarrow> per_jit_ja (scast off) |
  _ \<Rightarrow> None
)"

fun jitper :: "ebpf_asm \<Rightarrow> (nat \<times> i64 \<times> x64_bin) list option" where
  "jitper [] = Some []" |
  "jitper (h#xs) = (case per_jit_ins h of 
                   None \<Rightarrow> None 
                 | Some (n, off, x) \<Rightarrow> 
                     (case jitper xs of 
                        None \<Rightarrow> None 
                      | Some res \<Rightarrow> Some ((n, off, x) # res)))"


value "(scast(-1::i16)::i64)"

value "(scast(-1::i16)::i64)+1::i64"

value "(ucast(-1::u16)::u64)+1::u64"

value "(-1::i16) + (1::i16)"

value "(-1::u16) + (1::u16)"

value "Some ((map the (map per_jit_ins [BPF_ALU64 BPF_ADD BR0 (SOReg BR6),BPF_ALU64 BPF_ADD BR0 (SOReg BR1)])))"

value "jitper [BPF_ALU64 BPF_SUB BR0 (SOReg BR6),BPF_EXIT]"

value "jitper [BPF_ALU64 BPF_MUL BR0 (SOReg BR6)]"

                
value "snd (snd ((the (jitper [BPF_EXIT,BPF_EXIT]))!(0::nat)))"

value "jitper []"

value "jitper [BPF_ALU64 BPF_SUB BR0 (SOReg BR6),BPF_ALU64 BPF_ADD BR0 (SOReg BR6)]"

value "jitper [BPF_ALU64 BPF_ADD BR0 (SOReg BR6),BPF_ALU64 BPF_SUB BR0 (SOReg BR6)]"

value "jitper [BPF_ALU64 BPF_ADD BR0 (SOReg BR6), BPF_ALU64 BPF_ADD BR0 (SOReg BR6), BPF_EXIT]"

value "per_jit_ins (BPF_ALU64 BPF_ADD BR0 (SOReg BR6))"


subsection \<open> simulation relation \<close>

definition match_stack :: "regset \<Rightarrow> mem \<Rightarrow> bool" where
"match_stack xrs m = (
  \<exists> v. Mem.loadv M64 m (Vlong ((xrs SP) + (u64_of_memory_chunk M64))) = Some (Vlong v))" (* v of Vlong or Vint?*)

text \<open> because jited x64 code may use pop and push to save registers,
then x64 memory has more info than sbpf memory \<close>

definition match_mem :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
"match_mem bm xm = (
  \<forall> mc addr v. (Mem.loadv mc bm (Vlong addr) = Some v) \<longrightarrow> (Mem.loadv mc xm (Vlong addr) = Some v))"

definition match_reg :: "reg_map \<Rightarrow> regset \<Rightarrow> bool" where
  "match_reg rm rs = (\<forall> r. (rm r) = rs (bpf_to_x64_reg r))"

definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> bool" where
"match_state bst xst = (
  case bst of
  SBPF_OK pc rs m \<Rightarrow> (
    case xst of
      Next xpc xrs xm \<Rightarrow>
        match_reg rs xrs \<and> \<comment>\<open> for ALU + MEM + Call \<close>
        match_mem m xm  \<comment>\<open> for MEM + Call \<close> \<and> 
        match_stack xrs xm |
      _ \<Rightarrow> False
  ) |
  SBPF_Success v \<Rightarrow>(
    case xst of
    Next xpc xrs xm \<Rightarrow> v = xrs (bpf_to_x64_reg BR0) \<comment>\<open> for EXIT \<close> |
      _ \<Rightarrow> False
  ) |
  _ \<Rightarrow> False
)"

lemma sbpf_sem_induct: 
  "sbpf_sem (m+n) prog s = s' \<Longrightarrow>
    \<exists> temps.
    sbpf_sem m prog s = temps \<and> 
    sbpf_sem n prog temps = s'"
  apply (induct m arbitrary: n prog s s')
  apply simp_all
  done

lemma sbpf_sem_add: 
  "sbpf_sem (m+n) prog s = s' \<Longrightarrow>
    s = (SBPF_OK pc rs mem) \<Longrightarrow>
    s'\<noteq> SBPF_Err \<Longrightarrow>
    \<exists> temps.
    sbpf_sem m prog s = temps \<and> 
    sbpf_sem n prog temps = s'"
  using sbpf_sem_induct by blast

lemma sbpf_sem_err: 
  "sbpf_sem (m+n) prog s = s' \<Longrightarrow>
    s = SBPF_Err \<Longrightarrow>
    \<exists> temps.
    sbpf_sem m prog s = temps \<and> 
    sbpf_sem n prog temps = s'"
  using sbpf_sem_induct by blast

lemma err_is_still_err:" sbpf_sem x prog SBPF_Err = s' \<Longrightarrow> s' = SBPF_Err "
  apply(induct x, simp)
  by auto

lemma suc_success_is_err:"x > 0 \<Longrightarrow> sbpf_sem x prog (SBPF_Success v) = s' \<Longrightarrow> s' = SBPF_Err "
  apply(induct x, simp)
  using err_is_still_err by force

lemma intermediate_step_is_ok:"sbpf_sem x prog s = s' \<Longrightarrow> x > 0 \<Longrightarrow> s' \<noteq> SBPF_Err \<Longrightarrow> \<exists> pc rs mem. s = (SBPF_OK pc rs mem)"
  apply(induct x arbitrary: prog s s')
  apply simp 
  using err_is_still_err suc_success_is_err
  by (metis sbpf_step.elims)



lemma reg_r11_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.R11"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma mem_is_not_changed:"s2 = sbpf_step prog s1 \<Longrightarrow> s1 = (SBPF_OK pc1 rs1 m1) \<Longrightarrow> s2 = (SBPF_OK pc2 rs2 m2) \<Longrightarrow> m1 = m2"
  apply(cases "prog!(unat pc1)", simp_all)
  subgoal for x11 x12 x13 
    by (metis bpf_instruction.simps(361) sbpf_state.simps(6))
  subgoal for x21 x22 x23 x24
    by (metis bpf_instruction.simps(362) sbpf_state.simps(6))
  subgoal for x31 x32 x33 x34 
    by (metis bpf_instruction.simps(363) sbpf_state.simps(6))
  subgoal for x4 
    by (metis bpf_instruction.simps(364) sbpf_state.distinct(3))
  subgoal for x51 x52 x53 
    by (metis bpf_instruction.simps(365) sbpf_state.simps(6))
  subgoal for x6 
    by (metis bpf_instruction.simps(366) sbpf_state.simps(6))
  subgoal for x71 x72
    by (metis bpf_instruction.simps(367) sbpf_state.simps(6))
  subgoal for x81 x82
    by (metis bpf_instruction.simps(368) sbpf_state.simps(6))
  subgoal for x91 x92 x93
    apply(split if_splits, simp_all)
    apply(split if_splits, simp_all)
    apply(cases x91, simp_all)
     apply(cases "eval_alu BPF_ADD x92 x93 rs1", simp_all)
    apply(cases "eval_alu BPF_MUL x92 x93 rs1",simp_all)
    done
  subgoal for x10
    by (metis bpf_instruction.simps(370) sbpf_state.simps(6))
  subgoal for x111 x112
    by (metis bpf_instruction.simps(371) sbpf_state.simps(6))
  subgoal for x121 x122 x123
    by (metis bpf_instruction.simps(372) sbpf_state.simps(6))
  subgoal for x131 x132 x133
    by (metis bpf_instruction.simps(373) sbpf_state.simps(6))
  subgoal for x141 x142 x143
    by (metis bpf_instruction.simps(374) sbpf_state.simps(6))
  subgoal for x15
    apply(split if_splits, simp_all)
    by(split if_splits, simp_all)
  subgoal for x161 x162 x163 x164
    by (metis bpf_instruction.simps(376) sbpf_state.simps(6))
  subgoal for x171 x172
    by (metis bpf_instruction.simps(377) sbpf_state.simps(6))
  subgoal for x181 x182
    by (metis bpf_instruction.simps(378) sbpf_state.simps(6))
  by (metis (no_types, lifting) bpf_instruction.simps(379) sbpf_state.distinct(1) sbpf_state.simps(6))             

(*lemma mem_is_not_changed2:"x64_sem 1 l xst1 = xst2 \<Longrightarrow> xst1 = Next xpc1 xrs1 m1 \<Longrightarrow> xst2 = Next xpc2 xrs2 m2 \<Longrightarrow> m1 = m2"
  apply(cases "x64_decode (unat xpc1) l", simp_all)
  subgoal for a apply(cases a, simp_all)
    subgoal for aa b
      apply(unfold exec_instr_def)
      apply (cases b, simp_all)
      apply(unfold exec_ret_def Let_def) 
      apply(cases "loadv M64 m1 (xrs1 SP + u64_of_memory_chunk M64)", simp_all)
      subgoal for ab apply(cases ab, simp_all)
        done
    done
  done
  done*)


lemma aux1:"length prog \<noteq> 0 \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow>
  s = (SBPF_OK pc rs m) \<Longrightarrow> 
  s' = (SBPF_OK pc' rs' m') \<Longrightarrow> 
  (\<exists> dst src. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> 
  prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src)) \<or> (\<exists> x. prog!(unat pc) = BPF_JA x)"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x91 x92 x93 
   apply(unfold eval_alu_def Let_def)
    apply(cases x91,simp_all) 
     apply(cases x93, simp_all)
     apply(cases x93, simp_all)
    done
  done

lemma aux2:"length prog \<noteq> 0 \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow>
  s = (SBPF_OK pc rs m) \<Longrightarrow> 
  s' \<noteq> SBPF_Err \<Longrightarrow> 
  \<exists> dst src. prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src),BPF_EXIT, BPF_ALU64 BPF_MUL dst (SOReg src)}
  \<or> (\<exists> x. prog!(unat pc) = BPF_JA x)"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x91 x92 x93 
   apply(unfold eval_alu_def Let_def)
    apply(cases x91,simp_all) 
     apply(cases x93, simp_all)
    apply(cases x93, simp_all)
    done
  done


lemma aux3:"jitper prog = Some x64_prog \<Longrightarrow> length x64_prog = length prog"
proof (induction prog arbitrary: x64_prog)
  case Nil
  then show ?case by simp
next
  case (Cons h xs)
  assume "jitper (h # xs) = Some x64_prog"
  then have a0:"\<exists> x. per_jit_ins h = Some x" using Cons(1) by (cases "per_jit_ins h"; auto)
  obtain x where a1:"per_jit_ins h = Some x" using a0 by auto
  then have a2:"\<exists> res. jitper xs = Some res" using Cons(1) apply (cases "jitper xs"; auto) 
    using Cons.prems(1) by force
  obtain res where a3:"jitper xs = Some res" using a2 by auto
  have a4:" x64_prog = x # res" using Cons(1) a3 a1
    using Cons.prems(1) by force
  then have a5:"length ( x64_prog) = length (h # xs)" using a4 Cons.IH a3 by fastforce
  then show ?case using Cons by simp
qed


value "[2::nat,3]!(unat (0::u64))"


lemma aux5:"jitper prog = Some x64_prog \<Longrightarrow> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow> x64_prog!(unat pc) = l_bin \<Longrightarrow> prog \<noteq> [] 
  \<Longrightarrow> l_bin = the (per_jit_ins bins)"
proof (induction prog arbitrary: x64_prog pc bins l_bin)
  case Nil
  then show ?case by simp
next
  case (Cons a prog)
  then show ?case
  proof-
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have "unat pc = 0" using True a0 by simp
      have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
      then have b2:"\<exists> res. jitper prog = Some res" using Cons(1) apply (cases "jitper prog"; auto) 
        using Cons.prems(1) by force
      obtain res where b3:"jitper prog = Some res" using b2 by auto
      have b4:"x64_prog = x # res" using Cons(1) b3 b1 Cons by force
      have bn:"l_bin = the (per_jit_ins bins)" using b1 b2 
        using Cons.prems(3) Cons.prems(4) True b4 by fastforce
      then show ?thesis using bn by blast
    next
      case False
      have "\<exists> res. jitper prog = Some res" using Cons 
        apply (cases "jitper prog"; simp_all) 
        apply(cases a, simp_all) 
        subgoal for x91 x92 x93 apply(cases x91,simp_all) 
           apply(cases x93,simp_all)
          subgoal for x2 apply(cases "per_jit_add_reg64_1 x92 x2",simp_all) 
            done 
          apply(cases x93,simp_all)
          subgoal for x2 apply(cases "per_jit_mul_reg64 x92 x2",simp_all)
            done 
          done
        apply(unfold per_jit_exit_def) 
         apply(cases per_jit_exit,simp_all) 
        subgoal for x15 by(cases "per_jit_ja (scast x15)",simp_all)
        subgoal for x15 aa by(cases "per_jit_ja (scast x15)",simp_all)
        done
      then obtain res where b0:"jitper prog = Some res" by auto
      have b1:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b2:"per_jit_ins a = Some x" using b1 by auto
      have c0:" Some (x # res) = Some x64_prog" using b0 b2 Cons by auto
      have c1:"unat pc \<ge> 1" using a0 False by blast
      have c2:"(a#prog) ! unat pc = bins" using c0 Cons.prems(3) by blast
      let "?pc'" = "unat pc -1"
      have c4:"0 \<le> ?pc' \<and> ?pc' < length prog \<and>
      prog ! ?pc' = bins \<and> res ! ?pc' = l_bin \<and> prog \<noteq> []" using Cons.prems(2) Cons.prems(3) Cons.prems(4) c0 c1 by auto
      (* have cn:"0 \<le> unat pc \<and> unat pc < length prog \<Longrightarrow> 
          prog ! unat pc = bins \<Longrightarrow> ?x ! unat pc = l_bin \<Longrightarrow> Some (snd (snd l_bin)) = per_jit_ins bins" using Cons
        by (metis (no_types, lifting) jit.simps(2) option.case_eq_if option.collapse)*)
      have c5:"l_bin = the (per_jit_ins bins)" using c4 Cons 
         False jitper.simps(2) order_neq_le_trans unat_gt_0 unat_minus_one
        by (metis (no_types, lifting) b0)
      then show ?thesis using c5 by blast
    qed
  qed
qed


(*lemma corr_pc_aux1:
  "jitper prog = Some x64_prog \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  prog!(unat pc) \<noteq> BPF_JA v \<Longrightarrow>
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  off=1"
proof (induction prog arbitrary: x64_prog pc v num off l)
  case Nil
  then show ?case by simp
next
  case (Cons a prog)
  then show ?case
  proof-
    assume assm1:"(a # prog) ! unat pc \<noteq> BPF_JA v"
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have b0_1:"unat pc = 0" using True a0 by simp
      have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
      have b1_1:"(num,off,l) = x" using b0_1 b1 True Cons
        by (smt (verit) jitper.simps(2) nth_Cons_0 old.prod.case option.case_eq_if option.discI option.sel prod_cases3)
      
      have "a \<noteq> BPF_JA v" using assm1 b0_1 by auto
      hence b2:"per_jit_ins a \<noteq> per_jit_ja (ucast v)" using b1 apply(cases a,simp_all)
        subgoal for x91 x92 x93 
          apply(cases x91,simp_all)
           apply(cases x93,simp_all)
          subgoal for x2 apply(unfold per_jit_add_reg64_1_def per_jit_ja_def Let_def ) sorry
        using b1 apply fastforce
      have bn:"off = 1"
        using b1 apply(cases "per_jit_ins a", simp_all) 
        subgoal for aa 
         apply(cases a,simp_all)
        subgoal for x91 x92 x93
          apply(cases x91,simp_all)
          apply(cases x93,simp_all)
          subgoal for x1 using b1 b1_1 per_jit_add_reg64_1_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x2 using b1 b1_1 per_jit_mul_reg64_def Let_def by auto
          done 
        subgoal for x15 using assm1 b0_1 apply(unfold per_jit_ja_def Let_def,simp_all) try 
        apply(unfold per_jit_exit_def Let_def, simp_all) using b1 b1_1 by blast
      done
      then show ?thesis using bn by blast
    next
      case False
      have "\<exists> res. jitper prog = Some res" using Cons 
        apply (cases "jitper prog"; simp_all) 
        apply(cases a, simp_all) 
        subgoal for x91 x92 x93 apply(cases x91,simp_all) 
          apply(cases x93,simp_all)
          subgoal for x2 apply(cases "per_jit_add_reg64_1 x92 x2",simp_all) 
            done 
          apply(cases x93,simp_all) 
          subgoal for x2 apply(cases "per_jit_mul_reg64 x92 x2",simp_all) 
            done
          done
        apply(unfold per_jit_exit_def) 
        apply(cases per_jit_exit,simp_all) 
        done
      then obtain res where b0:"jitper prog = Some res" by auto
      have b1:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b2:"per_jit_ins a = Some x" using b1 by auto
      have c0:" Some (x # res) = Some x64_prog" using b0 b2 Cons by auto
      have c1:"unat pc \<ge> 1" using a0 False by blast
      have c2:"x64_prog ! unat pc = (num,off,l)" using c0 Cons by simp
      let "?pc'" = "unat pc -1"
      have c3:"(num,off,l) = res! ?pc'" using c0 False c2 by auto
      have c4:"0 \<le> ?pc' \<and> ?pc' < length prog \<and> prog \<noteq> [] " using Cons c0 c1 by auto
      have c5:"off=1" using c3 c4 
        by (metis Cons.IH False b0 unat_minus_one unsigned_eq_0_iff)
      then show ?thesis by blast
    qed
  qed
qed
*)

lemma match_s_not_stuck:"match_state s xst \<Longrightarrow> xst \<noteq> Stuck"
  apply(cases s, simp_all)
  apply(unfold match_state_def)
  subgoal for x11 x12 x13 by auto
  subgoal for x2 by auto
  by simp

lemma x64_sem1_induct_aux1:"x64_sem1 (Suc n) pc x64_prog (Next xpc xrs m) = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs m) = xst1 \<Longrightarrow> 
  x64_sem1 n (ucast (scast pc+ off)) x64_prog xst1 = xst'"
 apply(induct n arbitrary:pc x64_prog xpc xrs m xst' num off l)
 apply simp 
  by simp

lemma x64_sem1_induct_aux2:"x64_sem1 n pc x64_prog (Next xpc xrs xm) = x64_sem1 n pc x64_prog (Next 0 xrs xm)"
proof(cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
    thus ?thesis using Suc by fastforce
qed
 
lemma x64_sem1_induct_aux3:"
  xst = (Next xpc xrs m) \<Longrightarrow>
  x64_sem1 (Suc n) pc x64_prog xst = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs m) = xst1 \<Longrightarrow> 
  xst1 = Next xpc1 xrs1 m1 \<Longrightarrow>
  x64_sem1 n (ucast (scast pc+ off)) x64_prog (Next 0 xrs1 m1) = xst'"
  using x64_sem1_induct_aux2 x64_sem1_induct_aux1 by metis

lemma pc_scope_aux:"\<lbrakk> sbpf_sem n prog s = s'; s = (SBPF_OK pc rs m); s' = (SBPF_OK pc' rs' m'); prog \<noteq> []; n>0\<rbrakk> \<Longrightarrow> 
  unat pc < length prog \<and> unat pc \<ge> 0"
  by (metis (no_types, opaque_lifting) err_is_still_err linorder_not_less not_gr_zero sbpf_sem.elims sbpf_state.simps(6) sbpf_step.simps(1))

(*
lemma num_is_1_aux:"jitper prog = Some x64_prog \<Longrightarrow> prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc \<Longrightarrow> 
  fst (x64_prog!(unat pc)) = 1"
proof (induction prog arbitrary:x64_prog pc)
  case Nil
  then show ?case by blast
next
  case (Cons a prog)
  then show ?case 
  proof-
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
    obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
    then have b2:"\<exists> res. jitper prog = Some res" using Cons(1) apply (cases "jitper prog"; auto) 
      using Cons.prems(1) by simp
    obtain res where b3:"jitper prog = Some res"  using b2 by blast
    have b4:"x64_prog = x # res" using Cons(1) b3 b1 Cons by force
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have b5:"unat pc = 0" using True a0 by simp
      have b6:"fst (the (per_jit_ins a)) = 1"  
        apply(cases "per_jit_ins a",simp_all)
        using b1 apply fastforce
        subgoal for aa apply(cases a,simp_all)
          subgoal for x91 x92 x93
            apply(cases x91, simp_all)
            apply(cases x93,simp_all)
            subgoal for x2 
              apply(unfold per_jit_add_reg64_1_def Let_def,simp_all) 
              using b5 by auto
            done
          apply(unfold per_jit_exit_def,simp_all)
          using b5 by auto
        done
      have b7:"the (per_jit_ins a) = x64_prog!(unat pc)" using b5 b1 b4 by auto
      then show ?thesis using b6 b7 by auto
    next
      case False
      have c0:" Some (x # res) = Some x64_prog" using b4 by blast
      have c1:"unat pc \<ge> 1" using a0 False by blast
      let "?pc'" = "unat pc -1"
      have c2:"0 \<le> ?pc' \<and> ?pc' < length prog \<and> prog \<noteq> []" using Cons 
        by (metis False One_nat_def c1 length_Cons less_diff_conv2 less_one list.size(3) list.size(4) zero_le)
      hence "fst (x64_prog ! unat pc) = 1" using c2 Cons False b3
        by (metis (no_types, lifting) b4 nth_Cons' unat_minus_one unsigned_eq_0_iff)
      then show ?thesis by blast
    qed
  qed
qed
*)


lemma corr_pc_aux2:
  "jitper prog = Some x64_prog \<Longrightarrow> prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  s =  SBPF_OK pc rs m \<Longrightarrow>
  s' = sbpf_step prog s \<Longrightarrow> s' = SBPF_OK pc' rs' m' \<Longrightarrow> 
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  pc' = ucast (scast pc+ off)"
  sorry
(*proof-
  assume assm0:"s' = sbpf_step prog s"  and
         assm1:"s' = SBPF_OK pc' rs' m'" and
         assm2:"jitper prog = Some x64_prog" and
         assm3:"prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog" and
         assm4:"s = SBPF_OK pc rs m" and
         assm5:"(num,off,l) = x64_prog!(unat pc)"
  have "\<exists> src dst. prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src), BPF_EXIT}" 
    using assm0 assm1 assm3 assm4 aux2 length_0_conv sbpf_state.simps(6) by (smt (verit, del_insts) insert_commute)
  then obtain src dst where c0:"prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src), BPF_EXIT}" by blast
  have c1:"pc' = pc+1" using c0 assm0 assm1 apply(cases "prog!(unat pc)",simp_all)
    prefer 2 using assm4 assm3 apply simp
    subgoal for x91 x92 x93 apply(erule disjE)
      using assm4 assm3 eval_alu_def apply simp 
      using assm4 assm3 eval_alu_def by simp
    done
  have "off=1" 
    using assm2 assm3 assm5 corr_pc_aux1 by blast
  thus ?thesis using c1 by simp
qed*)
  (*have "x64_prog!(unat pc) = the (per_jit_ins (prog!(unat pc)))" using aux5 assm2 assm3 assm5 by blast
  hence c2:"x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src) \<or> x64_prog!(unat pc) = the per_jit_exit" using c0 by auto
  hence c3:"off = (fst(snd(the (per_jit_add_reg64_1 dst src)))) \<or> off = (fst(snd(the (per_jit_exit))))" using assm5 by (metis split_pairs)
  thus ?thesis
  proof(cases "off = (fst(snd(the (per_jit_exit))))")
    case True
    have "off = 1" using per_jit_add_reg64_1_def True by auto
    then show ?thesis using c1 by simp
  next
    case True
    have "off = (fst(snd(the (per_jit_exit))))" using True c3 by blast
    hence "off = 1" using per_jit_exit_def Let_def try
    then show ?thesis using c1 by simp
  qed                                                   
qed*)

value "(x64_encode (Pmovq_rr R11 RBX)@(x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX)))"
(*[1001001,10001001,11011011,1010010,1001001,11110111,11100011,1011010]*)
end