section \<open> JIT-Per: translate SBPF assembly to IR1 \<close>

text\<open> IR1 is a list-list binary code:
- each SBPF assembly is mapped a list of binary code
    where SBPF_JUMP ofs is set to 0 in the target binary 
- SBPF assembly and IR1 have the same pc value because JIT-Per is one-by-one 

SBPF: 0: BPF_ADD; 1: BPF_SUB; 2: BPF_EXIT

x64:  0:[add...]; 1:[sub...]; 2: [ret...]
 \<close>

theory JITPer
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler Proof1
  JITState

begin


subsection \<open> JIT rule \<close>

text \<open> return 
  - the number of jited x64 assembly code
  - the offset pointing to next pc
  - the jited x64 binary code \<close>
definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    map_option (\<lambda> l. (1, 1, l)) (x64_encode ins)
)"

definition per_jit_exit :: "(nat \<times> u64 \<times> x64_bin) option" where
"per_jit_exit = (
  let ins = Pret in
    map_option (\<lambda> l. (1, 1, l)) (x64_encode ins)
)"


(*definition per_jit_mul_reg64::"bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_mul_reg64 dst src \<equiv> let ins_list = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX] in
   map_option (\<lambda> l. (5, 1, l)) (x64_encodes_func_suffix ins_list)"*)

definition per_jit_mul_reg64::"bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_mul_reg64 dst src \<equiv> let ins_list = case (bpf_to_x64_reg dst) of
    RAX \<Rightarrow> [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]|
    RDX \<Rightarrow> [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RAX, Pmovq_rr RAX RDX, Pmulq_r R11, Pmovq_rr RDX RAX, Ppopl RAX]|
    _   \<Rightarrow> [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RAX, Pmovq_rr RAX (bpf_to_x64_reg dst), Ppushl_r RDX, Pmulq_r R11, 
            Ppopl RDX, Pmovq_rr (bpf_to_x64_reg dst) RAX, Ppopl RAX]
  in map_option (\<lambda> l. (length ins_list, 1, l)) (x64_encodes2 ins_list)"


fun per_jit_ins ::" bpf_instruction \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_ins bins = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  BPF_ALU64 BPF_MUL dst (SOReg src) \<Rightarrow> (per_jit_mul_reg64 dst src) |
  _ \<Rightarrow> None
)"

fun jitper :: "ebpf_asm \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list option" where
  "jitper [] = Some []" |
  "jitper (h#xs) = (case per_jit_ins h of 
                   None \<Rightarrow> None 
                 | Some (n, off, x) \<Rightarrow> 
                     (case jitper xs of 
                        None \<Rightarrow> None 
                      | Some res \<Rightarrow> Some ((n, off, x) # res)))"

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
  \<exists> v. Mem.loadv M64 m ((xrs SP) + (u64_of_memory_chunk M64)) = Some (Vlong v))"

text \<open> because jited x64 code may use pop and push to save registers,
then x64 memory has more info than sbpf memory \<close>
definition match_mem :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
"match_mem bm xm = (
  \<forall> mc addr v. (Mem.loadv mc bm addr = Some v) \<longrightarrow> (Mem.loadv mc xm addr = Some v))"

definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> bool" where
"match_state bst xst = (
  case bst of
  SBPF_OK pc rs m \<Rightarrow> (
    case xst of
      Next xpc xrs xm \<Rightarrow>
        (\<forall> r. (rs r) = xrs (bpf_to_x64_reg r)) \<and> \<comment>\<open> for ALU + MEM + Call \<close>
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

lemma x64_sem_add_stuck : 
" x64_sem (m + n) x64_prog Stuck = xst' \<Longrightarrow>
  x64_sem n x64_prog (x64_sem m x64_prog Stuck) = xst'"
  apply (cases m,simp)
  subgoal for m
    apply(cases n,simp)
    by auto
  done

lemma x64_sem_add: 
  "x64_sem (m+n) x64_prog xst = xst' \<Longrightarrow>
    xst = (Next pc rs ms) \<Longrightarrow>
    \<exists> xst1.
    x64_sem m x64_prog xst = xst1 \<and> 
    x64_sem n x64_prog xst1 = xst'"
  apply (induction m arbitrary: n x64_prog xst xst' pc rs ms)
  subgoal by simp
  subgoal for m n x64_prog xst xst' pc rs ms
    apply simp
    apply (cases "x64_decode (unat pc) x64_prog"; simp)
    subgoal by (cases n; simp)
    subgoal for ins1
      apply (cases ins1; simp)
      subgoal for sz ins
        apply (cases "(exec_instr ins (word_of_nat sz) pc rs ms)"; simp)
        apply (erule x64_sem_add_stuck)
        done
      done
    done
  done

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

lemma aluq_subgoal_rr_aux1:
     "bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow>
     xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')  \<Longrightarrow>
     Next spc' reg' xm' = exec_instr xins sz spc reg xm \<Longrightarrow>
     reg (bpf_to_x64_reg dst) = rs dst \<Longrightarrow>
     reg (bpf_to_x64_reg src) = rs src \<Longrightarrow>
     reg' (bpf_to_x64_reg dst) = (rs' dst)"
  apply (unfold exec_instr_def step)
  apply simp
  apply(cases "prog ! unat pc",simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done


lemma aluq_subgoal_rr_aux2_1:"xins = Paddq_rr dst src \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' r = reg r"
  by (simp add: exec_instr_def)


lemma aluq_subgoal_rr_aux2:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r \<noteq> dst. reg' (bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)"
  using aluq_subgoal_rr_aux2_1 by simp


lemma aluq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_ADD dst (SOReg src) \<Longrightarrow> 
  sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m') \<Longrightarrow> 
  prog!(unat pc) = bins \<Longrightarrow>
  \<forall> r \<noteq> dst. rs' r = rs r"
  apply(cases bins,simp_all)
  apply(cases "prog ! unat pc", simp_all)
  subgoal for x91 apply(simp split:if_split_asm) 
    apply(unfold eval_alu_def eval_reg_def,simp_all)
    by auto
  done

lemma stack_is_not_changed_by_add:"Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow> xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> match_stack reg m \<Longrightarrow> match_stack reg' m'"
proof-
  assume a0:"Next spc' reg' m' = exec_instr xins sz spc reg m" and
  a1:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) " and
  a2:"match_stack reg m"
  have b0:"bpf_to_x64_reg dst \<noteq> RSP" using bpf_to_x64_reg_def by (cases dst,simp_all)
  have b1:"reg SP = reg' SP" using exec_instr_def a0 a1 exec_instr_def b0 by simp
  have b2:"m = m'" using a0 a1 exec_instr_def by force
  have "match_stack reg' m'" using b1 b2 a2 match_stack_def by auto
  thus ?thesis by blast
qed

lemma mem_is_not_changed_by_add:"Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow> xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> m = m'"
  using exec_instr_def by simp

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
    by (metis bpf_instruction.simps(375) sbpf_state.simps(6))
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

lemma addq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and
       a1:"per_jit_add_reg64_1 dst src = Some (n, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (length l_bin, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = exec_instr xins sz spc reg xm" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg xm) " and
       a7:"prog!(unat pc) = bins"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' xm') "
proof -
  have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a3 
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def by simp
    moreover have b2:"(rs src) = reg (bpf_to_x64_reg src)" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (bpf_to_x64_reg dst)" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg ((bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg' xm'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed mem_is_not_changed_by_add match_state_def a6
      by (metis (no_types, lifting) a4 a5 b0 outcome.simps(4) sbpf_state.simps(9))
    thus ?thesis using b3 b7 match_state_def b8 b9 by fastforce
  qed
      

lemma exit_subgoal_rr_generic:
  assumes a0:"bins = BPF_EXIT" and
       a1:"per_jit_exit = Some (n, off, l_bin)" and
       a3:"x64_decode 0 l_bin = Some (n, xins)" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = st'" and
       a5:"xst' = exec_instr xins sz spc reg m" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg m) " and
       a7:"prog!(unat pc) = bins" and
       a8:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0"
     shows "match_state st' xst'"
proof-
  have b0:"st' = SBPF_Success (rs BR0)" using a0 a4 a7 a8 by simp
  have b1:"xins = Pret" using x64_encode_decode_consistency per_jit_exit_def a0 a1 a3
    by (smt (verit, ccfv_SIG) map_option_eq_Some option.inject prod.inject)
  moreover have b2:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def by simp
  moreover have b3:"(rs BR0) = reg (bpf_to_x64_reg BR0)" using a6 spec b2 by simp
  (*have b4:"Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) \<noteq> None" using match_state_def a6 match_stack_def by auto
  hence "\<exists> x. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = x \<and> x\<noteq> None" by simp
  hence "\<exists> v. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some v" by simp*)
  hence b5_1:"\<exists> v. Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some (Vlong v)" using match_state_def a6 match_stack_def by auto
  obtain v where b5_2:"Mem.loadv M64 m ((reg SP) + (u64_of_memory_chunk M64)) = Some (Vlong v)" using b5_1 by blast
  let "?reg'" = "(reg#SP <- ((reg SP) + (u64_of_memory_chunk M64)))"
  have b5_3:"xst' = Next v ?reg' m" using exec_instr_def exec_ret_def a5 b1 b5_2 by simp
  hence b5:"?reg' (bpf_to_x64_reg BR0) = reg (bpf_to_x64_reg BR0)" by (simp add: bpf_to_x64_reg_def)
  thus ?thesis using exec_instr_def b3 b1 b0 a5 using b5_2 exec_ret_def match_state_def by force
qed


lemma mulq_subgoal_rr_generic:
  assumes a0:"bins = BPF_ALU64 BPF_ADD dst (SOReg src)" and
       a1:"per_jit_mul_reg64 dst src = Some (n, off, l_bin)" and
       a3:"x64_decodes 0 l_bin = Some xins" and
       a4:"sbpf_step prog (SBPF_OK pc rs m) = (SBPF_OK pc' rs' m')" and
       a5:"Next spc' reg' xm' = interp3 (map snd xins) (Next spc reg xm)" and
       a6:"match_state (SBPF_OK pc rs m) (Next spc reg xm) " and
       a7:"prog!(unat pc) = bins" and 
       a8:"(bpf_to_x64_reg dst) = RAX"
  shows "match_state (SBPF_OK pc' rs' m') (Next spc' reg' xm') "
proof -
  let "?xins" = "map snd xins"
  have b0:"?xins = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]"
    using x64_encodes_decodes_consistency per_jit_mul_reg64_def a1 a3 a8 
    by(cases "bpf_to_x64_reg dst",simp_all)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def by simp
    moreover have b2:"(rs src) = reg (bpf_to_x64_reg src)" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (bpf_to_x64_reg dst)" using mulq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 a8 sorry
    have b4:"\<forall> r \<noteq> dst. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg ((bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg' xm'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed mem_is_not_changed_by_add match_state_def a6
      by (metis (no_types, lifting) a4 a5 b0 outcome.simps(4) sbpf_state.simps(9))
    thus ?thesis using b3 b7 match_state_def b8 b9 by fastforce
  qed

lemma aux1:"length prog \<noteq> 0 \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow>
  s = (SBPF_OK pc rs m) \<Longrightarrow> 
  s' = (SBPF_OK pc' rs' m') \<Longrightarrow> 
  \<exists> dst src. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src)"
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
  \<exists> dst src. prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src),BPF_EXIT, BPF_ALU64 BPF_MUL dst (SOReg src)}"
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


(*lemma aux3:"jit prog = x64_prog \<Longrightarrow> x64_prog \<noteq> None \<Longrightarrow> length (the x64_prog) = length prog"
  by (metis length_map option.sel)

lemma aux4:"jit prog = x64_prog \<Longrightarrow> x64_prog \<noteq> None \<Longrightarrow> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow> prog \<noteq> [] \<Longrightarrow>
  prog!(unat pc) = bins \<Longrightarrow> (the x64_prog)!(unat pc) = l_bin 
  \<Longrightarrow> Some l_bin = per_jit_ins bins"
  using jit_def aux3 by (metis (no_types, lifting) list.map_comp map_equality_iff nth_map nth_mem option.collapse option.sel)
*)

                                  
lemma demo1: assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m)" and
  a2:"s' = (SBPF_OK pc' rs' m')" and
  a3:"xst = (Next xpc xrs xm)" and
  a4:"match_state s xst" and
  a5:"jitper prog = Some x64_prog" and
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a7:"xpc = 0" 
shows "\<exists> xst'. let l = (x64_prog!(unat pc)) in x64_sem (fst l) (snd (snd l)) xst = xst' \<and> 
  match_state s' xst'"
(* \<and> snd xst' = unat (pc+1)*)
proof-
  let "?bpf_ins" = "prog!(unat pc)"
  have b0:"length prog \<noteq> 0" using a6 by blast
  have b1:"\<exists> src dst. ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using a0 a1 a2 a6 b0 aux1 by blast
  obtain src dst where b2:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using b1 by blast
  show ?thesis
  proof (cases "?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src)")
    case True
    let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
    have c0:"?l_bin = snd (snd (the (per_jit_add_reg64_1 dst src)))" using b2 True by fastforce
    have c1:"Some ?l_bin = x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" using per_jit_add_reg64_1_def c0 by fastforce
    have c2:"snd (snd (x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
    let "?st" = "x64_sem (fst (x64_prog!(unat pc))) ?l_bin xst"
    have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
    then have "x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src)" using b2 True by simp
    then have "(fst (x64_prog!(unat pc))) = 1" using per_jit_add_reg64_1_def by simp
    hence c3:"\<exists> size2 xins2. x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) \<and> ?st = exec_instr xins2 size2 xpc xrs xm" using x64_encode_decode_consistency a3 a7 c1 by fastforce
    obtain size2 xins2 where c4:"x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) \<and> ?st = exec_instr xins2 size2 xpc xrs xm" using c3 by auto
    have c5:"xins2 = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using Pair_inject c4 c1 option.inject x64_encode_decode_consistency by metis
    have c6:"\<exists> xrs' xpc' xm'. ?st = Next xpc' xrs' xm'" using exec_instr_def spec c5 c4 by auto
    obtain xrs' xpc' xm' where c7:"?st = Next xpc' xrs' xm'" using c6 by auto
    have "match_state s' ?st" using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 c1 per_jit_add_reg64_1_def b2 c4 True by fastforce
    then show ?thesis using True b2 c2 by force
  next
    case False
    let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
    have c0:"?l_bin = snd (snd (the (per_jit_mul_reg64 dst src)))" using b2 False by fastforce
    have c1:"Some ?l_bin = (let ins_list = case (bpf_to_x64_reg dst) of
    RAX \<Rightarrow> [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX]|
    RDX \<Rightarrow> [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RAX, Pmovq_rr RAX RDX, Pmulq_r R11, Pmovq_rr RDX RAX, Ppopl RAX]|
    _   \<Rightarrow> [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RAX, Pmovq_rr RAX (bpf_to_x64_reg dst), Ppushl_r RDX, Pmulq_r R11, 
            Ppopl RDX, Pmovq_rr (bpf_to_x64_reg dst) RAX, Ppopl RAX]
  in (x64_encodes_suffix ins_list))" using per_jit_mul_reg64_def c0 sorry
    have c2:"snd (snd (x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
    let "?st" = "x64_sem (fst (x64_prog!(unat pc))) ?l_bin xst"
    have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
    then have "x64_prog!(unat pc) = the (per_jit_mul_reg64 dst src)" using b2 False by simp
    then show ?thesis sorry
  qed
qed
  (*let "?l_bin"= "snd (snd (the (per_jit_ins ?bpf_ins)))"
  have c0:"?l_bin = snd (snd (the (per_jit_add_reg64_1 dst src)))" using b2 by fastforce
  have c1:"Some ?l_bin = x64_encode (Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))" using per_jit_add_reg64_1_def c0 by fastforce
  have c2:"snd (snd (x64_prog!(unat pc))) = ?l_bin" using a6 c0 a5 aux5 by metis
  let "?st" = "x64_sem (fst (x64_prog!(unat pc))) ?l_bin xst"
  have "x64_prog!(unat pc) = the (per_jit_ins ?bpf_ins)" using aux5 a5 a6 by blast
  then have "x64_prog!(unat pc) = the (per_jit_add_reg64_1 dst src)" using b2 by simp
  then have "(fst (x64_prog!(unat pc))) = 1" using per_jit_add_reg64_1_def by simp
  hence c3:"\<exists> size2 xins2. x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) \<and> ?st = exec_instr xins2 size2 xpc xrs xm" using x64_encode_decode_consistency a3 a7 c1 by fastforce
  obtain size2 xins2 where c4:"x64_decode 0 ?l_bin = Some (length ?l_bin, xins2) \<and> ?st = exec_instr xins2 size2 xpc xrs xm" using c3 by auto
  have c5:"xins2 = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" using Pair_inject c4 c1 option.inject x64_encode_decode_consistency by metis
  have c6:"\<exists> xrs' xpc' xm'. ?st = Next xpc' xrs' xm'" using exec_instr_def spec c5 c4 by auto
  obtain xrs' xpc' xm' where c7:"?st = Next xpc' xrs' xm'" using c6 by auto
  have "match_state s' ?st" using addq_subgoal_rr_generic a0 a1 a2 c7 a4 a3 c1 per_jit_add_reg64_1_def b2 c4 by fastforce
  thus ?thesis using c2 by simp
  qed*)

lemma match_s_not_stuck:"match_state s xst \<Longrightarrow> xst \<noteq> Stuck"
  apply(cases s, simp_all)
  apply(unfold match_state_def)
  subgoal for x11 x12 x13 by auto
  subgoal for x2 by auto
  by simp

(*
lemma x64_sem1_induct:"x64_sem1 (Suc n) pc x64_prog (Next xpc xrs m) = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs1 m1) = Next xpc1 xrs1 m1 \<Longrightarrow> 
  x64_sem1 n (pc+off) x64_prog (Next xpc1 xrs1 m1) = xst'"
  apply(cases "x64_prog!(unat pc)",simp_all)
  subgoal for a apply(cases "(Next 0 xrs1 m1)",simp_all)
    subgoal for x11
*)

lemma x64_sem1_induct_aux1:"x64_sem1 (Suc n) pc x64_prog (Next xpc xrs m) = xst' \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs m) = xst1 \<Longrightarrow> 
  x64_sem1 n (pc+off) x64_prog xst1 = xst'"
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
  x64_sem1 n (pc+off) x64_prog (Next 0 xrs1 m1) = xst'"
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

lemma corr_pc_aux1:"jitper prog = Some x64_prog \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  off=1"
proof (induction prog arbitrary: x64_prog pc num off l)
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
      have b0_1:"unat pc = 0" using True a0 by simp
      have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
      have b1_1:"(num,off,l) = x" using b0_1 b1 True Cons
        by (smt (verit) jitper.simps(2) nth_Cons_0 old.prod.case option.case_eq_if option.discI option.sel prod_cases3)
      have bn:"off = 1" 
        using b1 apply(cases "per_jit_ins a", simp_all) 
        subgoal for aa 
         apply(cases a,simp_all)
        subgoal for x91 x92 x93
          apply(cases x91,simp_all)
          apply(cases x93,simp_all)
          subgoal for x1 using b1 b1_1 per_jit_add_reg64_1_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x2 using b1 b1_1 per_jit_mul_reg64_def Let_def by (smt (verit) map_option_eq_Some prod.inject)
          done
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


lemma corr_pc_aux2:
  "jitper prog = Some x64_prog \<Longrightarrow> prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  s =  SBPF_OK pc rs m \<Longrightarrow>
  s' = sbpf_step prog s \<Longrightarrow> s' = SBPF_OK pc' rs' m' \<Longrightarrow> 
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  pc' = pc+off"
proof-
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
      using assm4 assm3 apply (smt (verit) binop.simps(133) bpf_instruction.simps(369) option.case_eq_if sbpf_state.inject(1) sbpf_state.simps(6) sbpf_step.elims)
      using assm4 assm3 option.case_eq_if sbpf_step.elims sorry
    done
  have "off=1" 
    using assm2 assm3 assm5 corr_pc_aux1 by blast
  thus ?thesis using c1 by simp
qed
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

lemma demo2_aux:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m');
   xst = (Next xpc xrs xm);
   match_state s xst;
   jitper prog = Some x64_prog;
   prog \<noteq> [];
   xpc = 0;
   x64_sem1 n pc x64_prog xst = xst' \<rbrakk> \<Longrightarrow>
   match_state s' xst'"
(* \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"*)
proof (induction n arbitrary: prog s s' pc rs m pc' rs' m' xst' xst xpc xrs xm x64_prog xst')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume 
       assm1: "sbpf_sem (Suc n) prog s = s'" and
       assm2:"s = SBPF_OK pc rs m" and
       assm3:"s' = SBPF_OK pc' rs' m'" and
       assm4:"xst = Next xpc xrs xm" and
       assm5:"match_state s xst" and
       assm6:"jitper prog = Some x64_prog" and
       assm7:"prog \<noteq> [] " and
       assm8:"xpc = 0" and
       assm9:"x64_sem1 (Suc n) pc x64_prog xst = xst'"
  then obtain s1 where s1_eq: "s1 = sbpf_step prog s" by simp
  have n_step_def:"sbpf_sem n prog s1 = s'" using s1_eq assm1 sbpf_sem_induct
    by (metis sbpf_sem.simps(2))
  have a0:"unat pc < length prog \<and> unat pc \<ge> 0" using assm1 assm3 
    using Suc.prems(2) assm7 pc_scope_aux by blast
  moreover have a1:"\<exists> pc1 rs1 m1. s1 = (SBPF_OK pc1 rs1 m1)"
    by (metis Suc.prems(3) bot_nat_0.not_eq_extremum intermediate_step_is_ok n_step_def sbpf_sem.simps(1) sbpf_state.simps(6))
  obtain pc1 rs1 m1 where a2:"s1 = (SBPF_OK pc1 rs1 m1)" using a1 by auto
  have a3:"m1 = m" using mem_is_not_changed s1_eq assm2 a2 by blast
  let "?num" = "(fst(x64_prog!(unat pc)))"
  have "\<exists> xst1. x64_sem (fst(x64_prog!(unat pc))) (snd (snd ((x64_prog!(unat pc)))))(Next xpc xrs xm) = xst1 \<and> match_state s1 xst1"
    using s1_eq assm2 a2 assm4 assm5 assm6 assm7 assm8 assm8 demo1 by (metis (mono_tags, lifting) calculation)
  then obtain xst1 where a4:"x64_sem ?num (snd (snd ((x64_prog!(unat pc)))))(Next 0 xrs xm) = xst1 \<and> match_state s1 xst1" using assm8 by auto
  hence a4_1:"x64_sem ?num (snd (snd ((x64_prog!(unat pc)))))(Next 0 xrs xm) = xst1" by auto
  have an:"\<exists> xpc1 xrs1 xm1. xst1 = Next xpc1 xrs1 xm1" using a4 by (metis match_s_not_stuck outcome.exhaust)
  then obtain xpc1 xrs1 xm1 where a10:"xst1 = Next xpc1 xrs1 xm1" by auto
  let "?xst1" = "Next 0 xrs1 xm1"
  have a5:"match_state s1 ?xst1" using an match_state_def
    using a10 a2 a4 by fastforce
  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where a6:"x64_prog!(unat pc) = (num,off,l)" by auto
  have a7:"l = (snd (snd ((x64_prog!(unat pc)))))" using a6 by simp
  let "?pc" = "pc+off"
  have a9:"x64_sem1 n ?pc x64_prog ?xst1 = xst'" using x64_sem1_induct_aux3 assm4 assm9 a7 a6 a4_1 a10 by (metis fst_conv)
  have a13:"?pc = pc1" using corr_pc_aux2 assm6 a0 s1_eq a6 a2 assm7 assm2 by auto
  from Suc.IH have " sbpf_sem n prog s = s' \<Longrightarrow>
           s = SBPF_OK pc rs m \<Longrightarrow>
           s' = SBPF_OK pc' rs' m' \<Longrightarrow>
           xst = Next xpc xrs xm \<Longrightarrow>
           match_state s xst \<Longrightarrow>
           jitper prog = Some x64_prog \<Longrightarrow>
           prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc \<Longrightarrow> 
           xpc = 0 \<Longrightarrow> 
           x64_sem1 n pc x64_prog xst = xst' \<Longrightarrow> 
           match_state s' xst'" by blast
  have "x64_sem1 n pc1 x64_prog (Next 0 xrs1 xm1) = xst' \<and> match_state s' xst'" using n_step_def a2 assm3 a10 a5 assm6 assm7 assm8 a9 Suc a13 by blast
  hence an:"match_state s' xst'" by blast
  then show ?case using an by auto
qed
(*
lemma demo2_aux:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m');
   xst = (Next xpc xrs xm);
   match_state s xst;
   jitper prog = Some x64_prog;
   prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0;
   xpc = 0;
   x64_sem1 n pc x64_prog xst = xst' \<rbrakk> \<Longrightarrow>
   match_state s' xst'"
(* \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"*)
proof (induction n arbitrary: prog s s' pc rs m pc' rs' m' xst' xst xpc xrs xm x64_prog xst')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume assm1: "sbpf_sem (Suc n) prog s = s'" and
       assm2:"s = SBPF_OK pc rs m" and
       assm3:"s' = SBPF_OK pc' rs' m'" and
       assm4:"xst = Next xpc xrs xm" and
       assm5:"match_state s xst" and
       assm6:"jitper prog = Some x64_prog" and
       assm7:"prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc " and
       assm8:"xpc = 0" and
       assm9:"x64_sem1 (Suc n) pc x64_prog xst = xst'"
  then obtain s1 where s1_eq: "s' = sbpf_step prog s1" 
    by (metis add_Suc_right sbpf_sem.simps(1) sbpf_sem.simps(2) sbpf_sem_induct)
  from Suc have s'_def:"sbpf_sem (Suc n) prog s = s'" by blast
  have one_step_def:"\<exists> s1. sbpf_sem n prog s = s1 \<and> sbpf_step prog s1 = s'" using s1_eq s'_def sbpf_sem_induct
    by (metis add_Suc_right sbpf_sem.simps(1) sbpf_sem.simps(2))
  obtain s1 where get_s1:"sbpf_sem n prog s = s1 \<and> sbpf_step prog s1 = s'" using one_step_def by simp
  have a1:"s1 = sbpf_sem n prog s" using one_step_def s1_eq using get_s1 by force
  have a3:"\<exists> pc1 rs1 m1. s1 = (SBPF_OK pc1 rs1 m1)" 
    by (smt (verit) Suc.prems(3) get_s1 sbpf_state.simps(6) sbpf_step.elims)
  obtain pc1 rs1 m1 where a6:"s1 = (SBPF_OK pc1 rs1 m1)" using a3 by auto
  moreover have "m1 = m'" using mem_is_not_changed Suc.prems(3) calculation get_s1 by blast
  hence a4:"s1 = (SBPF_OK pc1 rs1 m')" using calculation by blast
  have "\<exists> xst1. x64_sem1 n pc x64_prog xst = xst1" by blast
  (*have "\<exists> xst1. x64_sem1 n pc x64_prog xst = xst1 \<and> x64_sem 1 (snd (snd ((x64_prog!(unat pc1))))) xst1 = xst'" sorry*)
  then obtain xst1 where a2:"x64_sem1 n pc x64_prog xst = xst1" using a4 by auto
  from Suc.IH have "sbpf_sem n prog s = s' \<Longrightarrow>
           s = SBPF_OK pc rs m \<Longrightarrow>
           s' = SBPF_OK pc' rs' m' \<Longrightarrow>
           xst = Next xpc xrs m \<Longrightarrow>
           match_state s xst \<Longrightarrow>
           jitper prog = Some x64_prog \<Longrightarrow>
           prog \<noteq> [] \<and> unat pc < length prog \<and> 0 \<le> unat pc \<Longrightarrow> xpc = 0 \<Longrightarrow> x64_sem1 n pc x64_prog xst = xst' \<Longrightarrow> 
           match_state s' xst'" by blast
  from Suc have a5:"match_state s1 xst1" using a1 assm2 a4 assm4 assm5 assm6 assm7 assm8 a2 by blast
  have b0:"\<exists> xpc1 xrs1 m2. xst1 = (Next xpc1 xrs1 m2)" using match_s_not_stuck a5 by (meson outcome.exhaust)
  obtain xpc1 xrs1 m2 where b0:"xst1 = (Next xpc1 xrs1 m2)" using b0 by auto
  (*moreover have "m2 = m" using a4 a5 calculation(2) match_state_def mem_is_not_changed2 sorry*)
  have b4:"unat pc1 < length prog \<and> unat pc1 \<ge> 0" 
    by (metis (no_types, lifting) a4 assm3 get_s1 linorder_not_less sbpf_state.simps(6) sbpf_step.simps(1))
  have b6:"\<exists> xst2. x64_sem 1 (snd (snd ((x64_prog!(unat pc1)))))(Next 0 xrs1 m2) = xst2 \<and> match_state s' xst2" 
    using s1_eq a4 assm3 b0 a5 assm6 assm7 b0 demo1 b4 Suc.prems(6) get_s1 
    by (smt (verit, ccfv_SIG) match_state_def outcome.simps(4) sbpf_state.case(1))
  obtain xst2 where "x64_sem 1 (snd (snd ((x64_prog!(unat pc1))))) (Next 0 xrs1 m2) = xst2 \<and> match_state s' xst2" using b6 by auto
  moreover have "xst2 = xst'" using x64_sem1_induct 
    using a2 assm9 calculation(2) b0 sorry
  then show ?case using calculation(2) by fastforce
qed
*)
lemma demo2:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m);
   s' = (SBPF_OK pc' rs' m);
   xst = (Next xpc xrs m);
   match_state s xst;
   jitper prog = Some x64_prog;
   prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0;
   xpc = 0 \<rbrakk> \<Longrightarrow>
   \<exists> xst'. x64_sem1 n pc x64_prog xst = xst' \<and> match_state s' xst'"
  using demo2_aux by blast

end