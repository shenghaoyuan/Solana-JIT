section \<open> A collection of common type of JIT \<close>

theory JIT
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics
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

definition update_pc_section_aux ::"usize list \<Rightarrow> nat \<Rightarrow> usize \<Rightarrow> usize list" where
"update_pc_section_aux pc_sec pc x = list_update pc_sec pc x"

abbreviation "REG_SCRATCH::ireg \<equiv> x64Syntax.R11"  

definition bpf_to_x64_reg:: "bpf_ireg \<Rightarrow> ireg" where
  "bpf_to_x64_reg br = (
  case br of
  BR0 \<Rightarrow> x64Syntax.RAX |
  BR1 \<Rightarrow> x64Syntax.RDI |
  BR2 \<Rightarrow> x64Syntax.RSI |
  BR3 \<Rightarrow> x64Syntax.RDX |
  BR4 \<Rightarrow> x64Syntax.RCX |
  BR5 \<Rightarrow> x64Syntax.R8 |
  BR6 \<Rightarrow> x64Syntax.RBX |
  BR7 \<Rightarrow> x64Syntax.R13 |
  BR8 \<Rightarrow> x64Syntax.R14 |
  BR9 \<Rightarrow> x64Syntax.R15 |
  BR10 \<Rightarrow> x64Syntax.RBP
)"

lemma bpf_to_x64_reg_corr2[simp]:" bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2  \<longrightarrow> r1 \<noteq> r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(rule impI)
  apply(cases r1)
    apply(cases r2, simp_all)
           apply(cases r2, simp_all)
    apply(cases r2, simp_all)
         apply(cases r2, simp_all)
    apply(cases r2, simp_all)
       apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  done

lemma bpf_to_x64_reg_corr[simp]:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(rule impI)
  apply(cases r1)
    apply(cases r2, simp_all)
           apply(cases r2, simp_all)
    apply(cases r2, simp_all)
         apply(cases r2, simp_all)
    apply(cases r2, simp_all)
       apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  apply(cases r2, simp_all)
    apply(cases r2, simp_all)
  done


definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> x64_bin option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    x64_encode ins
)"

definition per_jit_exit :: "x64_bin option " where
"per_jit_exit = (
  let ins = Pret in
    x64_encode ins
)"

fun per_jit_ins ::" bpf_instruction \<Rightarrow> x64_bin option"where
"per_jit_ins bins = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  _ \<Rightarrow> None
)"

fun jit1 :: "ebpf_asm \<Rightarrow> u8 list \<Rightarrow> usize list \<Rightarrow> (u8 list * usize list) option" where
"jit1 [] l_bin l_pc = Some (l_bin, l_pc)" |
"jit1 (h#t) l_bin l_pc = (
  case per_jit_ins h of
  None \<Rightarrow> None |
  Some ins \<Rightarrow> (
    jit1 t (l_bin @ ins) (l_pc @ [of_nat (length l_bin)])
  )
)"

fun jit :: "ebpf_asm \<Rightarrow> (u8 list * usize list) option" where
"jit [] = Some ([], [])" |
"jit (h#t) = (
  case jit t of
  None \<Rightarrow> None |
  Some (l_bin, l_pc) \<Rightarrow> (
    case per_jit_ins h of
    None \<Rightarrow> None |
    Some ins \<Rightarrow> Some (ins @l_bin, 0#(map (\<lambda> i. i + (of_nat (length ins))) l_pc))
  )
)"



(**r simulation relation *)
definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> usize list \<Rightarrow> bool" where
"match_state bst xst pc_map = (
  case bst of
  SBPF_OK pc rs m \<Rightarrow> (
    case xst of
      Next xpc xrs xm \<Rightarrow>
        (\<forall> r. (rs r) = xrs (bpf_to_x64_reg r)) \<and> \<comment>\<open> for ALU + MEM + Call \<close>
        pc_map!(unat pc) = xpc \<and>  \<comment>\<open> for Jump \<close>
        m = xm  \<comment>\<open> for MEM + Call \<close> |
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
  apply (cases m; simp)
  subgoal for m
    apply (cases n; simp)
    done
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

theorem jit_correct:
 "jit prog = Some (x64_prog, pc_map) \<Longrightarrow>
  bst = SBPF_OK pc rs m \<Longrightarrow>
  bst' = SBPF_OK pc' rs' m' \<Longrightarrow>
  xst = Next xpc xrs xm \<Longrightarrow>
  match_state bst xst pc_map \<Longrightarrow>
  sbpf_step prog bst = bst' \<Longrightarrow>
  \<exists> fuel n xst'.
      x64_sem n x64_prog xst = xst' \<and> \<comment> \<open>
      x64_sem fuel x64_prog xst' = xst1 \<and> \<close>
      match_state bst' xst' pc_map"
  apply simp
  apply (cases "prog = []"; simp)

  sorry

end