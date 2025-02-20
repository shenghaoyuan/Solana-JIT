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
  x64Syntax x64Semantics x64Assembler
  JITState JITPer2Aux

begin


subsection \<open> JIT rule \<close>

text \<open> return 
  - the number of jited x64 assembly code
  - the offset pointing to next pc
  - the jited x64 binary code \<close>
definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 1, x64_encode ins) 
)"

definition per_jit_exit :: "(nat \<times> u64 \<times> x64_bin) option" where
"per_jit_exit = (
  let ins = Pret in
    Some (1, 1, x64_encode ins) 
)"


(*definition per_jit_mul_reg64::"bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_mul_reg64 dst src \<equiv> let ins_list = [Pmovq_rr (bpf_to_x64_reg src) R11, Ppushl_r RDX, Pmulq_r R11, Ppopl RDX] in
   map_option (\<lambda> l. (5, 1, l)) (x64_encodes_func_suffix ins_list)"*)

definition per_jit_mul_reg64::"bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
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
(*(Mem.loadv mc bm (Vlong addr) = Some v) \<longrightarrow> (Mem.loadv mc xm (Vlong addr) = Some v))*)
definition match_mem :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
"match_mem bm xm = (
  \<forall> mc addr v. (Mem.loadv mc bm addr = Some v) \<longrightarrow> (Mem.loadv mc xm addr = Some v))"

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


lemma reg_r11_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.R11"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma mulq_subgoal_rr_aux1_1:
  "xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
    exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) pc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6  \<Longrightarrow>
   \<forall> r. bpf_to_x64_reg r \<notin> {RDX, RAX} \<longrightarrow> rs (bpf_to_x64_reg r) = rs6 (bpf_to_x64_reg r) "
  apply(unfold exec_instr_def)
  apply(cases "Pmulq_r (bpf_to_x64_reg src)",simp_all)
  subgoal for x6
    apply(unfold exec_push_def exec_pop_def exec_ret_def  Let_def) 
    using store_load_consistency
    apply(cases "storev M64 m1 (rs1 SP - u64_of_memory_chunk M64) (Vlong (rs1 RAX))",simp_all)
    apply(cases "loadv M64 m5 (rs5 SP)", simp_all)
    subgoal for a apply(cases a,simp_all)
      subgoal for x5 
        apply(cases M64,simp_all)
        using store_load_consistency reg_r11_consist reg_rsp_consist by auto
      done
    done
  done

lemma mulq_subgoal_rr_aux1_2:
     "(bpf_to_x64_reg dst) = RDX \<Longrightarrow>
     bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow>
     prog!(unat pc) = bins \<Longrightarrow>
     sbpf_step prog (SBPF_OK pc reg m) = (SBPF_OK pc' reg' m')  \<Longrightarrow>
     xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
    exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6 \<Longrightarrow>
     rs (bpf_to_x64_reg dst) = reg dst \<Longrightarrow>
     rs (bpf_to_x64_reg src) = reg src \<Longrightarrow>
     rs6 (bpf_to_x64_reg dst) = (reg' dst)"
    apply (unfold exec_instr_def step) 
    apply(cases "snd (xins ! 0)",simp_all)
    subgoal for x51
      apply(unfold exec_push_def exec_pop_def exec_ret_def  Let_def eval_alu_def  eval_reg_def) 
      apply(split if_splits,simp_all)
      apply(cases " prog ! unat pc ",simp_all)
      subgoal for x91 apply(split if_splits,simp_all)
        using store_load_consistency
        apply(cases "storev M64 m1 (rs1 SP - u64_of_memory_chunk M64) (Vlong (rs1 RAX))",simp_all)
        apply(cases "loadv M64 m5 (rs5 SP)", simp_all)
    subgoal for a apply(cases a,simp_all)
      subgoal for x5 
        apply(cases M64,simp_all)
       by auto
      done
    done
  done
  done

lemma mulq_subgoal_rr_aux1_3:
  assumes a0:"xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)]" and
  a1:"exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) xpc xrs m   = Next xpc1 xrs1 m1" and
  a2:"exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) xpc1 xrs1 m1 = Next xpc2 xrs2 m2" and
  a3:"exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) xpc2 xrs2 m2 = Next xpc3 xrs3 m3" and
  a4:"exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) xpc3 xrs3 m3 = Next xpc4 xrs4 m4" and
  a5:"exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) xpc4 xrs4 m4 = Next xpc5 xrs5 m5" and
  a6:"exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) xpc5 xrs5 m5 = Next xpc6 xrs6 m6" 
  shows "xrs6 RAX = xrs RAX \<and> xrs6 RSP = xrs RSP"
proof-
  have b1:"m1 = m" using  a0 exec_instr_def a1 by simp
  have c1:"xrs SP = xrs1 SP" using a0 exec_instr_def a1 by auto
  have d1:"xrs RAX = xrs1 RAX" using a0 exec_instr_def a1 by auto

  have b2_1:"Next xpc2 xrs2 m2 = exec_push xpc1 1 M64 m1 xrs1 (xrs1 RAX)" using exec_instr_def exec_push_def a0 a2 by auto
  let "?addr" = "(xrs1 SP)- (u64_of_memory_chunk M64)"
  have b2_2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) \<noteq> None" 
    using a0 a1 exec_push_def apply(cases "storev M64 m ?addr (Vlong (xrs1 RAX))",simp_all)
    apply (metis (no_types, lifting) memory_chunk.simps(16) storev_def val.simps(29))    
    subgoal for a using b1 by blast
    done
  have b2:"storev M64 m1 ?addr (Vlong (xrs1 RAX)) = Some m2" 
    using b2_2 b2_1 exec_push_def
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all)
  have c2:"xrs2 RSP = ?addr" using b2_1 exec_push_def b2_2 b2_1
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all) 
  have d2:"xrs2 RAX = xrs1 RAX" using a0 exec_instr_def a2 b2_1 exec_push_def 
    by(cases "storev M64 m1 ?addr (Vlong (xrs1 RAX))",simp_all) 
  
  have b3:"m2=m3" using a0 exec_instr_def a3 by simp
  have c3:"xrs2 RSP = xrs3 RSP" using  a0 exec_instr_def a3 by auto

  have b4:"m3=m4" using  a0 exec_instr_def a4 by simp
  have c4:"xrs3 RSP = xrs4 RSP" using a0 exec_instr_def a4 by auto

  have b5:"m4=m5" using a0 exec_instr_def a5 by simp
  have c5:"xrs4 RSP = xrs5 RSP" using a0 exec_instr_def a5 by auto

  have b5_1:"Next xpc6 xrs6 m6 = exec_pop xpc5 1 M64 m5 xrs5 RAX" using a6 a0 exec_instr_def by simp
  have b5_2:"Mem.loadv M64 m5 ?addr \<noteq> None" using store_load_consistency b2 b3 b4 b5 by blast
  have b5_3:"Mem.loadv M64 m5 ?addr = Some (Vlong (xrs1 RAX))" using b2 b3 b4 b5 store_load_consistency by auto
  have b5:"m6 = m5 \<and> xrs6 RSP = xrs RSP" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 RAX)",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 c1 by force
    done
  have d5:"xrs6 RAX = xrs RAX" using exec_pop_def b5_2
    apply(cases "Mem.loadv M64 m5 ?addr",simp_all) 
     apply(cases "Vlong (xrs1 RAX)",simp_all)
    subgoal for a x5 
      using b5_1 b5_3 c2 c3 c4 c5 d1 d2 by force
    done
  thus ?thesis using d5 b5 by simp
qed

lemma mulq_subgoal_rr_aux1_4:
  "xins = [(3,Pmovq_rr R11 (bpf_to_x64_reg src)), (1,Ppushl_r RAX), (3,Pmovq_rr RAX RDX), (3,Pmulq_r R11), (3,Pmovq_rr RDX RAX), (1,Ppopl RAX)] \<Longrightarrow>
    exec_instr (snd(xins!0)) (of_nat(fst(xins!0))) pc rs xm = Next pc1 rs1 m1\<and>
    exec_instr (snd(xins!1)) (of_nat(fst(xins!1))) pc1 rs1 m1 = Next pc2 rs2 m2 \<and>
    exec_instr (snd(xins!2)) (of_nat(fst(xins!2))) pc2 rs2 m2 = Next pc3 rs3 m3 \<and>
    exec_instr (snd(xins!3)) (of_nat(fst(xins!3))) pc3 rs3 m3 = Next pc4 rs4 m4 \<and>
    exec_instr (snd(xins!4)) (of_nat(fst(xins!4))) pc4 rs4 m4 = Next pc5 rs5 m5 \<and> 
    exec_instr (snd(xins!5)) (of_nat(fst(xins!5))) pc5 rs5 m5 = Next pc6 rs6 m6 \<Longrightarrow>
  \<forall> r. bpf_to_x64_reg r \<notin> {RDX} \<longrightarrow> rs (bpf_to_x64_reg r) = rs6 (bpf_to_x64_reg r) "
  using mulq_subgoal_rr_aux1_3 mulq_subgoal_rr_aux1_1 reg_r11_consist reg_rsp_consist 
  by (smt (z3) insert_iff)


lemma mulq_subgoal_rr_aux2_1:
  "xins = Pmulq_r (bpf_to_x64_reg src) \<Longrightarrow> 
  Next pc' reg' m' = exec_instr xins sz pc reg m \<Longrightarrow>
  \<forall> r. r \<notin> {RAX, RDX} \<longrightarrow> reg' r = reg r"
  by (simp add: exec_instr_def)


lemma mulq_subgoal_rr_aux3:"bins = BPF_ALU64 BPF_MUL dst (SOReg src) \<Longrightarrow> 
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

lemma mem_is_not_changed_by_mov:"Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow> xins = Pmovq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) 
   \<Longrightarrow> m = m'"
  using exec_instr_def by simp

lemma mem_is_not_changed_by_mul:"Next spc' reg' m' = exec_instr xins sz spc reg m \<Longrightarrow> xins = Pmulq_r (bpf_to_x64_reg src) 
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
    have b0:"xins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src)" 
      using x64_encode_decode_consistency per_jit_add_reg64_1_def a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) Pair_inject map_option_eq_Some option.inject)
    moreover have b1:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def match_reg_def by simp
    moreover have b2:"(rs src) = reg (bpf_to_x64_reg src)" using a6 spec b1 by simp
    hence b3:"(rs' dst) = reg' (bpf_to_x64_reg dst)" using aluq_subgoal_rr_aux1 b0 b1 b2 a0 a4 a5 a7 by metis
    have b4:"\<forall> r \<noteq> dst. reg'(bpf_to_x64_reg r) = reg (bpf_to_x64_reg r)" using b0 a5 aluq_subgoal_rr_aux2 by blast
    have b5:"\<forall> r \<noteq> dst. (rs' r) = (rs r)" using aluq_subgoal_rr_aux3 a0 a4 a7 by force
    have b6:"\<forall> r \<noteq> dst. (rs r) = reg ((bpf_to_x64_reg r))" using a6 using b1 by blast
    have b7:"(\<forall> r \<noteq> dst. (rs' r) = reg' ((bpf_to_x64_reg r)))" using b1 b4 b5 by presburger
    have b8:"match_stack reg' xm'" using stack_is_not_changed_by_add a6 match_state_def a5 b0 by simp
    have b9:"match_mem m' xm'" using mem_is_not_changed mem_is_not_changed_by_add match_state_def a6
      by (metis (no_types, lifting) a4 a5 b0 outcome.simps(4) sbpf_state.simps(9))
    thus ?thesis using b3 b7 match_state_def b8 b9 match_reg_def by fastforce
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
  have b1:"xins = Pret" using x64_encode_decode_consistency per_jit_exit_def a0 a1 a3 list_in_list_prop
    by (smt (verit, ccfv_SIG) map_option_eq_Some option.inject prod.inject)
  moreover have b2:"(\<forall> r. (rs r) = reg (bpf_to_x64_reg r))" using a6 spec match_state_def match_reg_def by simp
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


(*
    Some l_bin = x64_encodes2 ins \<Longrightarrow>
    x64_decodes_aux (length ins) 0 l_bin = Some ins_list \<Longrightarrow>
    map snd ins_list = ins"
*)


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


                                  

end