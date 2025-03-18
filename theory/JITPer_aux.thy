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

abbreviation "REG_OTHER_SCRATCH::ireg \<equiv> R10"

definition bpf_to_x64_reg:: "bpf_ireg \<Rightarrow> ireg" where
  "bpf_to_x64_reg br = (
  case br of
  BR0 \<Rightarrow> RAX |
  BR1 \<Rightarrow> RSI |
  BR2 \<Rightarrow> RDX |
  BR3 \<Rightarrow> RCX |
  BR4 \<Rightarrow> R8 |
  BR5 \<Rightarrow> R9  |
  BR6 \<Rightarrow> R12 |
  BR7 \<Rightarrow> R13 |
  BR8 \<Rightarrow> R14 |
  BR9 \<Rightarrow> R15 |
  BR10 \<Rightarrow> RBP
)"
(*
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
)"*)

lemma bpf_to_x64_reg_corr2[simp]:" bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2  \<longrightarrow> r1 \<noteq> r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(cases r1; cases r2; simp)
  done

lemma bpf_to_x64_reg_corr[simp]:" r1 \<noteq> r2 \<longrightarrow> bpf_to_x64_reg r1 \<noteq> bpf_to_x64_reg r2 "
  apply(unfold bpf_to_x64_reg_def)
  apply(cases r1; cases r2; simp)
  done

lemma reg_r10_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.R10"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma reg_r11_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.R11"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)

lemma reg_rsp_consist:"r = (bpf_to_x64_reg dst) \<Longrightarrow> r \<noteq> x64Syntax.RSP"
  apply(cases dst) 
  by (unfold bpf_to_x64_reg_corr bpf_to_x64_reg_def, simp_all)


definition update_pc_section_aux ::"usize list \<Rightarrow> nat \<Rightarrow> usize \<Rightarrow> usize list" where
"update_pc_section_aux pc_sec pc x = list_update pc_sec pc x"

subsection \<open> JIT rule \<close>

text \<open> return 
  - the number of jited x64 assembly code
  - the offset pointing to next pc
  - the jited x64 binary code \<close>
definition per_jit_add_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_add_reg64_1 dst src = (
  let ins = Paddq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 0, x64_encode ins) 
)"


definition per_jit_sub_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_sub_reg64_1 dst src = (
  let ins = Psubq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 0, x64_encode ins) 
)"

definition per_jit_or_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_or_reg64_1 dst src = (
  let ins = Porq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 0, x64_encode ins) 
)"

definition per_jit_and_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_and_reg64_1 dst src = (
  let ins = Pandq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 0, x64_encode ins) 
)"

definition per_jit_xor_reg64_1 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_xor_reg64_1 dst src = (
  let ins = Pxorq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
    Some (1, 0, x64_encode ins) 
)"


definition per_jit_exit :: "(nat \<times> u64 \<times> x64_bin) option" where
"per_jit_exit = (
  let ins = Pret in
    Some (1, 0, x64_encode ins) 
)"


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
    in Some (len, 0, ins_list)"
                              
definition per_jit_jcc ::"condition \<Rightarrow> bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> u64 \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
  "per_jit_jcc cond dst src off \<equiv> 
    let tcond = (case cond of Eq \<Rightarrow> Some Cond_e |
                              Ne \<Rightarrow> Some Cond_ne | 
                              Lt \<Rightarrow> Some Cond_b | 
                              Le \<Rightarrow> Some Cond_be | 
                              Ge \<Rightarrow> Some Cond_ae | 
                              Gt \<Rightarrow> Some Cond_a | 
                              SLt \<Rightarrow> Some Cond_l | 
                              SLe \<Rightarrow> Some Cond_le | 
                              SGe \<Rightarrow> Some Cond_ge | 
                              SGt \<Rightarrow> Some Cond_g |  
                              _ \<Rightarrow> None ) in
  if tcond = None then None else
  let ins1 = Pcmpq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src) in
  let ins2 = (Pjcc (the tcond) 0) in Some (1,off+1,x64_encode ins1@x64_encode ins2 )"


definition per_jit_call_reg :: "bpf_ireg \<Rightarrow> imm_ty \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
  "per_jit_call_reg src imm = Some (1, ucast imm, x64_encode (Pcall_i 0))"

definition per_jit_shift_lsh_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_shift_lsh_reg64 dst src = (
  let cond1 = ((bpf_to_x64_reg dst) = RCX); 
    len = case (bpf_to_x64_reg dst) of 
        RCX \<Rightarrow> 5 |
          _ \<Rightarrow> 4; 
    l_bin = 
      case (bpf_to_x64_reg dst) of 
        RCX \<Rightarrow> x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src)) |               
      _ \<Rightarrow> x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshlq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX)   
    in Some (len, 0, l_bin)
)"

definition per_jit_shift_rsh_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_shift_rsh_reg64 dst src = (
  let cond1 = ((bpf_to_x64_reg dst) = RCX); 
    len = case (bpf_to_x64_reg dst) of 
        RCX \<Rightarrow> 5 |
          _ \<Rightarrow> 4; 
    l_bin = 
      case (bpf_to_x64_reg dst) of 
        RCX \<Rightarrow> x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src)) |               
      _ \<Rightarrow> x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Pshrq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX)   
    in Some (len, 0, l_bin)
)"

definition per_jit_shift_arsh_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_shift_arsh_reg64 dst src = (
  let cond1 = ((bpf_to_x64_reg dst) = RCX); 
    len = case (bpf_to_x64_reg dst) of 
        RCX \<Rightarrow> 5 |
          _ \<Rightarrow> 4; 
    l_bin = 
      case (bpf_to_x64_reg dst) of 
        RCX \<Rightarrow> x64_encode(Ppushl_r (bpf_to_x64_reg src))@ x64_encode(Pxchgq_rr (bpf_to_x64_reg dst) (bpf_to_x64_reg src))@
        x64_encode(Psarq_r (bpf_to_x64_reg src))@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src) )@ x64_encode(Ppopl (bpf_to_x64_reg src)) |               
      _ \<Rightarrow> x64_encode(Ppushl_r x64Syntax.RCX)@x64_encode(Pmovq_rr (x64Syntax.RCX) (bpf_to_x64_reg src))@
        x64_encode(Psarq_r (bpf_to_x64_reg dst))@x64_encode(Ppopl x64Syntax.RCX)   
    in Some (len, 0, l_bin)
)"

definition per_jit_load_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> memory_chunk \<Rightarrow> off_ty \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_load_reg64 dst src chk off = (
  let l_bin = 
    x64_encode (Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg src))@
    x64_encode (Pmov_mr (Addrmode (Some R11) None 0) (bpf_to_x64_reg dst) chk) in
    Some (3, 0, l_bin)
)"

definition per_jit_store_reg64 :: "bpf_ireg \<Rightarrow> bpf_ireg \<Rightarrow> memory_chunk \<Rightarrow> off_ty \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_store_reg64 dst src chk off = (
  let l_bin = 
    x64_encode (Pmovq_ri R11 (scast off))@x64_encode (Paddq_rr R11 (bpf_to_x64_reg dst))@
    x64_encode (Pmovq_rr R10 (bpf_to_x64_reg src))@x64_encode (Pmov_rm R10 (Addrmode (Some R11) None 0) chk) in
    Some (4, 0, l_bin)
)"



definition per_jit_ins ::" bpf_instruction \<Rightarrow> (nat \<times> u64 \<times> x64_bin) option" where
"per_jit_ins bins = (
  case bins of
  BPF_ALU64 BPF_ADD dst (SOReg src) \<Rightarrow> (per_jit_add_reg64_1 dst src) |
  BPF_ALU64 BPF_SUB dst (SOReg src) \<Rightarrow> (per_jit_sub_reg64_1 dst src) |
  BPF_ALU64 BPF_OR dst (SOReg src) \<Rightarrow> (per_jit_or_reg64_1 dst src) |
  BPF_ALU64 BPF_AND dst (SOReg src) \<Rightarrow> (per_jit_and_reg64_1 dst src) |
  BPF_ALU64 BPF_XOR dst (SOReg src) \<Rightarrow> (per_jit_xor_reg64_1 dst src) |
  BPF_EXIT \<Rightarrow> per_jit_exit |
  BPF_ALU64 BPF_MUL dst (SOReg src) \<Rightarrow> (per_jit_mul_reg64 dst src) |
  BPF_JUMP cond dst (SOReg src) off \<Rightarrow> per_jit_jcc cond dst src (scast off) |
  BPF_ALU64 BPF_LSH dst (SOReg src) \<Rightarrow> (per_jit_shift_lsh_reg64 dst src) |
  BPF_ALU64 BPF_RSH dst (SOReg src) \<Rightarrow> (per_jit_shift_rsh_reg64 dst src) |
  BPF_ALU64 BPF_ARSH dst (SOReg src) \<Rightarrow> (per_jit_shift_arsh_reg64 dst src)|
  BPF_LDX chk dst src off \<Rightarrow> (per_jit_load_reg64 dst src chk off) |
  BPF_ST chk dst (SOReg src) off \<Rightarrow> (per_jit_store_reg64 dst src chk off) |
  BPF_CALL_IMM src imm \<Rightarrow> (per_jit_call_reg src imm) |
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

(*
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
*)

subsection \<open> simulation relation \<close>
(* \<exists> v. Mem.loadv M64 m (Vptr sp_block ((xrs (IR SP)) - (u64_of_memory_chunk M64))) = Some (Vlong v))*)
definition match_stack :: "regset \<Rightarrow> bool" where
"match_stack xrs  = ((xrs (IR SP)) \<ge> MIN_SP_SIZE) "

text \<open> because jited x64 code may use pop and push to save registers,
then x64 memory has more info than sbpf memory \<close>

(*\<forall> mc addr v. (Mem.loadv mc bm (Vlong addr) = Some v) \<longrightarrow> (Mem.loadv mc xm (Vlong addr) = Some v))*)
definition match_mem :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
"match_mem bm xm = (
  \<forall> addr v. bm 0 addr = Some v \<longrightarrow> xm 0 addr = Some v)"
(*
definition match_mem_byte :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
"match_mem_byte bm xm = (
  \<forall> addr v. (Mem.loadv M8 bm (Vlong addr) = Some v) \<longrightarrow> (Mem.loadv M8 xm (Vlong addr) = Some v))"*)

definition match_reg :: "reg_map \<Rightarrow> regset \<Rightarrow> bool" where
  "match_reg rm rs = (\<forall> r. (rm r) = rs (IR (bpf_to_x64_reg r)))"

(*definition match_state :: "sbpf_state \<Rightarrow> x64_state \<Rightarrow> bool" where
"match_state bst xst = (
  case bst of
  SBPF_OK pc rs m \<Rightarrow> (
    case xst of
      Next xpc xrs xm \<Rightarrow>
        match_reg rs xrs \<and> \<comment>\<open> for ALU + MEM + Call \<close>
        match_mem m xm  \<comment>\<open> for MEM + Call \<close> \<and> 
        match_stack xrs xm  |
      _ \<Rightarrow> False
  ) |
  SBPF_Success v \<Rightarrow>(
    case xst of
    Next xpc xrs xm \<Rightarrow> v = xrs (bpf_to_x64_reg BR0) \<comment>\<open> for EXIT \<close> |
      _ \<Rightarrow> False
  ) |
  _ \<Rightarrow> False
)"*)

definition match_state :: "sbpf_state \<Rightarrow> hybrid_state \<Rightarrow> bool" where
"match_state bst hst = (
  case bst of
  SBPF_OK pc rs m ss \<Rightarrow> (
  let xst = snd hst; idx = fst hst in 
    case xst of
      Next xpc xrs xm xss\<Rightarrow>
        match_reg rs xrs \<and> \<comment>\<open> for ALU + MEM + Call \<close>
        match_mem m xm  \<comment>\<open> for MEM + Call \<close> \<and> 
        match_stack xrs \<and>
        ss = xss \<and>
        pc = idx  |
      _ \<Rightarrow> False
  ) |
  SBPF_Success v \<Rightarrow>(
    let xst = snd hst; idx = fst hst in 
    case xst of
    Next xpc xrs xm xss \<Rightarrow> v = xrs (IR (bpf_to_x64_reg BR0)) \<comment>\<open> for EXIT \<close> |
      _ \<Rightarrow> False
  ) |
  _ \<Rightarrow> False
)"




lemma match_mem_store_equiv: "
  match_mem m0 m1 \<Longrightarrow>
  storev mc m0 (Vlong addr) v = Some m0' \<Longrightarrow> 
  storev mc m1 (Vlong addr) v = Some m1' \<Longrightarrow>
  match_mem m0' m1'"
  apply (simp add: match_mem_def storev_def)
  apply (cases mc; cases v; simp add: u8_list_of_u16_def Let_def; force)
  done

lemma match_mem_store_1_equiv: "
  match_mem m0 m1 \<Longrightarrow>
  storev M64 m1 (Vptr b ofs) v = Some m1' \<Longrightarrow>
  match_mem m0 m1'"
  apply (simp add: match_mem_def storev_def)
  apply (cases " b = (0::nat)"; cases v; simp add: Let_def u8_list_of_u64_def)
  by force
  
lemma match_mem_load_1_equiv: "
  match_mem m0 m1 \<Longrightarrow>
  loadv mc m0 (Vlong addr) = Some v1 \<Longrightarrow>
  loadv mc m1 (Vlong addr) = Some v2 \<Longrightarrow>
  v1 = v2"
  apply (simp add: match_mem_def loadv_def)
  apply (cases mc; simp add: Let_def option_val_of_u64_def)
  apply (smt (verit, best) option_u64_of_u8_1_def memory_chunk.simps(13) option.collapse option.distinct(1) option.inject option.simps(4) val.simps(40))
  apply (smt (verit, del_insts) option.case_eq_if option.collapse option.distinct(1) option.sel option_u64_of_u8_2_def)
  using option_u64_of_u8_4_def apply (smt (verit, best) option.case_eq_if option.collapse option.distinct(1) option.inject) 
  using option_u64_of_u8_8_def by (smt (z3) option.case_eq_if option.collapse option.distinct(1) option.inject)


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
    s = (SBPF_OK pc rs mem ss) \<Longrightarrow>
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

lemma intermediate_step_is_ok:"sbpf_sem x prog s = s' \<Longrightarrow> x > 0 \<Longrightarrow> s' \<noteq> SBPF_Err \<Longrightarrow> \<exists> pc rs mem ss. s = (SBPF_OK pc rs mem ss)"
  apply(induct x arbitrary: prog s s')
  apply simp 
  using err_is_still_err suc_success_is_err
  using sbpf_step.elims
  by (metis (no_types, opaque_lifting))


lemma aux1:"length prog \<noteq> 0 \<and> unat pc < length prog \<and> unat pc \<ge> 0 \<Longrightarrow> 
  s' = sbpf_step prog s \<Longrightarrow>
  s = (SBPF_OK pc rs m ss) \<Longrightarrow> 
  s' = (SBPF_OK pc' rs' m' ss') \<Longrightarrow> 
  (\<exists> dst src. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_AND dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_ARSH dst (SOReg src)) \<or> 
  (\<exists> dst src chk off. prog!(unat pc) = BPF_LDX chk dst src off) \<or>
  (\<exists> dst src chk off. prog!(unat pc) = BPF_ST chk dst (SOReg src) off) \<or>
  (\<exists> x cond dst src. prog!(unat pc) = BPF_JUMP cond dst (SOReg src) x) \<or>
  (\<exists> src imm. prog!(unat pc) = BPF_CALL_IMM src imm) \<or>
  prog!(unat pc) = BPF_EXIT"
  apply(cases "prog!(unat pc)",simp_all)
  subgoal for x31 x32 x33 x34
    apply(unfold eval_store_def Let_def)
    by(cases x33,simp_all)
    subgoal for x91 x92 x93
   apply(unfold eval_alu_def Let_def)
    apply(cases x91,simp_all) 
     apply(cases x93, simp_all)
       apply(cases x93, simp_all)
      apply(cases x93, simp_all)
     apply(cases x93, simp_all)
          apply(cases x93, simp_all)
      apply(cases x93, simp_all)
        apply(cases x93, simp_all)
      apply(cases x93, simp_all)
      apply(cases x93, simp_all)
    done
  subgoal for x161 x162 x163 x164
    by(cases x163,simp_all)
  done
(*
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
qed*)


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
        apply(cases "per_jit_ins a", simp_all) 
        done
        (*subgoal for x15 by(cases "per_jit_ja (scast x15)",simp_all)
        subgoal for x15 aa by(cases "per_jit_ja (scast x15)",simp_all)
        done*)
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

lemma match_s_not_stuck:"match_state s (pc,xst) \<Longrightarrow> xst \<noteq> Stuck"
  apply(cases s, simp_all)
  apply(unfold match_state_def)
  subgoal for x11 x12 x13 by auto
  subgoal for x2 by auto
  by simp

(*lemma x64_sem1_induct_aux1:"x64_sem1 (Suc n) x64_prog (pc, Next xpc xrs m) = (pc+off,xst') \<Longrightarrow> 
  x64_prog!(unat pc) = (num,off,l) \<Longrightarrow>
  x64_sem num l (Next 0 xrs m) = xst1 \<Longrightarrow> 
  x64_sem1 n x64_prog (pc,xst1) = (pc+off,xst')"
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
  x64_sem1 n (pc+ off) x64_prog (Next 0 xrs1 m1) = xst'"
  using x64_sem1_induct_aux2 x64_sem1_induct_aux1 by metis
*)
lemma pc_scope_aux:"\<lbrakk> sbpf_sem n prog s = s'; s = (SBPF_OK pc rs m ss); s' = (SBPF_OK pc' rs' m' ss); prog \<noteq> []; n>0\<rbrakk> \<Longrightarrow> 
  unat pc < length prog \<and> unat pc \<ge> 0"
  by (metis (no_types, opaque_lifting) err_is_still_err linorder_not_less not_gr_zero sbpf_sem.elims sbpf_state.simps(6) sbpf_step.simps(1))
(*
lemma corr_pc_aux1_1:
  "jitper prog = Some x64_prog \<Longrightarrow> 
  prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src)} \<Longrightarrow>
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  off=0"
proof (induction prog arbitrary: x64_prog pc dst src num off l)
  case Nil
  then show ?case by simp
next
  case (Cons a prog)
  then show ?case
  proof-
    assume assm1:"(a # prog) ! unat pc \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src)}"
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    show ?thesis
    proof (cases "unat pc = 0")
      case True
      have b0_1:"unat pc = 0" using True a0 by simp
      have b0:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b1:"per_jit_ins a = Some x" using b0 by auto
      have b1_1:"(num,off,l) = x" using b0_1 b1 True Cons
        by (smt (verit) jitper.simps(2) nth_Cons_0 old.prod.case option.case_eq_if option.discI option.sel prod_cases3)
      
      have bn:"off = 0"
        using b1 apply(cases "per_jit_ins a", simp_all) apply(unfold per_jit_ins_def)
        apply(cases a,simp_all)
        subgoal for x21 x22 x23 x24
          using per_jit_load_reg64_def b1 b1_1 Let_def by auto
        subgoal for x31 x32 x33 x34 apply(cases x33,simp_all)
          subgoal for x2 using per_jit_store_reg64_def b1 b1_1 Let_def by auto
          done
        subgoal for x91 x92 x93
          apply(cases x91,simp_all)
              apply(cases x93,simp_all)         
          subgoal for x1 using b1 b1_1 per_jit_add_reg64_1_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x2 using b1 b1_1 per_jit_mul_reg64_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x3 using b1 b1_1 per_jit_shift_lsh_reg64_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x4 using b1 b1_1 per_jit_shift_rsh_reg64_def Let_def by auto
          apply(cases x93,simp_all) 
          subgoal for x4 using b1 b1_1 per_jit_shift_arsh_reg64_def Let_def by auto
          done 
        subgoal for x15 using assm1 b0_1 by(unfold per_jit_jcc_def Let_def,simp_all) 
        apply(unfold per_jit_exit_def Let_def, simp_all) using b1 b1_1 by blast 
      then show ?thesis using bn by blast
    next
      case False
      have "\<exists> res. jitper prog = Some res" using Cons 
        apply(cases "per_jit_ins a", simp_all) 
        by (metis (no_types, lifting) option.case_eq_if option.collapse)
      then obtain res where b0:"jitper prog = Some res" by auto
      have b1:"\<exists> x. per_jit_ins a = Some x" using Cons by (cases "per_jit_ins a"; auto)
      obtain x where b2:"per_jit_ins a = Some x" using b1 by auto
      have c0:" Some (x # res) = Some x64_prog" using b0 b2 Cons by auto
      have c1:"unat pc \<ge> 1" using a0 False by blast
      have c2:"x64_prog ! unat pc = (num,off,l)" using c0 Cons by simp
      let "?pc'" = "unat pc -1"
      have c3:"(num,off,l) = res! ?pc'" using c0 False c2 by auto
      have c4:"0 \<le> ?pc' \<and> ?pc' < length prog \<and> prog \<noteq> [] " using Cons c0 c1 by auto
      have c5:"off=0" using c3 c4 Cons.IH False b0 unat_minus_one unsigned_eq_0_iff 
        by (metis (no_types, lifting) assm1 nth_Cons')
      then show ?thesis by blast
    qed
  qed
qed
*)

lemma corr_pc_aux2:
  "jitper prog = Some x64_prog \<Longrightarrow> prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog \<Longrightarrow>
  s =  SBPF_OK pc rs m ss \<Longrightarrow>
  s' = sbpf_step prog s \<Longrightarrow> s' = SBPF_OK pc' rs' m' ss' \<Longrightarrow> 
  (num,off,l) = x64_prog!(unat pc) \<Longrightarrow>
  prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_SUB dst (SOReg src), 
  BPF_ALU64 BPF_OR dst (SOReg src), BPF_ALU64 BPF_AND dst (SOReg src), BPF_ALU64 BPF_XOR dst (SOReg src),
  BPF_ALU64 BPF_MUL dst (SOReg src), BPF_ALU64 BPF_LSH dst (SOReg src),BPF_ALU64 BPF_RSH dst (SOReg src), 
  BPF_ALU64 BPF_ARSH dst (SOReg src), BPF_LDX chk dst src d, BPF_ST chk dst (SOReg src) d} \<Longrightarrow>
  pc' = pc + 1" 
proof-
  assume assm0:"s' = sbpf_step prog s"  and
         assm1:"s' = SBPF_OK pc' rs' m' ss'" and
         assm2:"jitper prog = Some x64_prog" and
         assm3:"prog \<noteq> [] \<and> unat pc \<ge> 0 \<and> unat pc < length prog" and
         assm4:"s = SBPF_OK pc rs m ss" and
         assm5:"(num,off,l) = x64_prog!(unat pc)" and
         assm6:" prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_SUB dst (SOReg src), 
  BPF_ALU64 BPF_OR dst (SOReg src), BPF_ALU64 BPF_AND dst (SOReg src), BPF_ALU64 BPF_XOR dst (SOReg src),
  BPF_ALU64 BPF_MUL dst (SOReg src), BPF_ALU64 BPF_LSH dst (SOReg src),BPF_ALU64 BPF_RSH dst (SOReg src), 
  BPF_ALU64 BPF_ARSH dst (SOReg src), BPF_LDX chk dst src d, BPF_ST chk dst (SOReg src) d}"
  have c1:"pc' = pc+1 " using assm6 assm0 assm1 
    apply(cases "prog!(unat pc)",simp_all)
       (*prefer 4 using assm4 assm3 apply simp*)
      prefer 3 subgoal for x91 x92 x93 apply(erule disjE)
      using assm4 assm3 eval_alu_def apply simp 
      using assm4 assm3 eval_alu_def apply simp
      apply(cases x91,simp_all)
        apply(unfold eval_alu64_aux2_def Let_def) apply(cases BPF_LSH,simp_all)
      apply(unfold eval_alu64_aux3_def Let_def) apply(cases BPF_ARSH,simp_all)
      done
    apply (smt (z3) assm4 bpf_instruction.simps(362) option.case_eq_if sbpf_state.inject(1) sbpf_state.simps(6) sbpf_step.simps(1))
    using assm4 assm3 eval_store_def by(cases "eval_store chk dst (SOReg src) d rs m",simp_all)
  thus ?thesis using c1 by simp
qed



lemma x64_sem1_pc_aux1:
  assumes 
  a0:"s =  SBPF_OK pc rs m ss" and
  a1:"s' = sbpf_step prog s" and
  a2:"s' = SBPF_OK pc' rs' m' ss'" and 
  a3:"jitper prog = Some x64_prog" and
  a4:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a5:"xst = (Next xpc xrs xm xss)" and
  a6:"x64_prog!(unat pc) = (num,off,l)" and
  a7:"x64_sem num l (Next 0 xrs xm xss) = xst1 " and
  a8:"l!1 \<noteq> 0x39 \<and> l!0 \<noteq> 0xe8 \<and> l!0 \<noteq> 0xc3" and
  a10:"xst1 = Next xpc1 xrs1 xm1 xss1" and
  a11:"prog!(unat pc) \<in> {BPF_ALU64 BPF_ADD dst (SOReg src), BPF_ALU64 BPF_MUL dst (SOReg src),  
  BPF_ALU64 BPF_LSH dst (SOReg src),BPF_ALU64 BPF_RSH dst (SOReg src), BPF_ALU64 BPF_ARSH dst (SOReg src),
  BPF_LDX chk dst src d, BPF_ST chk dst (SOReg src) d}"
shows "x64_sem1 1 x64_prog (pc,xst) = (pc', Next xpc1 xrs1 xm1 xss1)"
proof-
  have "x64_sem1 1 x64_prog (pc,xst) = (let (num,off,l) = x64_prog!(unat pc) in
  let pair = let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in (pc+1, xst') in (x64_sem1 0 x64_prog pair))"
    using a5 a8 a6 one_step_def by simp
  hence "x64_sem1 1 x64_prog (pc,xst) = (x64_sem1 0 x64_prog (pc+1,xst1))" using a3 a4 a5 a6 a7 a8 one_step_def by simp
  hence "x64_sem1 1 x64_prog (pc,xst) = (pc+1, Next xpc1 xrs1 xm1 xss1)" using a10 by simp
  moreover have "pc+1=pc'" using corr_pc_aux2 a3 a0 a1 a2 a4 a11 a6 a8 by metis
  hence "x64_sem1 1 x64_prog (pc,xst) = (pc', Next xpc1 xrs1 xm1 xss1)" using calculation by blast
  thus ?thesis by blast
qed


lemma x64_sem1_pc_aux2:
  assumes 
  a0:"s =  SBPF_OK pc rs m ss" and
  a1:"s' = sbpf_step prog s" and
  a2:"s' = SBPF_OK pc' rs' m' ss'" and 
  a3:"jitper prog = Some x64_prog" and
  a4:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" and
  a5:"xst = (Next xpc xrs xm xss)" and
  a6:"x64_prog!(unat pc) = (num,off,l)" and
  a7:"x64_sem num l (Next 0 xrs xm xss) = xst1 " and
  a8:"l!0 \<noteq> 0xc3 \<and> l!0 \<noteq> 0xe8 \<and> l!1 = 0x39" and
  a10:"xst1 = Next xpc1 xrs1 xm1 xss1" and
  a11:"prog!(unat pc) \<in> {BPF_JUMP cond dst (SOReg src) d}" and
  a12:"match_state s (pc,xst)" and
  a13:"xrs (IR (bpf_to_x64_reg dst)) = xrs (IR (bpf_to_x64_reg src)) \<longrightarrow> xrs1 (CR ZF) = 1" and
  a14: "xrs (IR (bpf_to_x64_reg dst)) \<noteq> xrs (IR (bpf_to_x64_reg src)) \<longrightarrow> xrs1 (CR ZF) = 0"
shows "x64_sem1 1 x64_prog (pc,xst) = (pc', Next xpc1 xrs1 xm1 xss1)" 
proof-
  have c0:"x64_sem1 1 x64_prog (pc,xst) = (let (num,off,l) = x64_prog!(unat pc) in
  let pair = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
        case xst' of Next xpc' rs' m' s' \<Rightarrow>
          if rs' (CR ZF) = 1 then (off+pc, xst')
          else (pc+1, xst')|
         Stuck \<Rightarrow> (pc, Stuck))
   in (x64_sem1 0 x64_prog pair))"
    using a5 a8 a6 one_step_def by auto
  have b0:"(num,off,l) = the (per_jit_ins (prog!(unat pc)))" using aux5 a0 a1 a2 a7 a11 a3 a4 a6 by blast
  have b1:"(num,off,l) = the (per_jit_jcc cond dst src (scast d))" using b0 a11 per_jit_ins_def by simp
  have b2:"cond = Eq" sorry
  thus ?thesis
  proof(cases "rs src = rs dst")
    case True
    hence b3:"eval_jmp cond dst (SOReg src) rs" using a2 a3 a4 a5 a6 b2 eval_jmp_def eval_reg_def by fastforce
    hence b4:"pc' = pc + scast d + 1" using a11 a4 b2 eval_reg_def a0 a1 a2 by simp
    have c1:"xrs (IR (bpf_to_x64_reg dst)) = xrs (IR (bpf_to_x64_reg src))" 
      using bpf_to_x64_reg_def True a12 match_state_def a0 a5 match_reg_def by auto
    have c2:"xrs1 (CR ZF) = 1" using True a10 a7 a13 c1 by simp
    have c3:"x64_sem1 1 x64_prog (pc,xst) = (let (num,off,l) = x64_prog!(unat pc)
      in (x64_sem1 0 x64_prog ((off+pc, xst1))))" using c2 c0 a5 a7 a10 a6 one_step_def by auto
    have c4:"x64_sem1 1 x64_prog (pc,xst) = (off+pc, Next xpc1 xrs1 xm1 xss1)" using c3 a6 a10 by force
    have c5:"off = scast d + 1" using b1 per_jit_jcc_def b2 by auto
    then show ?thesis using b4 c4 c5 by simp
  next
    case False
    have b3:"rs src \<noteq> rs dst" using False by simp
    hence "\<not> eval_jmp cond dst (SOReg src) rs" 
      apply(unfold eval_jmp_def Let_def eval_reg_def,simp_all)
      using b2 by(cases cond,simp_all)
    hence b4:"pc' = pc + 1" 
    using a11 a4 a5 a6 b2 eval_reg_def a0 a1 a2 eval_reg_def by auto
    
    have c1:"xrs (IR (bpf_to_x64_reg dst)) \<noteq> xrs (IR (bpf_to_x64_reg src))"
      using bpf_to_x64_reg_def False a12 match_state_def a0 a5 match_reg_def by auto
    have c2:"xrs1 (CR ZF) = 0" using False a10 a7 a14 c1 by auto
    have c3:"x64_sem1 1 x64_prog (pc,xst) = (let (num,off,l) = x64_prog!(unat pc)
      in (x64_sem1 0 x64_prog ((1+pc, xst1))))" using c2 c0 a5 a7 a10 a6 by auto
    have c4:"x64_sem1 1 x64_prog (pc,xst) = (1+pc, Next xpc1 xrs1 xm1 xss1)" using c3 a6 a10 by force
    then show ?thesis using c4 b4 by simp
  qed
qed




lemma match_state_eqiv:"match_state s (pc,Next xpc' xrs' xm' xss') = match_state s (pc,Next 0 xrs' xm' xss')"
  using match_state_def 
  apply(cases s,simp_all)
  done

(*
value "(x64_encode (Pmovq_rr R11 RBX)@(x64_encode (Ppushl_r RDX)) @ (x64_encode (Pmulq_r R11)) @ (x64_encode (Ppopl RDX)))"*)
(*[1001001,10001001,11011011,1010010,1001001,11110111,11100011,1011010]*)
end