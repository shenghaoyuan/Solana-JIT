section \<open> x64 Semantics \<close>

theory x64Semantics
imports
  Main
  rBPFCommType Val Mem x64Syntax x64Disassembler x64Assembler
begin

(*axiomatization x64_decode :: "nat \<Rightarrow> u8 list \<Rightarrow> (nat * instruction) option"*)

text \<open> define our x64 semantics in Isabelle/HOL, following the style of CompCert x64 semantics: https://github.com/AbsInt/CompCert/blob/master/x86/Asm.v  \<close>


type_synonym regset = "preg \<Rightarrow> u64"

syntax "_pregmap_set" :: "'a => 'b => 'c => 'a" ("_ # _ <- _" [1000, 1000, 1000] 1)

(* Define the translation for the notation *)
translations
  "_pregmap_set a b c" => "(a(b := c))"

fun undef_regs :: "preg list \<Rightarrow> regset \<Rightarrow> regset" where
"undef_regs [] rs = rs" |
"undef_regs (r#l') rs = undef_regs l' (rs#r <- 0)"

datatype outcome = Next u64 regset mem | Stuck

definition exec_ret :: "memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> outcome" where
"exec_ret chunk m rs = (
  let nsp =  (rs (IR SP)) + (u64_of_memory_chunk chunk) in
    case Mem.loadv M64 m (Vlong nsp) of
    None \<Rightarrow> Stuck |
    Some ra \<Rightarrow> (
      case ra of
      Vlong v \<Rightarrow> let rs1 = rs#(IR SP) <- nsp in
                  Next v rs1 m |
      _ \<Rightarrow> Stuck)
)"

definition exec_pop :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> ireg \<Rightarrow> outcome" where
"exec_pop pc sz chunk m rs rd = (
  let nsp = (rs (IR SP)) + (u64_of_memory_chunk chunk) in
    let addr = (rs (IR SP)) in
      case Mem.loadv chunk m (Vptr sp_block addr) of
        None \<Rightarrow> Stuck |
        Some x => 
          (case x of Vlong v \<Rightarrow> let rs1 =rs # (IR SP) <- nsp  in
          Next (pc + sz) (rs1#(IR rd) <- v ) m |
                     _ \<Rightarrow> Stuck)
)"

definition exec_push :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> regset \<Rightarrow> usize \<Rightarrow> outcome" where
"exec_push pc sz chunk m rs v = ( 
  let nsp = (rs (IR SP)) - (u64_of_memory_chunk chunk) in
      case Mem.storev chunk m (Vptr sp_block nsp) (Vlong v) of
        None \<Rightarrow> Stuck |
        Some m' => Next (pc + sz) (rs#(IR SP) <- nsp) m'
)"

definition of_optbool :: " bool \<Rightarrow> u64" where
"of_optbool ob = (case ob of True \<Rightarrow> 1 | False \<Rightarrow> 0)"

definition compare_longs :: "u64 \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> regset" where
"compare_longs x y rs = ((((rs#(CR ZF) <- (of_optbool (x = y)))
                            #(CR CF) <- (of_optbool (x < y)))
                            #(CR SF) <- (if scast(x-y) <s (0::i64) then 1 else 0))
                            #(CR OF) <- (sub_overflowi64 x y 0))"

definition eval_testcond :: "testcond \<Rightarrow> regset \<Rightarrow> bool option" where
"eval_testcond c rs = (
  case c of
  Cond_e  \<Rightarrow> (Some (rs (CR ZF) = 1)) | 
  Cond_ne \<Rightarrow> (Some (rs (CR ZF) = 0)) |
  Cond_b  \<Rightarrow> (Some (rs (CR CF) = 1)) |
  Cond_be \<Rightarrow> (Some (rs (CR CF) = 1 \<or> rs (CR ZF) = 1)) |
  Cond_ae \<Rightarrow> (Some (rs (CR CF) = 0)) |      
  Cond_a  \<Rightarrow> (Some (rs (CR CF) = 0 \<or> rs (CR ZF) = 0)) |
  Cond_l  \<Rightarrow> (let n = rs (CR OF); s = rs (CR SF) in 
             Some ((xor n s) = 1)) |
  Cond_le \<Rightarrow> (let n = rs (CR OF); s = rs (CR SF); z = rs (CR ZF) in 
             Some ((xor n s) = 1 \<or> z = 1)) |
  Cond_ge \<Rightarrow> (let n = rs (CR OF); s = rs (CR SF) in Some ((xor n s) = 0)) |
  Cond_g  \<Rightarrow> (let n = rs (CR OF); s = rs (CR SF); z = rs (CR ZF) in 
              Some ((xor n s) = 0 \<and> z = 0)) |
  Cond_p  \<Rightarrow> (Some (rs (CR PF) = 1)) |
  Cond_np \<Rightarrow> (Some (rs (CR PF) = 0))
)"

definition eval_addrmode64 :: "addrmode \<Rightarrow> regset \<Rightarrow> u64" where
"eval_addrmode64 a rs = 
  (case a of Addrmode base ofs const \<Rightarrow>
    (case base of None \<Rightarrow> 0 | 
                  Some r \<Rightarrow> (rs (IR r)))
    +
      ((case ofs of None \<Rightarrow> 0 |
                    Some (r2, sc) \<Rightarrow> (rs (IR r2)) << (unat sc)) 
    + (scast const)) 
)"

definition exec_load :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> addrmode \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> outcome" where
"exec_load pc sz chunk m a rs rd = (
  let addr =  eval_addrmode64 a rs in
    case Mem.loadv chunk m (Vlong addr) of
      None \<Rightarrow> Stuck | 
      Some ra \<Rightarrow> 
        (case ra of Vlong v \<Rightarrow> Next (pc+sz) (rs#rd <- v) m | 
                          _ \<Rightarrow> Stuck)
)"

(*preg list?*)
definition exec_store :: "usize \<Rightarrow> u64 \<Rightarrow> memory_chunk \<Rightarrow> mem \<Rightarrow> addrmode \<Rightarrow> regset \<Rightarrow> preg \<Rightarrow> outcome" where
"exec_store pc sz chunk m a rs r1 = (
  let addr =  eval_addrmode64 a rs in (
    case Mem.storev chunk m (Vlong addr) (Vlong (rs r1)) of
      None \<Rightarrow> Stuck |
      Some m' \<Rightarrow> Next (pc+ sz) rs m'
  )
)"


(*
definition exec_jcc::"usize \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> testcond \<Rightarrow> i32 \<Rightarrow> outcome" where
"exec_jcc pc sz rs m t d \<equiv> 
  (case eval_testcond t rs of 
     Some b \<Rightarrow> if b then Next (scast d) rs m 
     else Next (pc+sz) rs m |
          None \<Rightarrow> Stuck)"*)
(*
definition eval_testcond :: "testcond \<Rightarrow> regset \<Rightarrow> bool option" where
"eval_testcond c rs = (
  case c of
  Cond_e  \<Rightarrow> (case rs (CR ZF) of Vint n \<Rightarrow> Some (n = 1) | _ \<Rightarrow> None) |      
  Cond_ne \<Rightarrow> (case rs (CR ZF) of Vint n \<Rightarrow> Some (n = 0) | _ \<Rightarrow> None) |
  Cond_b  \<Rightarrow> (case rs (CR CF) of Vint n \<Rightarrow> Some (n = 1) | _ \<Rightarrow> None) |      
  Cond_be \<Rightarrow> (case rs (CR CF) of Vint c \<Rightarrow> (
                case rs (CR ZF) of  Vint z \<Rightarrow> Some (c = 1 \<or> z = 1) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_ae \<Rightarrow> (case rs (CR CF) of Vint n \<Rightarrow> Some (n = 0) | _ \<Rightarrow> None) |      
  Cond_a  \<Rightarrow> (case rs (CR CF) of Vint c \<Rightarrow> (
                case rs (CR ZF) of  Vint z \<Rightarrow> Some (c = 0 \<or> z = 0) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_l  \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> Some ((xor n s) = 1) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_le \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> (
                  case rs (CR ZF) of Vint z \<Rightarrow> Some ((xor n s) = 1 \<or> z = 1) | _ \<Rightarrow> None) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_ge \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> Some ((xor n s) = 0) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_g  \<Rightarrow> (case rs (CR OF) of Vint n \<Rightarrow> (
                case rs (CR SF) of  Vint s \<Rightarrow> (
                  case rs (CR ZF) of Vint z \<Rightarrow> Some ((xor n s) = 0 \<and> z = 0) | _ \<Rightarrow> None) |
                                    _ \<Rightarrow> None) | _ \<Rightarrow> None) |
  Cond_p  \<Rightarrow> (case rs (CR PF) of Vint n \<Rightarrow> Some (n = 1) | _ \<Rightarrow> None) |
  Cond_np \<Rightarrow> (case rs (CR PF) of Vint n \<Rightarrow> Some (n = 0) | _ \<Rightarrow> None)
)"*)

(*Pjmp       d    \<Rightarrow> Next (scast d) rs m*)
definition exec_instr :: "instruction \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> regset \<Rightarrow> mem \<Rightarrow> outcome" where
"exec_instr i sz pc rs m = (\<comment> \<open> sz is the binary size (n-byte) of current instruction  \<close>
  case i of
  Paddq_rr  rd r1 \<Rightarrow> Next (pc + sz) ((rs#(IR rd) <- (rs (IR rd) + rs (IR r1)))) m |
  Pret            \<Rightarrow> exec_ret M64 m rs |
  Ppopl     rd    \<Rightarrow> exec_pop pc sz M64 m rs rd |
  Ppushl_r  r1    \<Rightarrow> exec_push pc sz M64 m rs (rs (IR r1)) |
  Pmovq_rr rd r1  \<Rightarrow> Next (pc + sz) (rs#(IR rd) <- (rs (IR r1))) m |
  Pmulq_r   r1    \<Rightarrow> let rs1 = rs#(IR RAX) <- ((rs (IR RAX))*(rs (IR r1))) in
                     Next (pc + sz) (rs1#(IR RDX) <-( (rs (IR RAX))*(rs (IR r1)) div (2 ^ 32))) m |
  Pjcc      t d    \<Rightarrow> (case eval_testcond t rs of Some b \<Rightarrow> 
                          if b then Next (scast d) rs m 
                          else Next (pc+sz) rs m | 
                        None \<Rightarrow> Stuck) |
  Pcmpq_rr rd r1 \<Rightarrow> Next (pc+sz)(compare_longs (rs (IR r1)) (rs (IR rd)) rs) m |
  Pmovq_ri rd n  \<Rightarrow> Next (pc + sz) (rs#(IR rd) <- n) m |
  Pmov_mr  a r1 c \<Rightarrow> exec_load  pc sz c m a rs (IR r1) |                    \<comment> \<open> store reg to mem \<close>
  Pxchgq_rr rd r1 \<Rightarrow> let tmp = rs (IR rd) in
                     let rs1 = (rs#(IR rd)<- (rs (IR r1))) in
                       Next (pc + sz) (rs1#(IR r1)<- tmp) m |
  Pshlq_r   rd    \<Rightarrow> Next (pc + sz) (rs#(IR rd) <- ((rs (IR rd))<< (unat (and ( (ucast (rs(IR RCX)))::u32) (63::u32))))) m |
  Pshrq_r   rd    \<Rightarrow> Next (pc + sz) (rs#(IR rd) <- ((rs (IR rd))>> (unat (and ( (ucast (rs(IR RCX)))::u32) (63::u32))))) m |
  Psarq_r   rd    \<Rightarrow> Next (pc + sz) (rs#(IR rd) <- (ucast (((scast (rs (IR rd)))::i64) >> (unat (and ( (ucast (rs(IR RCX)))::u32) (63::u32)))))) m |
  Pmov_rm  rd a c \<Rightarrow> exec_store pc sz c m a rs (IR rd) 
)"


fun x64_sem :: "nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem 0 _ st = st" |
"x64_sem (Suc n) l Stuck = Stuck"|
"x64_sem (Suc n) l (Next pc rs m) = (
  case x64_decode (unat pc) l of
  None \<Rightarrow> Stuck |
  Some (sz, ins) \<Rightarrow>
    x64_sem n l (exec_instr ins (of_nat sz) pc rs m)
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

type_synonym hybrid_state = "u64 \<times> outcome"

definition one_step:: " (nat \<times> u64 \<times> x64_bin) list \<Rightarrow> hybrid_state\<Rightarrow> hybrid_state" where
"one_step lt st  \<equiv>
  let pc = fst st; xst = snd st in 
  let (num,off,l) = lt!(unat pc) in
    case xst of
    Next xpc rs m \<Rightarrow> (
      if l!1 = (0x39::u8) then 
        let xst_temp = Next 0 rs m; xst' = x64_sem num l xst_temp in
          case xst' of
          Next xpc' rs' m' \<Rightarrow>
            if rs' (CR ZF) = 1 then (off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck)
      else
        let xst_temp = Next 0 rs m; xst' = x64_sem num l xst_temp in
          (pc+1, xst'))
    | Stuck \<Rightarrow> (pc,Stuck)"

fun x64_sem1 :: "nat \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"x64_sem1 0 _ (pc,st) = (pc,st)" |
"x64_sem1 (Suc n) lt (pc,xst) = (
  let pair = one_step lt (pc,xst) in
    (x64_sem1 n lt pair))"
(*
fun x64_sem1 :: "nat \<Rightarrow> u64 \<Rightarrow> (nat \<times> u64 \<times> x64_bin) list \<Rightarrow> outcome \<Rightarrow> outcome" where
"x64_sem1 0 _ _ st = (let xst_temp =
   case st of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck in xst_temp )" |
"x64_sem1 (Suc n) pc lt xst = (
  let (num,off,l) = lt!(unat pc) in
  let xst_temp = (
    case xst of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck) in
    if l!0 = 0xE9 then x64_sem1 n (pc+off) lt xst else
  let xst' = x64_sem num l xst_temp in (
    x64_sem1 n (pc+off) lt xst'))"
*)

type_synonym x64_state = outcome

value "scast (100::u64) ::i64"

value "ucast((scast (100::u64) ::i64) + (-1::i64))::u64"

end
