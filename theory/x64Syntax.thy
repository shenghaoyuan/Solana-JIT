section \<open> x64 Syntax \<close>

theory x64Syntax
imports
  Main
  rBPFCommType Mem
begin
  
subsection  \<open> x64 Syntax \<close>

datatype ireg = RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15

(*
fun u8_of_ireg ::"ireg \<Rightarrow> u8" where
"u8_of_ireg RAX = 0" |
"u8_of_ireg RBX = 1" |
"u8_of_ireg RCX = 2" |
"u8_of_ireg RDX = 3" |
"u8_of_ireg RSI = 4" |
"u8_of_ireg RDI = 5" |
"u8_of_ireg RBP = 6" |
"u8_of_ireg RSP = 7" |
"u8_of_ireg R8  = 8" |
"u8_of_ireg R9  = 9" |
"u8_of_ireg R10 = 10" |
"u8_of_ireg R11 = 11" |
"u8_of_ireg R12 = 12" |
"u8_of_ireg R13 = 13" |
"u8_of_ireg R14 = 14" |
"u8_of_ireg R15 = 15" *)

text \<open> TODO: Solana rBPF uses the following mapping, very weird.
I don't understand, see: https://github.com/solana-labs/rbpf/blob/main/src/x86.rs#L16 
But this mapping doesn't effect x64 semantics, only binary code
\<close>

fun u8_of_ireg ::"ireg \<Rightarrow> u8" where
"u8_of_ireg RAX = 0" |
"u8_of_ireg RCX = 1" |
"u8_of_ireg RDX = 2" |
"u8_of_ireg RBX = 3" |
"u8_of_ireg RSP = 4" | 
"u8_of_ireg RBP = 5" |
"u8_of_ireg RSI = 6" |
"u8_of_ireg RDI = 7" |
"u8_of_ireg R8  = 8" |        
"u8_of_ireg R9  = 9" |
"u8_of_ireg R10 = 10" |
"u8_of_ireg R11 = 11" |
"u8_of_ireg R12 = 12" |
"u8_of_ireg R13 = 13" |
"u8_of_ireg R14 = 14" |
"u8_of_ireg R15 = 15"

definition ireg_of_u8 ::"u8 \<Rightarrow> ireg option" where
"ireg_of_u8 i = (                
        if i = 0 then
    Some RAX
  else  if i = 1 then
    Some RCX
  else  if i = 2 then
    Some RDX
  else  if i = 3 then
    Some RBX
  else  if i = 4 then
    Some RSP
  else  if i = 5 then
    Some RBP
  else  if i = 6 then
    Some RSI
  else  if i = 7 then
    Some RDI
  else  if i = 8 then
    Some R8
  else  if i = 9 then
    Some R9
  else  if i = 10 then
    Some R10
  else  if i = 11 then
    Some R11
  else  if i = 12 then
    Some R12
  else  if i = 13 then
    Some R13
  else  if i = 14 then
    Some R14
  else  if i = 15 then
    Some R15
  else
    None
)"


text \<open> skip float registers, as Solana rBPF doesn't deal with float \<close>

datatype crbit = ZF | CF | PF | SF | OF

datatype preg = IR ireg | CR crbit 

type_synonym label = nat
(*
datatype preg = PC | IR ireg | CR crbit

abbreviation "RIP \<equiv> PC"  \<comment> \<open> the RIP register in x86-64 (x64) architecture is the equivalent of the program counter (PC) in many other architectures.  \<close>
    *)

abbreviation "SP \<equiv> RSP"

datatype addrmode =
  Addrmode "ireg option" "(ireg * u8) option" u32

datatype testcond =
    Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np

fun u8_of_cond :: "testcond \<Rightarrow> u8" where
"u8_of_cond Cond_b  = 2" |  (* B, NAE: Below, Not above or equal *)
"u8_of_cond Cond_ae = 3" |  (* NB, AE: Not below, Above or equal *)
"u8_of_cond Cond_e  = 4" |  (* E, Z: Equal, Zero *)
"u8_of_cond Cond_ne = 5" |  (* NE, NZ: Not equal, Not zero *)
"u8_of_cond Cond_be = 6" |  (* BE, NA: Below or equal, Not above *)
"u8_of_cond Cond_a  = 7" |  (* NBE, A: Not below or equal, Above *)
"u8_of_cond Cond_p  = 10" | (* P, PE: Parity, Parity Even *)
"u8_of_cond Cond_np = 11" | (* NP, PO: Not parity, Parity Odd *)
"u8_of_cond Cond_l  = 12" | (* L, NGE: Less than, Not greater than or equal *)
"u8_of_cond Cond_ge = 13" | (* NL, GE: Not less than, Greater than or equal to *)
"u8_of_cond Cond_le = 14" | (* LE, NG: Less than or equal to, Not greater than *)
"u8_of_cond Cond_g  = 15"   (* NLE, G: Not less than or equal to, Greater*)

definition cond_of_u8 :: "u8 \<Rightarrow> testcond option" where
"cond_of_u8 i = (
  if i = 2 then
    Some Cond_b
  else  if i = 3 then
    Some Cond_ae
  else  if i = 4 then
    Some Cond_e
  else  if i = 5 then
    Some Cond_ne
  else  if i = 6 then
    Some Cond_be
  else  if i = 7 then
    Some Cond_a
  else  if i = 10 then
    Some Cond_p
  else  if i = 11 then
    Some Cond_np
  else  if i = 12 then
    Some Cond_l
  else  if i = 13 then
    Some Cond_ge
  else  if i = 14 then
    Some Cond_le
  else  if i = 15 then
    Some Cond_g
  else
    None
)"

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions for types: Pmov_rm   rd a c  \<Rightarrow> exec_store  sz c m a rs (IR rd) [] |                 \<comment> \<open> load  mem to reg \<close>
  Pmov_mr   a r1 c  \<Rightarrow> exec_load   sz c m a rs (IR r1) |            
- [b]: 8 bits
- [w]: 16 bits ("word")
- [l]: 32 bits ("longword")
- [q]: 64 bits ("quadword")
- [d] or [sd]: FP double precision (64 bits)
- [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

(*Pcall_r ireg*)
datatype instruction =
  Paddq_rr ireg ireg
  | Psubq_rr ireg ireg
  | Porq_rr ireg ireg
  | Pandq_rr ireg ireg
  | Pxorq_rr ireg ireg
  | Pret
  | Ppushl_r ireg
  | Ppopl  ireg
  | Pmovq_rr ireg ireg       (**r [mov] (integer) *)
  | Pmovq_ri ireg u64      (**r [mov] (integer) *)
  | Pimulq_r ireg
  | Pjcc testcond i32
  | Pcmpq_rr ireg ireg
  | Pmov_mr addrmode ireg memory_chunk
  | Pxchgq_rr ireg ireg
  | Pshrq_r ireg
  | Pshlq_r ireg
  | Psarq_r ireg
  | Pmov_rm ireg addrmode memory_chunk
  | Pcall_i u32

type_synonym x64_asm = "instruction list"
type_synonym x64_bin = "u8 list"

lemma u8_of_ireg_of_u8_iff: "(u8_of_ireg r = i) = (ireg_of_u8 i = Some r)"
  by (cases r, auto simp add: ireg_of_u8_def)

end