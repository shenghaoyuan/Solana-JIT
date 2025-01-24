theory x64Assembler
  imports Main rBPFCommType rBPFSyntax x64Syntax x86CommType

begin
fun x64_encode :: "instruction \<Rightarrow> x64_bin option" where
"x64_encode ins = (
case ins of
Paddq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x01 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  Pret \<Rightarrow>
    Some [0xc3] |
  _ \<Rightarrow> None)"


value "x64_encode (Paddq_rr RAX RBX)"
value "x64_encode (Pret)"

value "construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg R14) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg R15) 0b1000 \<noteq> 0)"

end