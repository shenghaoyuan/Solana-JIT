theory Proof1
imports
  Main
  rBPFCommType rBPFSyntax x64Assembler x64Disassembler

begin

value "x64_decode 0 (the (x64_encode (Paddq_rr RAX RBX)))"
           
lemma x64_encode_decode_consistency:
  "Some l_bin = x64_encode ins \<Longrightarrow>
    x64_decode 0 l_bin = Some (length l_bin, ins)"
  apply(cases ins,simp_all)
   prefer 2 apply(unfold x64_decode_def, simp_all)
  subgoal for dst src 
        apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; simp;cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          Suc3_eq_add_3 add.commute)
    done
  done
end