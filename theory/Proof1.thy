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
  subgoal for dst src 
    \<comment> \<open> Paddq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases src; simp;cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          Suc3_eq_add_3 add.commute)
    done
   apply(unfold x64_decode_def;auto)
  subgoal for dst
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
 subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
  done
  defer
 subgoal for dst src
  \<comment> \<open> Pmovq_rr \<close> 
   apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
   (*apply(erule conjE; erule conjE)*)
   subgoal by (cases src; cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done
  subgoal for dst 
    \<comment> \<open> Pmulq_r \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal by (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
    done
  subgoal for dst
    \<comment> \<open> Ppopl_i \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    apply (cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def)
  done
  done

(*lemma x64_encodes_decodes_consistency:
  "Some l_bin = x64_encodes2 ins \<Longrightarrow>
    x64_decodes 0 l_bin = Some ins_list \<Longrightarrow>
    map snd ins_list = ins" 
  sorry*)
(*
value "x64_decode 0 [0b01001000,0b00000001,0b11011000]"
value "x64_decodes_aux 0 [0xc3,0b01001000,0b00000001,0b11011000]"
value "x64_decodes 0 [0xc3,0b01001000,0b00000001,0b11011000]"
value "x64_decode 1 [0xc3,0b01001000,0b00000001,0b11011000]"
value "x64_encodes_suffix []"
value "x64_decodes 0 []"*)




end