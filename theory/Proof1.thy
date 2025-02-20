theory Proof1
imports
  Main
  rBPFCommType rBPFSyntax x64Assembler x64Disassembler

begin

value "x64_decode 0 (x64_encode (Paddq_rr RAX RBX))"

lemma list_in_list_prop_aux1:"x@[] = x"
  by blast

lemma list_in_list_prop_aux2: "list_in_list l2 (length l1) (l1@l2@l3)"
  apply (induction l2 arbitrary: l1 l3)
  subgoal for l1 l3
    by simp
  subgoal for a l2 l1 l3
    apply simp
    by (metis append.left_neutral append_Cons append_assoc length_append_singleton)
  done

lemma list_in_list_prop:"list_in_list l 0 l"
  using list_in_list_prop_aux1
  by (metis append_Nil list_in_list_prop_aux2 list.size(3))

lemma x64_encode_decode_consistency:
 "list_in_list l_bin pc l \<Longrightarrow>
   l_bin = x64_encode ins \<Longrightarrow>
   x64_decode pc l = Some (length l_bin, ins)"
  sorry
  (*apply(cases ins,simp_all)
  subgoal for dst src 
    \<comment> \<open> Paddq_rr \<close> 
    apply (unfold Let_def construct_rex_to_u8_def construct_modsib_to_u8_def)
    subgoal apply (cases src; simp;cases dst; auto simp add: x64_decode_def bitfield_insert_u8_def Let_def ireg_of_u8_def
          Suc3_eq_add_3 add.commute)
      done
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
  done*)

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