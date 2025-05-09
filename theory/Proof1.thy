theory Proof1
imports
  Main
  rBPFCommType rBPFSyntax x64Assembler x64Disassembler x64DecodeProofAux

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

(*
lemma list_in_list_prop2:"list_in_list l1 0 l2 \<Longrightarrow> list_in_list l2 0 l3 \<Longrightarrow> list_in_list l1 0 l3"
  using list_in_list_prop_aux1
  sorry*)

axiomatization where x64_encode_decode_consistency: 
  "list_in_list l_bin pc l \<Longrightarrow>
  l_bin = x64_encode ins \<Longrightarrow>
  length l_bin = n \<Longrightarrow>
  x64_decode pc l = Some (n, ins)"

end