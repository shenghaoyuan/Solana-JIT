section \<open> JITExtraction: extract to OCaml for evaluation \<close>

text\<open> ...
 \<close>

theory JITExtraction
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem rBPFDecoder
  x64Syntax x64Semantics x64Assembler
  x64DecodeProofAux
  JITPer_aux

begin

fun list_embedd_in_list :: "u8 list \<Rightarrow> u8 list \<Rightarrow> (u8 list) option" where
"list_embedd_in_list [] l = Some l" |
"list_embedd_in_list (x#xs) [] = None" |
"list_embedd_in_list (x#xs) (y#ys) = (
  if x = y then
    list_embedd_in_list xs ys
  else
    list_embedd_in_list (x#xs) ys
)"

value "list_embedd_in_list (1#2#[]) (1#3#2#2#5#[])"

fun dlist_embedd_in_list :: "(u8 list) list \<Rightarrow> u8 list \<Rightarrow> bool" where
"dlist_embedd_in_list [] _ = True" |
"dlist_embedd_in_list (x#xs) l = (
  case list_embedd_in_list x l of
  None \<Rightarrow> False |
  Some l1 \<Rightarrow> dlist_embedd_in_list xs l1
)"

value "dlist_embedd_in_list ([1#2#[], 2#5#[]]) (1#3#2#2#5#[])"
value "dlist_embedd_in_list ([1#2#[], 1#2#[]]) (1#3#2#2#5#[])"

definition int_to_u8_list :: "int list \<Rightarrow> u8 list" where
"int_to_u8_list lp = (map (\<lambda>i. of_int i) lp)"

definition jit_evaluation :: "int list \<Rightarrow> int list \<Rightarrow> bool" where
"jit_evaluation ebpf_prog compiled_progam = (
  let ebpf_binary = int_to_u8_list ebpf_prog in
  let jit_prog = int_to_u8_list compiled_progam in
    case bpf_find_prog ((length ebpf_binary) div 8) 0 ebpf_binary of
    None \<Rightarrow> False |
    Some l_ebpf_asm \<Rightarrow> (
      case jitper l_ebpf_asm of
      None \<Rightarrow> False |
      Some l_bin3 \<Rightarrow>
        let l_bin = map (\<lambda> x. snd (snd x)) l_bin3 in
          dlist_embedd_in_list l_bin jit_prog
))"

end