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
  \<comment> \<open> P2884 `MUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 0111 : 11 100 qowrdreg` \<close>
  Pmulq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg r1) in
      Some [ rex, op, rop] |
  \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
  Pmovq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x89 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      Some [ rex, op, rop ] |
  \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
  Ppushl_r  r1 \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = bitfield_insert_u8 0 3 0x50 (u8_of_ireg r1) in
      if rex = 0x40 then
        Some [op]
      else 
        Some [rex, op] |
  \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
  Ppopl rd \<Rightarrow>
    let (rex::u8) = (construct_rex_to_u8    \<comment> \<open> `000B` \<close>
      False \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = bitfield_insert_u8 0 3 0x58 (u8_of_ireg rd) in
      if rex = 0x40 then
        Some [op]
      else 
        Some [rex, op] )"


value "x64_encode (Paddq_rr RAX RBX)"
value "x64_encode (Pret)"

value "construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg R14) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg R15) 0b1000 \<noteq> 0)"


(*fun list_in_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_in_list [] _ _ = True" |
"list_in_list (h#t) n l = (h = l!n \<and> list_in_list t (Suc n) l)"*)

fun x64_encodes_aux :: "instruction list \<Rightarrow> x64_bin option list" where
"x64_encodes_aux [] = [None]" |
"x64_encodes_aux (h#t) = (let ins' = x64_encode h in 
                        (case ins' of None \<Rightarrow> [None] |
                                      Some v \<Rightarrow> [Some v] @ x64_encodes_aux t))"

definition x64_encodes:: "instruction list \<Rightarrow> x64_bin list option" where
"x64_encodes xs = (let x = x64_encodes_aux xs in if x = [None] then None  
                   else Some (map Option.the (butlast x)))"

primrec flat :: "'a list list => 'a list" where
  "flat [] = []" |
  "flat (x # xs) = x @ flat xs"

definition x64_encodes_suffix:: "instruction list \<Rightarrow> x64_bin option" where
"x64_encodes_suffix xs = (let l = x64_encodes xs in (if l = None then None else Some (flat (Option.the l))))"



(*primrec flat2 :: "'a list list option=> 'a list option" where
  "flat2 None = None" |
  "flat2 res = x @ flat xs"*)

fun x64_encodes1 :: "instruction list \<Rightarrow> x64_bin list option" where
  "x64_encodes1 [] = Some []" |
  "x64_encodes1 (h#xs) = (case x64_encode h of 
                            None \<Rightarrow> None |
                            Some x \<Rightarrow> 
                              (case x64_encodes1 xs of
                                None \<Rightarrow> None |
                                Some res \<Rightarrow> Some (x#res)))"

definition x64_encodes2 :: "instruction list \<Rightarrow> x64_bin option" where
"x64_encodes2 xs = (let x = (x64_encodes1 xs) in 
    case x of None \<Rightarrow> None |
              Some x \<Rightarrow> Some (flat x))"

lemma x64_encodes1_induct:"x64_encodes1 insns = Some res \<Longrightarrow>
  insns = (h#xs) \<Longrightarrow>
  (x64_encode h) = Some res1 \<Longrightarrow> 
  (x64_encodes1 xs) = Some res2 \<Longrightarrow>
  res = res1#res2"
  apply(induction insns arbitrary: res h xs res1 res2)
   apply simp
  subgoal for a insns res h xs res1 res2 by simp
  done


lemma x64_encodes2_equiv:"Some res = x64_encode ins \<Longrightarrow>
  Some resn = x64_encodes2 [ins] \<Longrightarrow>
  res = resn"
  using x64_encodes2_def by (metis (mono_tags) append.right_neutral flat.simps(1) flat.simps(2) option.sel option.simps(5) x64_encodes1.simps(1) x64_encodes1.simps(2))

lemma x64_encodes2_induct:
  assumes 
  a1:"x64_encodes2 insns = Some res" and
  a2:"insns = (h#xs)" and
  a3:"(x64_encode h) = Some res1" and
  a4:"(x64_encodes2 xs) = Some res2"
shows "res = res1@res2"
 (* using x64_encodes1_induct x64_encodes2_def apply(cases "(x64_encodes1 xs)",simp_all*)
proof-
  have "\<exists>result. result = (x64_encodes1 xs)" by blast
  then obtain result where b0:"result = (x64_encodes1 xs)" by auto
  hence b1:"res2 = flat (the result)" using x64_encodes2_def a4 by(cases "x64_encodes1 xs",simp_all)
  hence "\<exists> res2'. result = Some res2'" using a4 
    using b0 option.collapse x64_encodes2_def by fastforce
  then obtain res2' where b2:"result = Some res2'" by auto
  hence b3:"res2 = flat res2'" using b1 by simp
  hence "\<exists> res'. res' = res1#res2'" by simp
  then obtain res' where b4:"res' = res1#res2'" by auto
  have "flat res' = res" using b4 b2 a1 a2 a3 b0 x64_encodes2_def by auto
  thus ?thesis by (simp add: b4 b3)
qed

(*


fun x64_encodes_func :: "instruction list \<Rightarrow> x64_bin option" where
"x64_encodes_func [] = None"|
"x64_encodes_func (h#t) = (let ins' = x64_encode h in 
                        (case ins' of None \<Rightarrow> None |
                                      Some v \<Rightarrow> Some (v @ the (x64_encodes_func t))))"
definition x64_encodes_func_suffix:: "instruction list \<Rightarrow> x64_bin option" where
"x64_encodes_func_suffix xs = (let l = x64_encodes_func xs in (if l = None then None else Some (butlast(the l))))"


value "x64_encodes_func [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_encodes_func_suffix [Pmovq_rr src dst,Pmovq_rr src dst]"

lemma "x64_encodes_suffix xs = x64_encodes_func_suffix xs"
  apply(unfold x64_encodes_suffix_def x64_encodes_func_suffix_def Let_def x64_encodes_def)
  apply(split if_splits,simp_all)
  sorry

*)
value "x64_encode (Pmovq_rr src dst)"
value "x64_encodes [Pmovq_rr src dst, Pmovq_rr src dst]"
value "x64_encodes1 [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_encodes_suffix [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_encodes2 [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_encodes_suffix []"
value "x64_encodes2 []"


end