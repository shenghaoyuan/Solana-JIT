theory x64Assembler
  imports Main rBPFCommType rBPFSyntax x64Syntax x86CommType

begin

definition x64_encode :: "instruction \<Rightarrow> x64_bin" where
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
     [ rex, op, rop ] |
  Pret \<Rightarrow>
    [0xc3] |
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
      [ rex, op, rop] |
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
       [ rex, op, rop ] |
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
         [op]
      else 
        [rex, op] |
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
         [op]
      else 
          [rex, op] |
   \<comment> \<open> P2881 `JMP: direct` -> `1110 1001 : displacement32` \<close>
  Pjcc t d \<Rightarrow>
    let (ex:: u8) = 0x0f in
    let (op:: u8) = bitfield_insert_u8 0 4 0x80 (u8_of_cond t) in
    [ex, op] @ (u8_list_of_u32 (ucast d)) |
  Pcmpq_rr r1 r2 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True  \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r2) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x39 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg r2) in
      [rex, op, rop] |
  Pxchgq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op::u8) = 0x87 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      [rex, op, rop] |
    \<comment> \<open> P2890 `SHR qwrodregister by CL`   -> ` 0100 100B 1101 001w : 11 101 reg ` \<close>
  Pshrq_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg rd) in
      [ rex, op, rop ] |
   \<comment> \<open> P2888 `SAR qwordregister by CL`     -> ` 0100 100B 1101 001w : 11 111 reg ` \<close>
  Psarq_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b111 (u8_of_ireg rd) in
      [ rex, op, rop ] |
   \<comment> \<open> P2889 `SHL qwordregister by CL`              -> ` 0100 100B 1101 001w : 11 100 reg ` \<close>
  Pshlq_r rd  \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xd3 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg rd) in
      [ rex, op, rop ] |
   \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
  Pmov_mr  a r1 c \<Rightarrow> (
    case a of Addrmode (Some rb) None dis \<Rightarrow> 
      let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> WRXB \<close>
        (c = M64) \<comment> \<open> W \<close>
        (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
        ) in
      if dis \<le> 127 \<or> dis \<ge> -128  then   \<comment> \<open> displacement8 : mod 01 \<close>
        let (dis::u8) = scast dis in
        let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg r1) (u8_of_ireg rb) in
        if rex = 0x40 then(
          case c of 
            M8  \<Rightarrow> [0x88, rop, dis] |
            M16 \<Rightarrow> [0x66, 0x89, rop, dis] |
            M32 \<Rightarrow> [0x89, rop, dis] )
        else (
          case c of 
            M8  \<Rightarrow> [rex, 0x88, rop, dis] |
            M16 \<Rightarrow> [0x66,rex, 0x89, rop, dis] |
            M32 \<Rightarrow> [rex, 0x89, rop, dis] |
            M64 \<Rightarrow> [rex, 0x89, rop, dis])
      else  \<comment> \<open> displacement8 : mod 10, (and (u8_of_ireg rb) 0b0111 \<noteq> 0b100) \<close>       
        let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg r1) (u8_of_ireg rb) in
        if rex = 0x40 then(
          case c of 
            M32 \<Rightarrow> ([0x89, rop] @ (u8_list_of_u32 dis)))
        else (
          case c of 
            M32 \<Rightarrow> ([rex, 0x89, rop] @ (u8_list_of_u32 dis)) |
            M64 \<Rightarrow> ([rex, 0x89, rop] @ (u8_list_of_u32 dis)))
    |  Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>
          \<comment> \<open> ! scale > 3 | c \<noteq> M64 then None\<close>
          let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> 1RXB \<close>
            True \<comment> \<open> W \<close>
            (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
            (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
            (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
            ) in
        let (op:: u8) = 0x89 in
        let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg r1) 0b100 in
        let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
            ([rex, op, rop, sib] @ (u8_list_of_u32 dis))
))"

(*Pjmp d \<Rightarrow>
    let (op:: u8) = 0xe9 in
      [op] @ (u8_list_of_u32 (ucast d)))*)
                                         
fun list_in_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_in_list [] _ _ = True" |
"list_in_list (h#t) n l = (h = l!n \<and> list_in_list t (Suc n) l)"


(*fun x64_encode :: "instruction \<Rightarrow> (nat \<times> x64_bin) option" where
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
      Some (3, [ rex, op, rop ]) |
  Pret \<Rightarrow>
    Some (1,[0xc3]) |
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
      Some (3,[ rex, op, rop]) |
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
      Some (3,[ rex, op, rop ]) |
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
*)

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

primrec flat :: "'a list list => 'a list" where
  "flat [] = []" |
  "flat (x # xs) = x @ flat xs"


(*primrec flat2 :: "'a list list option=> 'a list option" where
  "flat2 None = None" |
  "flat2 res = x @ flat xs"*)

fun x64_encodes1 :: "instruction list \<Rightarrow> x64_bin list" where
  "x64_encodes1 [] = []" |
  "x64_encodes1 (h#xs) = ((x64_encode h)# (x64_encodes1 xs))"

definition x64_encodes2 :: "instruction list \<Rightarrow> x64_bin" where
"x64_encodes2 xs = (let x = (x64_encodes1 xs) in (flat x))"

lemma x64_encodes1_induct:"x64_encodes1 insns = res \<Longrightarrow>
  insns = (h#xs) \<Longrightarrow>
  (x64_encode h) = res1 \<Longrightarrow> 
  (x64_encodes1 xs) =res2 \<Longrightarrow>
  res = res1#res2"
  apply(induction insns arbitrary: res h xs res1 res2)
   apply simp
  subgoal for a insns res h xs res1 res2 by simp
  done

lemma x64_encodes2_equiv:"res = x64_encode ins \<Longrightarrow>
  resn = x64_encodes2 [ins] \<Longrightarrow>
  res = resn"
  using x64_encodes2_def by (metis (mono_tags) append.right_neutral flat.simps(1) flat.simps(2) x64_encodes1.simps(1) x64_encodes1.simps(2))

lemma x64_encodes2_induct:
  assumes 
  a1:"x64_encodes2 insns = res" and
  a2:"insns = (h#xs)" and
  a3:"(x64_encode h) = res1" and
  a4:"(x64_encodes2 xs) = res2"
shows "res = res1@res2"
proof-
  have "\<exists>res2'. res2' = (x64_encodes1 xs)" by blast
  then obtain res2' where b0:"res2' = (x64_encodes1 xs)" by auto
  hence b1:"res2 = flat res2'" using x64_encodes2_def a4 by simp
  hence b3:"res2 = flat res2'" using b1 by simp
  hence "\<exists> res'. res' = res1#res2'" by simp
  then obtain res' where b4:"res' = res1#res2'" by auto
  have "flat res' = res" using b4 a1 a2 a3 b0 x64_encodes2_def by simp
  thus ?thesis by (simp add: b4 b3)
qed


value "x64_encode (Pmovq_rr src dst)"
value "x64_encodes1 [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_encodes2 [Pmovq_rr src dst,Pmovq_rr src dst]"
value "x64_encodes2 []"





end