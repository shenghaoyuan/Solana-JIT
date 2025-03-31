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
  \<comment> \<open> P2891 `SUB qwordregister1 from qwordregister2` -> `0100 1R0B : 0010 1001 : 11 reg1 reg2` \<close>
  Psubq_rr rd r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x29 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      [ rex, op, rop ] |
    \<comment> \<open> P2884 `OR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0000 1001 : 11 reg1 reg2` \<close>
  Porq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x09 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      [ rex, op, rop] |
   \<comment> \<open> P2876 `AND qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0010 0001 : 11 reg1 reg2` \<close>
  Pandq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x21 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      [ rex, op, rop] |
   \<comment> \<open> P2893 `XOR qwordregister1 to qwordregister2` -> ` 0100 1R0B : 0011 0001 : 11 reg1 reg2` \<close>
  Pxorq_rr rd r1  \<Rightarrow> 
     let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `1R0B` \<close>
      True \<comment> \<open> W \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0x31 in
    let (rop::u8) = construct_modsib_to_u8 0b11 (u8_of_ireg r1) (u8_of_ireg rd) in
      [ rex, op, rop] |
  Pret \<Rightarrow>
    [0xc3] |
  \<comment> \<open> P2884 `MUL RAX with qwordregister (to RDX:RAX)` -> ` 0100 100B : 1111 0111 : 11 100 qowrdreg` 
  Pmulq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b100 (u8_of_ireg r1) in
      [ rex, op, rop] |\<close>
  Pimulq_r r1 \<Rightarrow>
    let (rex:: u8) = (construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg r1) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xf7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b101 (u8_of_ireg r1) in
      [ rex, op, rop] |
   \<comment> \<open> P2882 `MOV immediate64 to qwordregister (alternate encoding)` -> `0100 100B 1011 1reg : imm64` \<close>
  Pmovq_ri rd n \<Rightarrow>
    let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = bitfield_insert_u8 0 3 0xb8 (u8_of_ireg rd) in
       ([rex, op] @ u8_list_of_u64 n)|
  \<comment> \<open> P2882 `MOV immediate to register` -> `0100 100B : 1100 0111 : 11 000 reg : imm` \<close>
  Pmovl_ri rd n \<Rightarrow>
    let (rex::u8) = ( construct_rex_to_u8  \<comment> \<open> `100B` \<close>
      True \<comment> \<open> W \<close>
      False \<comment> \<open> R \<close>
      False \<comment> \<open> X \<close>
      (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
      ) in
    let (op:: u8) = 0xc7 in
    let (rop::u8) = construct_modsib_to_u8 0b11 0b000 (u8_of_ireg rd) in
      if rex = 0x40 then
        [op, rop] @ (u8_list_of_u32 n)
      else
        [rex, op, rop] @ (u8_list_of_u32 n) |
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
   \<comment> \<open> P2882 ` MOV: memory64 to qwordregister` ->  `0100 1RXB 1000 1001 : mod qwordreg r/m` \<close>
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
            ([rex, op, rop, sib] @ (u8_list_of_u32 dis))) |
 \<comment> \<open> P2882 ` MOV: qwordregister to memory64` ->  `0100 1RXB : 1000 1011 : mod qwordreg r/m`\<close>
  Pmov_rm rd a c \<Rightarrow>( 
    case a of Addrmode (Some rb) None dis \<Rightarrow> 
      let (rex::u8) =  construct_rex_to_u8 \<comment> \<open> WRXB \<close>
        (c = M64) \<comment> \<open> W \<close>
        (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
        False \<comment> \<open> X \<close>
        (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close> in  
      if dis \<le> 127 \<or> dis \<ge> -128 then   \<comment> \<open> displacement8 : mod 01\<close>
        let (dis::u8) = scast dis in
        let (rop::u8) = construct_modsib_to_u8 0b01 (u8_of_ireg rd) (u8_of_ireg rb) in
        if rex = 0x40 then    
          case c of 
            M32 \<Rightarrow> [0x8b, rop, dis] 
        else 
          case c of 
            M32 \<Rightarrow> [rex, 0x8b, rop, dis] |
            M64 \<Rightarrow> [rex, 0x8b, rop, dis] 
        else
          let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg rd) (u8_of_ireg rb) in
          if rex = 0x40 then    
            case c of 
              M32 \<Rightarrow> ([0x8b, rop] @ (u8_list_of_u32 dis))
          else 
            (case c of 
              M32 \<Rightarrow> ([rex, 0x8b, rop] @ (u8_list_of_u32 dis)) |
              M64 \<Rightarrow> ([rex, 0x8b, rop] @ (u8_list_of_u32 dis)) )
    |  Addrmode (Some rb) (Some (ri,scale)) dis \<Rightarrow>(
                let (rex::u8) = ( construct_rex_to_u8 \<comment> \<open> 1RXB \<close>
                  True \<comment> \<open> W \<close>
                  (and (u8_of_ireg rd) 0b1000 \<noteq> 0) \<comment> \<open> R \<close>
                  (and (u8_of_ireg ri) 0b1000 \<noteq> 0) \<comment> \<open> X \<close>
                  (and (u8_of_ireg rb) 0b1000 \<noteq> 0) \<comment> \<open> B \<close>
                ) in
                  let (op:: u8) = 0x8b in
                  let (rop::u8) = construct_modsib_to_u8 0b10 (u8_of_ireg rd) 0b100 in
                  let (sib::u8) = construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
                  ([rex, op, rop, sib] @ (u8_list_of_u32 dis)))) |
  \<comment> \<open> P2878 `CALL: direct`   -> `1110 1000 : displacement32` \<close>
  Pcall_i d  \<Rightarrow>
      ([0xe8] @ (u8_list_of_u32 d))
)"
                              
fun list_in_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_in_list [] _ _ = True" |
"list_in_list (h#t) n l = (h = l!n \<and> list_in_list t (Suc n) l)"

value "x64_encode (Pjcc Cond_e 3)"

value "unsigned_bitfield_extract_u8 0 4 0x84"

end