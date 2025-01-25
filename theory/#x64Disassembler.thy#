theory x64Disassembler
imports
  Main
  rBPFCommType
  x64Syntax
begin

(*
  \<comment> \<open> P2887 `ADD register1 to register2` -> `0100 WR0B : 0000 000w : 11 reg1 reg2` \<close>
            if modrm = 0b11 then (
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Paddq_rr dst src)
                else None
*)
(*definition x64_decode :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode pc l_bin = (
  let h = l_bin!pc in
    if h = 0xc3 then Some (1, Pret)
  else 
  let w = unsigned_bitfield_extract_u8 3 1 h in
  let r = unsigned_bitfield_extract_u8 2 1 h in
  let x = unsigned_bitfield_extract_u8 1 1 h in
  let b = unsigned_bitfield_extract_u8 0 1 h in
  let op = l_bin!(pc+1) in 
  let reg = l_bin!(pc+2) in 
  let modrm = unsigned_bitfield_extract_u8 6 2 reg in
  let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
  let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
  let src   = bitfield_insert_u8 3 1 reg1 r in
  let dst   = bitfield_insert_u8 3 1 reg2 b in
  if op = 0x01 then if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Paddq_rr dst src)
                else None))
  else None
else None)"
*)

definition x64_decode :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode pc l_bin = (
  let h = l_bin!pc in
    if h = 0xc3 then Some (1, Pret)
  else 
  let w = unsigned_bitfield_extract_u8 3 1 h in
  let r = unsigned_bitfield_extract_u8 2 1 h in
  let x = unsigned_bitfield_extract_u8 1 1 h in
  let b = unsigned_bitfield_extract_u8 0 1 h in
  let op = l_bin!(pc+1) in 
  let reg = l_bin!(pc+2) in 
  let modrm = unsigned_bitfield_extract_u8 6 2 reg in
  let reg1  = unsigned_bitfield_extract_u8 3 3 reg in
  let reg2  = unsigned_bitfield_extract_u8 0 3 reg in
  let src   = bitfield_insert_u8 3 1 reg1 r in
  let dst   = bitfield_insert_u8 3 1 reg2 b in
  if op = 0x01 then if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Paddq_rr dst src)
                else None))
  else None
else None)"

value "x64_decode 0 [0b01001000,0b00000001,0b11011000]"

end

          