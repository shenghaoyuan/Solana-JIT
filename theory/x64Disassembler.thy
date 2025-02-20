theory x64Disassembler
imports
  Main
  rBPFCommType
  x64Syntax
  x64Assembler
begin

definition x64_decode :: "nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) option" where
"x64_decode pc l_bin = (

  let h = l_bin!pc in
  if h = 0xc3 then Some (1, Pret)
  else if unsigned_bitfield_extract_u8 4 4 h \<noteq> 0b0100 then  \<comment> \<open> h is not rex  \<close>
      \<comment> \<open> R1 [opcode] \<close>
      \<comment> \<open> P2885 `PUSH: qwordregister (alternate encoding)`   -> ` 0100 W00BS : 0101 0 reg64` \<close>
      if unsigned_bitfield_extract_u8 3 5 h = 0b01010 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 h in
        let dst  = bitfield_insert_u8 3 1 reg2 0 in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (1, Ppushl_r dst))
      \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
      else if unsigned_bitfield_extract_u8 3 5 h = 0b01011 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 h in
        let dst  = bitfield_insert_u8 3 1 reg2 0 in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          Some (1, Ppopl dst))
      else None
  else 
    let w = unsigned_bitfield_extract_u8 3 1 h in
    let r = unsigned_bitfield_extract_u8 2 1 h in
    let x = unsigned_bitfield_extract_u8 1 1 h in
    let b = unsigned_bitfield_extract_u8 0 1 h in
    let op = l_bin!(pc+1) in
    if unsigned_bitfield_extract_u8 3 5 op = 0b01010 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 op in
        let dst  = bitfield_insert_u8 3 1 reg2 b in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          if w = 0 \<and> r = 0 \<and> x = 0 then
            Some (2, Ppushl_r dst)
          else None)
      \<comment> \<open> P2885 `POP: qwordregister (alternate encoding)`   -> ` 0100 W00B : 0101 1 reg64 ` \<close>
    else if unsigned_bitfield_extract_u8 3 5 op = 0b01011 then
        let reg2 = unsigned_bitfield_extract_u8 0 3 op in
        let dst  = bitfield_insert_u8 3 1 reg2 b in
        case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
          if w = 0 \<and> r = 0 \<and> x = 0 then
            Some (2, Ppopl dst)
          else None)
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
      if op = 0x01 then 
           if modrm = 0b11 then
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then 
                  Some (3, Paddq_rr dst src) \<comment> \<open> 0b01001000\<close>
                else None))
              else None
      else if op = 0xf7 then 
           if modrm = 0b11 \<and> reg1 = 0b100 then 
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
              if w = 1 \<and> r = 0 \<and> x = 0 then 
                Some (3, Pmulq_r dst) 
              else None)
           else None
      else if op = 0x89 then
            if modrm = 0b11 then 
            \<comment> \<open> P2882 `MOV register1 to register2` -> `0100 WR0B : 1000 100w : 11 reg1 reg2` \<close>
            \<comment> \<open> P2882 `MOV qwordregister1 to qwordregister2` -> `0100 1R0B : 1000 1001 : 11 reg1 reg2` \<close>
              case ireg_of_u8 src of None \<Rightarrow> None | Some src \<Rightarrow> (
              case ireg_of_u8 dst of None \<Rightarrow> None | Some dst \<Rightarrow> (
                if w = 1 \<and> x = 0 then   \<comment> \<open> rex should be `W=1` and `X=0`\<close> 
                  Some (3, Pmovq_rr dst src) 
                else None)) 
            else None
      else None)"


value "x64_decode 0 [0b01001000,0b00000001,0b11011000,0xc3]"


fun x64_decodes_aux ::  "nat \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> (nat * instruction) list option" where
"x64_decodes_aux 0 _ _ = Some []" |
"x64_decodes_aux (Suc num) pc xs = ( let ins' = x64_decode pc xs in (case ins' of 
                                        None \<Rightarrow> None |
                                        Some (len, v) \<Rightarrow>  
                                          (case x64_decodes_aux num pc (drop len xs) of
                                            None \<Rightarrow> None |
                                            Some res \<Rightarrow> Some ((len, v)#res))))"

lemma x64_decodes_aux_equiv:
  "Some res = x64_decode pc ins \<Longrightarrow>
  Some resn = x64_decodes_aux 1 pc ins \<Longrightarrow>
  [res] = resn"
  apply(cases "x64_decode pc ins",simp_all)
  (*apply(split if_splits,simp_all)*)
  done

lemma x64_decodes_aux_induct_aux1:"
  x64_decodes_aux (Suc n) pc xs = Some res \<Longrightarrow>
  x64_decode pc xs = Some res1 \<Longrightarrow>
  len = (fst res1) \<Longrightarrow>
  x64_decodes_aux n pc (drop len xs) = Some res2 \<Longrightarrow>
  res = res1#res2"
  apply(induction n arbitrary: pc xs res res1 len res2)
   apply simp
  subgoal for n pc xs res res1 len res2 
    by (metis (mono_tags, lifting) old.prod.case option.inject option.simps(5) prod.collapse x64_decodes_aux.simps(2))
  done

lemma x64_decodes_aux_induct_aux2:
  "x64_decodes_aux (Suc n) pc xs = Some res \<Longrightarrow> 
  x64_decode pc xs = Some res1 \<Longrightarrow>
  len = (fst res1) \<Longrightarrow>
  x64_decodes_aux n pc (drop len xs) \<noteq> None"
  apply(cases "x64_decodes_aux n pc (drop len xs)",simp_all)
  apply(cases "res1",simp_all)
  done

lemma x64_decodes_aux_induct2:
  assumes a0:"x64_decodes_aux (Suc n) pc xs = Some res" and
  a1:"x64_decode pc xs = Some res1" and
  a2:"len = (fst res1)" 
shows "\<exists> res2. x64_decodes_aux n pc (drop len xs) = Some res2 \<and> res = res1#res2"
  using x64_decodes_aux_induct_aux2 a0 a1 a2 x64_decodes_aux_induct_aux1 by fast

value "x64_decodes_aux 2 0 [0xc3,0xc2,0b01001000,0b00000001,0b11011000]"

value "x64_decodes_aux 2 0 [0xc3,0b01001000,0b00000001,0b11011000]"

value "x64_decodes_aux 1 1 [0xc3,0b01001000,0b00000001,0b11011000]"

value "x64_decodes_aux 0 1 [0xc3,0b01001000,0b00000001,0b11011000]"

value "x64_decodes_aux 5 1 [0xc3,0b01001000,0b00000001,0b11011000]"


end

          