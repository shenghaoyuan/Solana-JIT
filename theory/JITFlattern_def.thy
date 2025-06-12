theory JITFlattern_def
  imports x64Semantics
begin
type_synonym flat_bpf_prog = "x64_bin \<times> (nat \<times> nat) list \<times> ((int\<times>u64) list)"

definition update_l_jump::"(nat \<times> u64 \<times> x64_bin) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (int\<times>u64) list \<Rightarrow> (int\<times>u64) list" where
"update_l_jump x l_pc l_jump \<equiv> let (num,off,l_bin0) = x in 
  case x64_decode 0 l_bin0 of 
  Some(_, Pcall_i _) \<Rightarrow> l_jump@ [(of_nat (length l_pc), off)]|
  Some(_, Pcmpq_rr src dst) \<Rightarrow> l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) +  off)]|
  _ \<Rightarrow> l_jump"

fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf (x#xs) k = (
  let (num,off,l_bin0) = x in
  let (l_bin,l_pc,l_jump) = k in
  let curr_pc = of_nat (length l_bin) in 
  let l_jump' = update_l_jump (num,off,l_bin0) l_pc l_jump in
      jitflat_bpf xs (
        l_bin@l_bin0,
        l_pc@[(curr_pc,num)],
        l_jump')
)"

definition init_second_layer::"x64_bin \<times> (nat \<times> nat) list \<times> ((int\<times>u64) list)" where
"init_second_layer \<equiv> ([],[],[])"

(*fun well_formed_prog_aux::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
  "well_formed_prog_aux [] = True" |
  "well_formed_prog_aux (x#xs) = (let (num,off,l) = x in 
    num > 0 \<and> l \<noteq> [] \<and> well_formed_prog_aux xs)"


value "well_formed_prog_aux [(1,0,[3])]"
  
definition well_formed_prog::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
"well_formed_prog lt \<equiv> well_formed_prog_aux lt \<and> length lt \<le> 100000 \<and> lt \<noteq> []"

value "well_formed_prog [(1,0,[3])]"*)


fun wf_x64_bin :: "nat \<Rightarrow> x64_bin \<Rightarrow> nat \<Rightarrow> ((nat * nat) list) option" where
"wf_x64_bin 0 _ _ = None" |
"wf_x64_bin (Suc n) l_bin pc = (
  case x64_decode pc l_bin of
  None \<Rightarrow> None |
  Some (sz, ins) \<Rightarrow> (
    case wf_x64_bin n l_bin (pc+sz) of
    None \<Rightarrow> None |
    Some l \<Rightarrow> Some ((pc, sz)#l)
))"

fun wf_pc_sz :: "(nat * nat) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"wf_pc_sz [] _ _ = False" |
"wf_pc_sz (x#xs) pc sz = ((fst x = pc \<and> snd x =sz) \<or> wf_pc_sz xs pc sz)"


value "int (1::nat)"
value "nat (1::int)"

definition well_formed_prog1::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
"well_formed_prog1 lt \<equiv> (\<forall> id. id < length lt \<and> id \<ge>0 \<longrightarrow> fst(lt!id) > 0)"

definition well_formed_prog::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
"well_formed_prog lt \<equiv> ( lt \<noteq> [] \<and> 
  (\<forall> id. id < length lt \<and> id \<ge>0 \<longrightarrow> snd(snd (lt!id)) \<noteq> [] \<and> fst(lt!id) >0))"

fun find_target_pc_in_l_pc :: "((int\<times>u64) list) \<Rightarrow> nat \<Rightarrow> u64 option" where
"find_target_pc_in_l_pc [] _ = None" |
"find_target_pc_in_l_pc ((x, y)#xs) pc = (
  if x = of_nat pc then Some y
  else find_target_pc_in_l_pc xs pc
)"


fun find_target_pc_in_l_pc3 :: "((int\<times>u64) list) \<Rightarrow> nat \<Rightarrow> int option" where
"find_target_pc_in_l_pc3 [] _ = None" |
"find_target_pc_in_l_pc3 ((x, y)#xs) pc = (
  if y = of_nat pc then Some x
  else find_target_pc_in_l_pc3 xs pc
)"


(*value "((of_int (1::int))::nat)"*)

(*if unat pc \<ge> length lp \<or> unat pc < 0 then (pc,Stuck) else *)
(*definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    (case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc rs m ss \<Rightarrow> (
    if unat pc \<ge> length l_pc \<or> unat pc < 0 then (pc,Stuck) else 
    let num = snd (l_pc!(unat pc)) in 
    let old_xpc = nat (fst (l_pc!(unat pc))) in 
      if xpc \<noteq> old_xpc then (pc, Stuck) else 
        case x64_decode xpc l_bin of Some(_, Pcall_i _) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> (
                let xst_temp = x64_sem 1 l_bin xst in 
                  (case xst_temp of Stuck \<Rightarrow> (pc, Stuck) | 
                                    Next xpc' rs' m' ss' \<Rightarrow> (npc, (Next (nat (fst (l_pc!(unat npc)))) rs' m' ss'))) )) |
        Some(sz, Pcmpq_rr src dst) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_decode (xpc+sz) l_bin of Some (sz2,Pjcc _ _) \<Rightarrow>
            (case x64_sem num l_bin (Next xpc rs m ss) of
            Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
            Next xpc1 rs1 m1 ss1 \<Rightarrow> (
              case find_target_pc_in_l_pc l_jump (uint pc) of
                None \<Rightarrow> (pc, Stuck) |
                Some npc \<Rightarrow>
              if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
                ((npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
              else \<comment>\<open> donot JUMP \<close>
                (pc+1, (Next (xpc1+sz2) rs1 m1 ss1))
            ))|
            _ \<Rightarrow> (pc, Stuck)) |
        Some(sz,Pret_anchor) \<Rightarrow>
          (case x64_decode (xpc+sz) l_bin of Some (sz2,Pret) \<Rightarrow>
          let (pc', ss', caller,fp) = update_stack2 ss in 
          if find_target_pc_in_l_pc3 l_jump (uint pc) \<noteq> Some (uint pc') then (pc,Stuck) else
          let rs' = restore_x64_caller rs caller fp in (pc', Next (nat (fst (l_pc!(unat pc')))+1) rs' m ss') |
          _ \<Rightarrow> (pc,Stuck)) |
          \<comment>\<open> case: NOT BPF JMP \<close>
        _ \<Rightarrow>
          (pc+1, x64_sem num l_bin (Next xpc rs m ss))
)))"
*)

definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    (case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc rs m ss \<Rightarrow> (
    if unat pc \<ge> length l_pc \<or> unat pc < 0 then (pc,Stuck) else 
    let num = snd (l_pc!(unat pc)) in 
    let old_xpc = fst (l_pc!(unat pc)) in 
      if xpc \<noteq> old_xpc then (pc, Stuck) else 
        case x64_decode xpc l_bin of Some(sz, Pcall_i imm) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump (unat pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> (
                let xst_temp = exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc rs m ss in 
                  (case xst_temp of Stuck \<Rightarrow> (pc, Stuck) | 
                                    Next xpc' rs' m' ss' \<Rightarrow> (npc, (Next xpc' rs' m' ss'))))) |
        Some(sz,Pcmpq_rr src dst) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_decode (xpc+sz) l_bin of Some (sz2,Pjcc _ _) \<Rightarrow>
            (case x64_sem num l_bin (Next xpc rs m ss) of
            Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
            Next xpc1 rs1 m1 ss1 \<Rightarrow> (
              case find_target_pc_in_l_pc l_jump (unat pc) of
                None \<Rightarrow> (pc, Stuck) |
                Some npc \<Rightarrow>
              if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
                ((npc, (Next (fst (l_pc!(unat npc))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
              else \<comment>\<open> donot JUMP \<close>
                (pc+1, (Next (xpc1+sz2) rs1 m1 ss1))
            ))|
            _ \<Rightarrow> (pc, Stuck)) |
        Some(sz,Pret_anchor) \<Rightarrow>
          (case x64_decode (xpc+sz) l_bin of Some (sz2,Pret) \<Rightarrow>
          let (pc', ss', caller,fp) = update_stack2 ss in 
          if find_target_pc_in_l_pc3 l_jump (unat pc) \<noteq> Some (uint pc') then (pc,Stuck) else
          let rs' = restore_x64_caller rs caller fp in 
          let xst_temp = exec_instr Pret sz2 (xpc+sz) rs' m ss' in 
          (case xst_temp of Stuck \<Rightarrow> (pc,Stuck)| Next xpc1 rs1 m1 ss1 \<Rightarrow> 
            (if xpc1 = (fst (l_pc! (unat pc')))+1 then (pc',Next xpc1 rs1 m1 ss1) else (pc,Stuck) ))|
          _ \<Rightarrow> (pc,Stuck)) |
          \<comment>\<open> case: NOT BPF JMP \<close>
        _ \<Rightarrow>
          (pc+1, x64_sem num l_bin (Next xpc rs m ss))
)))"


fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ (pc,st) = (pc,st)" |
"flat_bpf_sem (Suc n) lt (pc, xst) = (
   let pair = flat_bpf_one_step lt (pc, xst) in
    flat_bpf_sem n lt pair
)"

definition match_mem :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
"match_mem bm xm = (
  \<forall> addr v. bm 0 addr = Some v \<longrightarrow> xm 0 addr = Some v)"

definition match_state1::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state1 fxst xxst \<equiv> 
  (case fxst of (Next xst xrs xm xss) \<Rightarrow>
    (case xxst of (Next xst1 xrs1 xm1 xss1) \<Rightarrow> 
     xrs = xrs1 \<and> match_mem xm xm1 \<and> xss = xss1 |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"

definition match_state::"hybrid_state \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "match_state fxst xxst \<equiv> 
  (case fxst of (pc,Next xpc xrs xm xss) \<Rightarrow>
    (case xxst of (pc1,Next xpc1 xrs1 xm1 xss1) \<Rightarrow> 
      pc = pc1 \<and> match_state1 (Next xpc xrs xm xss) (Next xpc1 xrs1 xm1 xss1) |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"

end