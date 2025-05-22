theory JITFlattern_def
  imports x64Semantics
begin
type_synonym flat_bpf_prog = "x64_bin \<times> (int \<times> nat) list \<times> ((int\<times>u64) list)"

definition update_l_jump::"(nat \<times> u64 \<times> x64_bin) \<Rightarrow> (int \<times> nat) list \<Rightarrow> (int\<times>u64) list \<Rightarrow> (int\<times>u64) list" where
"update_l_jump x l_pc l_jump \<equiv> let (num,off,l_bin0) = x in 
  if (\<exists> d. x64_decode 0 l_bin0 = Some(5, Pcall_i d)) then l_jump@ [(of_nat (length l_pc), off)]
  else if (\<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst)) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) +  off)]
  else l_jump"

fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
  let curr_pc = of_nat (length l_bin) in 
  let l_jump' = update_l_jump (num,off,l_bin0) l_pc l_jump in
      jitflat_bpf xs (
        l_bin@l_bin0,
        l_pc@[(curr_pc,num)],
        l_jump')
)"

definition init_second_layer::"x64_bin \<times> (int \<times> nat) list \<times> ((int\<times>u64) list)" where
"init_second_layer \<equiv> ([],[],[])"

(*fun well_formed_prog_aux::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
  "well_formed_prog_aux [] = True" |
  "well_formed_prog_aux (x#xs) = (let (num,off,l) = x in 
    num > 0 \<and> l \<noteq> [] \<and> well_formed_prog_aux xs)"


value "well_formed_prog_aux [(1,0,[3])]"
  
definition well_formed_prog::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
"well_formed_prog lt \<equiv> well_formed_prog_aux lt \<and> length lt \<le> 100000 \<and> lt \<noteq> []"

value "well_formed_prog [(1,0,[3])]"*)

value "int (1::nat)"
value "nat (1::int)"

definition well_formed_prog1::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
"well_formed_prog1 lt \<equiv> (\<forall> id. id < length lt \<and> id \<ge>0 \<longrightarrow> fst(lt!id) > 0)"

definition well_formed_prog::"(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> bool" where
"well_formed_prog lt \<equiv> ( lt \<noteq> [] \<and> 
  (\<forall> id. id < length lt \<and> id \<ge>0 \<longrightarrow> snd(snd (lt!id)) \<noteq> [] \<and> fst(lt!id) >0))"

fun find_target_pc_in_l_pc :: "((int\<times>u64) list) \<Rightarrow> int \<Rightarrow> u64 option" where
"find_target_pc_in_l_pc [] _ = None" |
"find_target_pc_in_l_pc ((x, y)#xs) pc = (
  if x = pc then Some y
  else find_target_pc_in_l_pc xs pc
)"

(*value "((of_int (1::int))::nat)"*)

(*if unat pc \<ge> length lp \<or> unat pc < 0 then (pc,Stuck) else *)
definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
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
        if (\<exists> d. x64_decode xpc l_bin = Some(5, Pcall_i d)) then
            (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (pc+1) ss in
                  (case ss' of None \<Rightarrow> (pc, Stuck) | 
                  Some ra \<Rightarrow> (npc, (Next (nat (fst (l_pc!(unat npc)))) rs' m ra)))))
        else if (\<exists> src dst. x64_decode xpc l_bin = Some(3, Pcmpq_rr src dst)) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem num l_bin (Next xpc rs m ss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, (Next xpc1 rs1 m1 ss1))
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc rs m ss))
)))"

fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ (pc,st) = (pc,st)" |
"flat_bpf_sem (Suc n) lt (pc, xst) = (
   let pair = flat_bpf_one_step lt (pc, xst) in
    flat_bpf_sem n lt pair
)"

definition match_state1::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state1 fxst xxst \<equiv> 
  (case fxst of (Next xst xrs xm xss) \<Rightarrow>
    (case xxst of (Next xst1 xrs1 xm1 xss1) \<Rightarrow> 
     xrs = xrs1 \<and> xm = xm1 \<and> xss = xss1 |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"

definition match_state::"hybrid_state \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "match_state fxst xxst \<equiv> 
  (case fxst of (pc,Next xst xrs xm xss) \<Rightarrow>
    (case xxst of (pc1,Next xst1 xrs1 xm1 xss1) \<Rightarrow> 
      pc = pc1 \<and> match_state1 (Next xst1 xrs1 xm1 xss1) (Next xst xrs xm xss)  |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"
(*x64_decode 0 l = x64_decode xpc l
xxst = Next xpc1 xrs1 xm1 xss1 \<Longrightarrow>
   fxst = Next xpc2 xrs2 xm2 xss2 \<Longrightarrow>
xrs1 = xrs2 \<and> xm1 = xm2 \<and> xss1 = xss2*)
end