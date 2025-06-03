theory JITFix_def
imports JITFlattern
begin

fun find_target_pc_in_l_pc2 :: "((int\<times>nat) list) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int option" where
"find_target_pc_in_l_pc2 [] _ _ = None" |
"find_target_pc_in_l_pc2 (x#xs) xpc num = (
  if fst x = xpc then Some num
  else find_target_pc_in_l_pc2 xs xpc (num+1)
)"


fun find_num_in_l_pc :: "((int\<times>nat) list) \<Rightarrow> int \<Rightarrow> nat option" where
"find_num_in_l_pc [] _ = None" |
"find_num_in_l_pc ((x,y)#xs) xpc = (
  if x = xpc then Some y
  else find_num_in_l_pc xs xpc 
)"


value "find_target_pc_in_l_pc2 [(0,1),(1,2),(3,3)] 3 0"

value "find_num_in_l_pc [(0,1),(1,2),(3,3)] 3"

(*definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"flat_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
    let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 ; v2 = find_num_in_l_pc l_pc (int xpc) in 
      case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
        (case v2 of None \<Rightarrow> Stuck | Some num \<Rightarrow>
          (case x64_decode xpc l_bin of Some(sz, Pcall_i d) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump pc of 
              None \<Rightarrow> Stuck |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (of_int pc+1) ss in
                  (case ss' of None \<Rightarrow> Stuck | 
                  Some ra \<Rightarrow> (Next (nat (fst (l_pc!(unat npc)))) rs' m ra))))  |
              Some(_,Pret) \<Rightarrow>
                  let (pc', ss', caller,fp) = update_stack2 ss in 
                  let rs' = restore_x64_caller rs caller fp in Next (nat(fst(l_pc!(unat pc')))) rs' m ss' |
    _ \<Rightarrow> (x64_sem num l_bin (Next xpc rs m ss))
       
)))))"*)

(*
definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
    let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 ; v2 = find_num_in_l_pc l_pc (int xpc) in 
      case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
        (case v2 of None \<Rightarrow> Stuck | Some num \<Rightarrow>
          (case x64_decode xpc l_bin of Some(sz, Pcall_i d) \<Rightarrow>
            (case find_target_pc_in_l_pc l_jump pc of 
              None \<Rightarrow> Stuck |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (of_nat xpc) ss in
                  (case ss' of None \<Rightarrow> Stuck | 
                  Some ra \<Rightarrow> (Next (nat (fst (l_pc!(unat npc)))) rs' m ra))))  |
                  Some(_, Pcmpq_rr src dst) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
                          \<comment>\<open> case: BPF JMP \<close>
                          (case x64_sem num l_bin (Next xpc rs m ss) of
                          Stuck \<Rightarrow> Stuck | \<comment>\<open> if one step error, stop, it should be impossible \<close>
                          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
                            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
                              (case find_target_pc_in_l_pc l_jump pc of
                              None \<Rightarrow> Stuck |
                              Some npc \<Rightarrow>
                                (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
                            else \<comment>\<open> donot JUMP \<close>
                              (Next xpc1 rs1 m1 ss1)
                          )) |
              Some(_,Pret) \<Rightarrow>
                  let (xpc', ss', caller,fp) = update_stack2 ss in 
                  let rs' = restore_x64_caller rs caller fp in Next (unat xpc') rs' m ss' |
    _ \<Rightarrow> (x64_sem num l_bin (Next xpc rs m ss))
       
)))))"
*)

(*
definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
          (case x64_decode xpc l_bin of 
                  Some(sz, Pcall_i imm) \<Rightarrow>
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_int(fst (l_pc!(unat npc))))) sz xpc rs m ss)) |
                  Some(sz, Pjcc cond d) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_int (fst (l_pc!(unat npc)))-(of_nat (xpc+1)))) sz xpc rs m ss))) |
                  Some(sz, Pret) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case (exec_instr Pret sz xpc rs m ss) of Stuck \<Rightarrow> Stuck | 
                                          Next xpc1 rs1 m1 ss1 \<Rightarrow> let v2 = find_target_pc_in_l_pc3 l_jump pc in
                                            (case v2 of None \<Rightarrow> Stuck | Some pc'\<Rightarrow>
                                              (if xpc1 \<noteq> nat (fst (l_pc!(nat pc')))+1 then Stuck else Next xpc1 rs1 m1 ss1 )))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc rs m ss) |
                  _ \<Rightarrow> Stuck 
))))"*)


(*
definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
          (case x64_decode xpc l_bin of 
                  Some(sz, Pcall_i imm) \<Rightarrow>
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_int(fst (l_pc!(unat npc))))) sz xpc rs m ss)) |
                  Some(sz, Pjcc cond d) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_int (fst (l_pc!(unat npc)))-(of_nat (xpc+1)))) sz xpc rs m ss))) |
                  Some(sz, Pret) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case (exec_instr Pret sz xpc rs m ss) of Stuck \<Rightarrow> Stuck | 
                                          Next xpc1 rs1 m1 ss1 \<Rightarrow> let v2 = find_target_pc_in_l_pc3 l_jump pc in
                                            (case v2 of None \<Rightarrow> Stuck | Some pc'\<Rightarrow>
                                              (if xpc1 \<noteq> nat (fst (l_pc!(nat pc')))+1 then Stuck else Next xpc1 rs1 m1 ss1 )))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc rs m ss) |
                  _ \<Rightarrow> Stuck 
))))"
*)

definition fix_bpf_one_step :: "flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_one_step lp xst = (
  let (l_bin,l_pc,l_jump) = lp in  
    (case xst of
    Stuck \<Rightarrow> Stuck |
    Next xpc rs m ss \<Rightarrow> (
          (case x64_decode xpc l_bin of 
                  Some(sz, Pcall_i imm) \<Rightarrow>
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_int(fst (l_pc!(unat npc))))) sz xpc rs m ss)) |
                  Some(sz, Pjcc cond d) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (int xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_int (fst (l_pc!(unat npc)))-(of_nat (xpc+1)))) sz xpc rs m ss))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc rs m ss) |
                  _ \<Rightarrow> Stuck 
))))"




fun fix_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_sem 0 _ xst = xst" |
"fix_bpf_sem (Suc n) lt xst = (
   let pair = fix_bpf_one_step lt xst in
    fix_bpf_sem n lt pair
)"

(*
definition match_state2::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state2 fxst xxst \<equiv> 
  fxst = xxst \<and> (fxst \<noteq> Stuck \<or> xxst \<noteq> Stuck)"
*)

definition match_state2::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state2 fxst xxst \<equiv> 
  (case fxst of (Next xpc xrs xm xss) \<Rightarrow>
    (case xxst of (Next xpc1 xrs1 xm1 xss1) \<Rightarrow> 
    xpc = xpc1 \<and> xrs = xrs1 \<and> match_mem xm xm1 \<and> xss = xss1 |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"


end