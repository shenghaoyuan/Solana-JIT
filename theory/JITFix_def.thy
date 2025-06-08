theory JITFix_def
imports JITFlattern
begin

fun find_target_pc_in_l_pc2 :: "((nat\<times>nat) list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
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
                  Some(_, Pjcc cond d) \<Rightarrow> \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
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
                      let v = find_target_pc_in_l_pc2 l_pc xpc 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                      exec_instr (Pcall_i (of_nat(fst (l_pc!(unat npc))))) sz xpc rs m ss)) |
                  Some(sz, Pjcc cond d) \<Rightarrow> 
                      let v = find_target_pc_in_l_pc2 l_pc (xpc-3) 0 in
                      (case v of None \<Rightarrow> Stuck | Some pc \<Rightarrow>
                      (case find_target_pc_in_l_pc l_jump pc of
                        None \<Rightarrow> Stuck |
                        Some npc \<Rightarrow>
                          (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc+1)))) sz xpc rs m ss))) |
                  Some(sz,ins) \<Rightarrow> (exec_instr ins sz xpc rs m ss) |
                  _ \<Rightarrow> Stuck 
))))"




fun fix_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> outcome \<Rightarrow> outcome" where
"fix_bpf_sem 0 _ xst = xst" |
"fix_bpf_sem (Suc n) lt xst = (
   let pair = fix_bpf_one_step lt xst in
    fix_bpf_sem n lt pair
)"


definition match_state2::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state2 fxst xxst \<equiv> 
  fxst = xxst \<and> (fxst \<noteq> Stuck \<or> xxst \<noteq> Stuck)"


(*definition match_state2::"outcome \<Rightarrow> outcome \<Rightarrow> bool" where
  "match_state2 fxst xxst \<equiv> 
  (case fxst of (Next xpc xrs xm xss) \<Rightarrow>
    (case xxst of (Next xpc1 xrs1 xm1 xss1) \<Rightarrow> 
    xpc = xpc1 \<and> xrs = xrs1 \<and> match_mem xm xm1 \<and> xss = xss1 |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"
*)


value "x64_encode (Pcall_i 0x1111)"

value "u8_list_of_i32 0x1111"

value "x64_encode (Pjcc Cond_e 0x00000000)"

value "u8_list_of_i32 0x11110000"

value "u32_of_u8_list [0,0,0,0]"

fun x64_bin_update ::"nat \<Rightarrow> x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
  "x64_bin_update 0 l _ _ = l" |
  "x64_bin_update (Suc n) l pc u8_list =  (let l' = list_update l pc (hd u8_list) in x64_bin_update n l' (pc+1) (tl u8_list))"

value "x64_bin_update 4 [232::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] 1 [17::8 word, 17::8 word, 0::8 word, 0::8 word]"

value "x64_bin_update 4 [15::8 word, 132::8 word, 0::8 word, 0::8 word, 17::8 word, 17::8 word] 2 [0::8 word, 0::8 word, 17::8 word, 17::8 word]"
(*
definition get_updated_l_bin::"(int\<times>u64) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin option"where
  "get_updated_l_bin x l l_pc \<equiv> 
    (let fix_begin_addr = fst (l_pc!(nat(fst x))); 
        (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
        (case x64_decode (nat fix_begin_addr) l of 
              Some(sz, Pcall_i _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+of_nat sz+1)::i32) in 
                                     let u8_list = x64_encode (Pcall_i (ucast offset)) in
                                     Some (x64_bin_update (length u8_list) l (nat fix_begin_addr) u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = nat fix_begin_addr+sz in 
                    (case x64_decode loc l of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"
*)

definition get_updated_l_bin::"(int\<times>u64) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin option"where
  "get_updated_l_bin x l l_pc \<equiv> 
    (let fix_begin_addr = fst (l_pc!(nat(fst x))); 
        (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
        (case x64_decode (nat fix_begin_addr) l of 
              Some(sz, Pcall_i _) \<Rightarrow> let u8_list = x64_encode (Pcall_i (of_int target_begin_addr)) in
                                     Some (x64_bin_update (length u8_list) l (nat fix_begin_addr) u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = nat fix_begin_addr+sz in 
                    (case x64_decode loc l of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"

value "x64_decode 0 [72::8 word, 57::8 word, 195::8 word] "


value "x64_decode 0 [15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] "


value "get_updated_l_bin (0,1) [72::8 word, 57::8 word, 195::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word ,195::8 word] [(0::int, 8::nat), (9::int, 1::nat)]"

value "get_updated_l_bin (0,1) [232::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word ,195::8 word] [(0::int, 1::nat), (6::int, 1::nat)]"

(*input: l_jump x64_bin l_pc*)
fun jitfix :: "((int\<times>u64) list) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin option" where
  "jitfix [] l _  = Some l" |
  "jitfix (x#xs) l l_pc = (if l = [] then None else 
    let res = get_updated_l_bin x l l_pc in case res of None \<Rightarrow> None | 
                                                        Some l' \<Rightarrow> jitfix xs l' l_pc)"

value "x64_encode (Pcmpq_rr RAX RBX)"

value "x64_encode (Pret)"

value "jitflat_bpf [(1, 1, [0x48,0x01,0xD8]),(1, 2, [0x48, 0x39, 0xc3, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8])] init_second_layer"

value "jitfix [(1::int, 3::64 word)] [72::8 word, 1::8 word, 216::8 word, 72::8 word, 57::8 word, 195::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word] [(0::int, 1::nat), (3::int, 1::nat), (12::int, 1::nat), (15::int, 1::nat)]"

value "jitflat_bpf [(1, 2, [0x48, 0x39, 0xc3, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0xc3]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8]),(1, -3, [0x48, 0x39, 0xc3, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00])] init_second_layer"

value "jitfix [(0::int, 2::64 word), (4::int, 1::64 word)] [72::8 word, 57::8 word, 195::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 195::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 57::8 word, 195::8 word,
   15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] [(0::int, 1::nat), (9::int, 1::nat), (10::int, 1::nat), (13::int, 1::nat), (16::int, 1::nat)]"

value "hd ([]::nat list)"
value "tl ([]::nat list)"
(*

definition x64_bin_update ::"x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
 "x64_bin_update l pc u8_list \<equiv>  ( let l1 = list_update l pc (u8_list!0);
                                       l2 = list_update l1 (pc+1) (u8_list!1);
                                       l3 = list_update l2 (pc+2) (u8_list!2);   
                                       l4 = list_update l3 (pc+3) (u8_list!3) in l4)"

definition get_updated_l_bin::"(int\<times>u64) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin"where
  "get_updated_l_bin x l l_pc \<equiv> 
    (let fix_begin_addr = fst (l_pc!(nat(fst x))); 
        (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
        (case x64_decode (nat fix_begin_addr) l of 
              Some(_, Pcall_i _) \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+5+1)::i32);
                              u8_list = u8_list_of_i32 offset in
                              x64_bin_update l (nat (fix_begin_addr+1)) u8_list | 
              _ \<Rightarrow> let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+3+6+1)::i32);
                              u8_list = u8_list_of_i32 offset in                                                     
                             x64_bin_update l (nat (fix_begin_addr+3+2)) u8_list))"*)



(*definition update_l_jump_further::"flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> (hybrid_state \<times> flat_bpf_prog)" where
 "update_l_jump_further lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    (case xst of
    Stuck \<Rightarrow> ((pc, Stuck), lp) |
    Next xpc rs m ss \<Rightarrow> (
    if unat pc \<ge> length l_pc \<or> unat pc < 0 then ((pc, Stuck), lp) else 
    let num = snd (l_pc!(unat pc)) in 
    let old_xpc = nat (fst (l_pc!(unat pc))) in 
      if xpc \<noteq> old_xpc then ((pc, Stuck), lp) else 
        if (\<exists> d. x64_decode xpc l_bin = Some(5, Pcall_i d)) then
            (case find_target_pc_in_l_pc l_jump (uint pc) of 
              None \<Rightarrow> ((pc, Stuck), lp) |
              Some npc \<Rightarrow> 
                (let caller = save_x64_caller rs; fp = save_x64_frame_pointer rs; 
                    rs' = upate_x64_stack_pointer rs (stack_pointer ss) in
                let ss' = update_stack caller fp (pc+1) ss in
                  (case ss' of None \<Rightarrow> ((pc, Stuck), lp) | 
                  Some ra \<Rightarrow> ((npc, (Next (nat (fst (l_pc!(unat npc)))) rs' m ra)), lp))))
        else if (\<exists> src dst. x64_decode xpc l_bin = Some(3, Pcmpq_rr src dst)) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem num l_bin (Next xpc rs m ss) of
          Stuck \<Rightarrow> ((pc, Stuck), lp) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump (uint pc) of
              None \<Rightarrow> ((pc, Stuck), lp) |
              Some npc \<Rightarrow>
                ((npc, (Next (nat (fst (l_pc!(unat npc)))) rs1 m1 ss1)),lp)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              ((pc+1, (Next xpc1 rs1 m1 ss1)), lp)
          ))
        else if x64_decode xpc l_bin = Some(1,Pret) then
          let (pc', ss', caller,fp) = update_stack2 ss in 
          let rs' = restore_x64_caller rs caller fp in ((pc', Next xpc rs' m ss'), lp)
          \<comment>\<open> case: NOT BPF JMP \<close>
        else
          ((pc+1, x64_sem num l_bin (Next xpc rs m ss)), lp)
)))"
*)


definition last_fix_sem::"nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
  "last_fix_sem n lt xst = x64_sem n lt xst"

end