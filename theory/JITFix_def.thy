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
                          (exec_instr (Pjcc cond (of_nat (fst (l_pc!(unat npc)))-(of_nat (xpc+sz+1)))) sz xpc rs m ss))) |
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



value "x64_encode (Pcall_i 0x1111)"

value "u8_list_of_i32 0x1111"

value "x64_encode (Pjcc Cond_e 0x00000000)"

value "u8_list_of_i32 0x11110000"

value "u32_of_u8_list [0,0,0,0]"

value "x64_bin_update 4 [232::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] 1 [17::8 word, 17::8 word, 0::8 word, 0::8 word]"

value "x64_bin_update 4 [15::8 word, 132::8 word, 0::8 word, 0::8 word, 17::8 word, 17::8 word] 2 [0::8 word, 0::8 word, 17::8 word, 17::8 word]"


definition get_updated_l_bin::"(int\<times>u64) \<Rightarrow> x64_bin \<Rightarrow> (nat \<times> nat) list \<Rightarrow> x64_bin option"where
  "get_updated_l_bin x l l_pc \<equiv> 
    (let fix_begin_addr = fst (l_pc!(nat(fst x))); 
        (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
        (case x64_decode fix_begin_addr l of 
              Some(sz, Pcall_i _) \<Rightarrow> let u8_list = x64_encode (Pcall_i (of_nat target_begin_addr)) in
                                     Some (x64_bin_update (length u8_list) l fix_begin_addr u8_list) |
              Some(sz, Pcmpq_rr src dst) \<Rightarrow> let loc = fix_begin_addr+sz in 
                    (case x64_decode loc l of 
                            Some(sz2, Pjcc cond _) \<Rightarrow> let offset = ((of_nat target_begin_addr)::i32) - ((of_nat (loc+sz2)+1)::i32) in
                                                      let u8_list = x64_encode (Pjcc cond (ucast offset)) in                                                     
                                                      Some (x64_bin_update (length u8_list) l loc u8_list) | 
                            _ \<Rightarrow> None ) |
              _ \<Rightarrow> None ))"

value "x64_decode 0 [72::8 word, 57::8 word, 195::8 word] "


value "x64_decode 0 [15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] "


value "get_updated_l_bin (0,1) [72::8 word, 57::8 word, 195::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word ,195::8 word] [(0, 8::nat), (9, 1::nat)]"

value "get_updated_l_bin (0,1) [232::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word ,195::8 word] [(0, 1::nat), (6, 1::nat)]"

(*input: l_jump x64_bin l_pc*)
fun jitfix :: "((int\<times>u64) list) \<Rightarrow> x64_bin \<Rightarrow> (nat \<times> nat) list \<Rightarrow> x64_bin option" where
  "jitfix [] l _  = Some l" |
  "jitfix (x#xs) l l_pc = (if l = [] then None else 
    let res = get_updated_l_bin x l l_pc in case res of None \<Rightarrow> None | 
                                                        Some l' \<Rightarrow> jitfix xs l' l_pc)"

value "x64_encode (Pcmpq_rr RAX RBX)"

value "x64_encode (Pret)"

value "jitflat_bpf [(1, 1, [0x48,0x01,0xD8]),(1, 2, [0x48, 0x39, 0xc3, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8])] init_second_layer"

value "jitfix [(1::int, 3::64 word)] [72::8 word, 1::8 word, 216::8 word, 72::8 word, 57::8 word, 195::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word] [(0, 1::nat), (3, 1::nat), (12, 1::nat), (15, 1::nat)]"

value "jitflat_bpf [(1, 2, [0x48, 0x39, 0xc3, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0xc3]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8]),(1, -3, [0x48, 0x39, 0xc3, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00])] init_second_layer"

value "jitfix [(0::int, 2::64 word), (4::int, 1::64 word)] [72::8 word, 57::8 word, 195::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 195::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 57::8 word, 195::8 word,
   15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] [(0, 1::nat), (9, 1::nat), (10, 1::nat), (13, 1::nat), (16, 1::nat)]"

value "tl ([]::nat list)"


definition last_fix_sem::"nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
  "last_fix_sem n lt xst = x64_sem n lt xst"

end