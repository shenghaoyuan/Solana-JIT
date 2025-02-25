theory JITFlat

imports JITPer
begin

type_synonym l_pc = "u64 list"

type_synonym location = u64

type_synonym target_pc = u64

type_synonym l_jump = "(location\<times>target_pc) list"

(*
fun jitflat :: "nat \<Rightarrow> (nat \<times> i64 \<times> x64_bin) list \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump " where
  "jitflat _ [] = ([], [], [])"| 
  "jitflat n (x#xs) = (let l_bin0 = (snd (snd x)) in
        let curr_pc = of_nat (length (snd(snd x)))::u64 in 
        let curr_jump = (fst (snd x)) in
        let fst_res = fst (jitflat (n+1) xs) in
        let snd_res = fst (snd (jitflat (n+1) xs)) in
        let thrd_res =snd (snd (jitflat (n+1) xs)) in
          if curr_jump \<noteq> 1
          then (l_bin0@fst_res, curr_pc# map (\<lambda>y. curr_pc + y) snd_res, (of_nat n,of_nat n + curr_jump)#thrd_res)
          else (l_bin0@fst_res, curr_pc# map (\<lambda>y. curr_pc + y) snd_res, thrd_res))"

value "jitflat 0 [(1, 1, [00000000,11111111]), (1, 1, [00000000]), (1, (-1), [00000000,11111111])]"


*)

(*let curr_pc = (of_nat (length (snd(snd x)))::u64) + sum_list snd_comp in*)

definition negative_value_of_i64::"i64" where
"negative_value_of_i64 \<equiv> 1000000000000000000000000000000000000000000000000000000000000000 "

value "(-1::i64) > negative_value_of_i64"

value "(1::i64) > negative_value_of_i64"

value "(-1::i64) + (2::i64) > negative_value_of_i64"



fun jitflat :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump " where
  "jitflat [] last_comp = last_comp"| 
  "jitflat ((num,off,l_bin0)#xs) (fst_comp,snd_comp,trd_comp) = 
        (let curr_pc = of_nat (length fst_comp) in 
         (if l_bin0!0 = (0xE9::u8) then 
             (jitflat xs (fst_comp@l_bin0, snd_comp@[curr_pc], trd_comp@ [(of_nat (length snd_comp), of_nat (length snd_comp) + off)]))
          else (jitflat xs (fst_comp@l_bin0, snd_comp@[curr_pc], trd_comp))))"

(*
fun jitflat :: "(nat \<times> i64 \<times> x64_bin) list \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump " where
  "jitflat [] last_comp = last_comp"| 
  "jitflat ((num,off,l_bin0)#xs) (fst_comp,snd_comp,trd_comp) = 
        (let curr_pc = of_nat (length fst_comp) in 
          if off = 1 then (jitflat xs (fst_comp@l_bin0, snd_comp@[curr_pc], trd_comp))
          else if off < negative_value_of_i64 then 
             (jitflat xs (fst_comp@l_bin0, snd_comp@[curr_pc], trd_comp@[(of_nat (length snd_comp),of_nat (length snd_comp) + off)]))      
          else let addr_begin = snd_comp!(unat(of_nat(length snd_comp) + off)); u8_list = u8_list_of_u32 ((ucast addr_begin)::u32); l_bin0'= x64_bin_update l_bin0 1 u8_list in
             (jitflat xs (fst_comp@l_bin0', snd_comp@[curr_pc], trd_comp)))"
*)

definition init_second_layer::"x64_bin \<times> l_pc \<times> l_jump" where
"init_second_layer \<equiv> ([],[],[])"

value "jitflat [(1, 1, [0x48,0x01,0xD8]),(1, 2, [0xE9, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8])] init_second_layer"

value "jitflat [(1, 2, [0xE9, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0xc3]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8]),(1, -3, [0xE9, 0x00, 0x00, 0x00, 0x00])] init_second_layer"

value "[0xE9, 0x00, 0x00, 0x00, 0x00]::u8 list "

value "[0x48,0x01,0xD8]::u8 list"

value "(12::64 word) = of_nat(12::nat)"


value "(scast ((-1)::u64))::i64"
value "((-2)::i64) + 1"
value "((-1)::i64)"

(*
  jmp 2
  ret
  add rax rbx
  add rax rbx
  jmp -3
*)

(*
fun jitfix :: "l_jump \<Rightarrow> x64_bin \<Rightarrow> l_pc \<Rightarrow> x64_bin" where
  "jitfix [] _ _  = []" |
  "jitfix (x#xs) l pcs = (let place_end = pcs!(unat (fst x)); addr_begin = pcs!(unat (snd x-1));
                              u8_list = u8_list_of_u32 ((ucast addr_begin)::u32);
                              l' = x64_bin_update l (unat (place_end-3)) u8_list in 
                          jitfix xs l' pcs)"*)

value "(scast ((0x0005::u64)- (0x00011::u64)))::i64"

value "(scast(0x0005::u64)::i32)-(scast(0x00011::u64)::i32)"

value "ucast((scast(0x0005::u64)::i32)-(scast(0x00011::u64)::i32))::u32"

definition x64_bin_update ::"x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
 "x64_bin_update l pc u8_list \<equiv>  ( let l1 = list_update l pc (u8_list!0);
                                       l2 = list_update l1 (pc+1) (u8_list!1);
                                       l3 = list_update l2 (pc+2) (u8_list!2);   
                                       l4 = list_update l3 (pc+3) (u8_list!3) in l4)"

fun jitfix :: "l_jump \<Rightarrow> x64_bin \<Rightarrow> l_pc \<Rightarrow> x64_bin" where
  "jitfix [] l _  = l" |
  "jitfix (x#xs) l pcs = (let fix_begin_addr = pcs!(unat (fst x)); 
                              target_begin_addr = pcs!(unat (snd x));
                              offset = (scast (target_begin_addr)::i32) - (scast(fix_begin_addr+5)::i32);
                              u8_list = u8_list_of_i32 offset;
                              l' = x64_bin_update l (unat (fix_begin_addr+1)) u8_list in 
                          jitfix xs l' pcs)"

value "jitfix [(1::64 word, 3::64 word)] 
  [72::8 word, 1::8 word, 216::8 word, 233::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word]
  [0::64 word, 3::64 word, 8::64 word, 11::64 word]"

value "jitfix [(0::64 word, 2::64 word), (4::64 word, 1::64 word)]
[233::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 195::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word, 233::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word]
[0::64 word, 5::64 word, 6::64 word, 9::64 word, 12::64 word]  "




(*
definition x64_bin_update ::"x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
 "x64_bin_update l pc u8_list \<equiv>  ( let l1 = list_update l pc (u8_list!0);
                                       l2 = list_update l (pc+1) (u8_list!1);
                                       l3 = list_update l (pc+2) (u8_list!2);
                                       l4 = list_update l (pc+3) (u8_list!3) in l4)"

fun jitfix :: "l_jump \<Rightarrow> x64_bin \<Rightarrow> l_pc \<Rightarrow> x64_bin" where
  "jitfix [] _ _  = []" |
  "jitfix (x#xs) l pcs = (let place_end = pcs!(unat (fst x)); addr_end = pcs!(unat (snd x));
                              u8_list = [l!(unat addr_end-3)]@[l!(unat addr_end-2)]@[l!(unat addr_end-1)]@[l!(unat addr_end)];
                              l' = x64_bin_update l (unat (place_end-3)) u8_list in 
                          jitfix xs l' pcs)"
*)
value "x64_encode (Pjmp 0x2)"

(*
fun jitflat1 :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> x64_bin" where
  "jitflat1 [] = []" |
  "jitflat1 (x#xs) = (let l_bin0 = (snd (snd x)) in l_bin0 @ jitflat1 xs)"


fun jitflat2 :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> l_pc" where
  "jitflat2 [] = []"| 
  "jitflat2 (x # xs) = 
     (let curr_pc = of_nat (length (snd (snd x))) :: u64 in
        let rest = jitflat2 xs in
          curr_pc # map (\<lambda>y. curr_pc + y) rest)"


value "jitflat2 [(1, 2, [00000000,11111111]), (2, 3, [00000000]), (3, 4, [11111111,00000000])]"
 
primrec flat :: "'a list list => 'a list" where
  "flat [] = []" |
  "flat (x # xs) = x @ flat xs"

type_synonym l_pc = "(u64, u64) map"

definition init_l_pc :: "l_pc" where " init_l_pc \<equiv> (\<lambda> _ . None)"

definition jitflat2 :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> l_pc" where
"jitflat2 prog = (let curr_pc_list = (map fst (map snd prog)) in
   (\<lambda> i. if i \<ge> 0 \<and> i < of_nat(length curr_pc_list) 
    then (Some (sum_list(take (unat i) curr_pc_list))) else init_l_pc i))"

value "jitflat2"

type_synonym l_jump = "(u64, u64) map"

definition init_l_jump :: "l_jump" where " init_l_jump \<equiv> (\<lambda> i . Some i)"

definition jitflat3 :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> (u64 \<times> u64) list" where
"jitflat3 prog = (let curr_jump_list::u64 list = (map fst (map snd prog)) in
   (\<lambda> i. if (curr_jump_list !(unat i) \<noteq> (1::u64))
    then Some (curr_jump_list !(unat i)) else init_l_jump i))"
*)

value "x64_encode (Pjmp ((-1)::i32))"


                                                 
qed

end