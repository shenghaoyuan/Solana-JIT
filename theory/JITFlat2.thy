theory JITFlat2

imports JITPer_aux
begin


type_synonym flat_bpf_prog = "x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)"

fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
  let curr_pc = of_nat (length l_bin) in 
    if l_bin0!0 = (0xE9::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
      jitflat_bpf xs (
        l_bin@l_bin0,
        l_pc@[(curr_pc,num)],
        l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)])
    else
      jitflat_bpf xs (l_bin@l_bin0, l_pc@[(curr_pc,num)], l_jump)
)"

fun find_target_pc_in_l_pc :: "((u64\<times>u64) list) \<Rightarrow> u64 \<Rightarrow> u64 option" where
"find_target_pc_in_l_pc [] _ = None" |
"find_target_pc_in_l_pc ((x, y)#xs) pc = (
  if x = pc then Some y
  else find_target_pc_in_l_pc xs pc
)"

definition init_second_layer::"x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)" where
"init_second_layer \<equiv> ([],[],[])"


definition flat_bpf_one_step :: "u64 \<Rightarrow> nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step xpc num lp st = (

  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc_old rs m \<Rightarrow> (
      if xpc \<noteq> xpc_old then \<comment>\<open> In this case, xpc should be equal to xpc_old \<close>
        (pc, Stuck)
      else
        if l_bin!(unat xpc) = (0x0f::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          case x64_sem 1 l_bin (Next xpc rs m) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (fst (l_pc!(unat npc))) rs1 m1)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, xst)
          )
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc rs m))
))"theory JITFlat2

imports JITPer_aux
begin


type_synonym flat_bpf_prog = "x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)"

fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
  let curr_pc = of_nat (length l_bin) in 
    if l_bin0!0 = (0xE9::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
      jitflat_bpf xs (
        l_bin@l_bin0,
        l_pc@[(curr_pc,num)],
        l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)])
    else
      jitflat_bpf xs (l_bin@l_bin0, l_pc@[(curr_pc,num)], l_jump)
)"

fun find_target_pc_in_l_pc :: "((u64\<times>u64) list) \<Rightarrow> u64 \<Rightarrow> u64 option" where
"find_target_pc_in_l_pc [] _ = None" |
"find_target_pc_in_l_pc ((x, y)#xs) pc = (
  if x = pc then Some y
  else find_target_pc_in_l_pc xs pc
)"

definition init_second_layer::"x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)" where
"init_second_layer \<equiv> ([],[],[])"


definition flat_bpf_one_step :: "u64 \<Rightarrow> nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step xpc num lp st = (

  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc_old rs m \<Rightarrow> (
      if xpc \<noteq> xpc_old then \<comment>\<open> In this case, xpc should be equal to xpc_old \<close>
        (pc, Stuck)
      else
        if l_bin!(unat xpc) = (0x0f::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          case x64_sem 1 l_bin (Next xpc rs m) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (fst (l_pc!(unat npc))) rs1 m1)) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, xst)
          )
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc rs m))
))"


lemma one_step_equiv:
  "flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
   jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
   one_step lt (pc,xst) = xxst \<Longrightarrow>
   fxst = xxst"
  sorry



fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ hst = hst" |
"flat_bpf_sem (Suc n) (l_bin,l_pc,l_jump) (pc, xst) = (
  let (xpc, num) = l_pc!(unat pc) in
  let (npc, nxst) = flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) in
  flat_bpf_sem n (l_bin,l_pc,l_jump) (npc, nxst)
)"

lemma n_steps_equiv:
  "flat_bpf_sem n (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
  jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
  x64_sem1 n lt (pc, xst) = xxst \<Longrightarrow>
  fxst = xxst"
proof(induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) (l_bin, l_pc, l_jump) (pc, xst) = fxst" and 
  assm1:"jitflat_bpf lt init_second_layer = (l_bin, l_pc, l_jump)" and
  assm2:"x64_sem1 (Suc n) lt (pc, xst) = xxst" 
  then show ?case sorry
qed


(*

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


fun x64_sem2::"nat \<Rightarrow> x64_bin \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
 "x64_sem2 0 _ st = st" |
 "x64_sem2 (Suc n) lt (pc,xst) = 
  (let xst' = x64_sem 1 lt xst;
   off = (case xst' of Stuck \<Rightarrow> pc |
                Next pc' rs' m' \<Rightarrow> pc') in
    x64_sem2 n lt (off,xst'))"


(*

fun x64_sem2::"nat \<Rightarrow> x64_bin \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
 "x64_sem2 0 _ (pc,st) = (let xst_temp =
   case st of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck in (pc,xst_temp))" |
 "x64_sem2 (Suc n) lt (pc,xst) = 
  (let xst_temp = (
    case xst of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck) in
  (let xst' = x64_sem 1 lt xst_temp;
   off = (case xst' of Stuck \<Rightarrow> pc |
                Next pc' rs' m' \<Rightarrow> pc') in
    x64_sem2 n lt (off,xst')))"


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



lemma refinement_relation_of_two_layers:
  "snd st = Next pc rs m \<Longrightarrow>
  x64_sem1 n x64_prog st = st1 \<Longrightarrow>
  snd st1 = Next pc' rs' m' \<Longrightarrow>
  (l_bin0, pc_info, jump_info) = jitflat x64_prog init_second_layer \<Longrightarrow>
  jitfix jump_info l_bin0 pc_info = x64_prog2 \<Longrightarrow>
  x64_sem2 n x64_prog2 st = st2 \<Longrightarrow>
  st1 = st2"
  sorry
                                                 
*)

end


lemma one_step_equiv:
  "flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
   jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
   one_step lt (pc,xst) = xxst \<Longrightarrow>
   fxst = xxst"
  sorry



fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ hst = hst" |
"flat_bpf_sem (Suc n) (l_bin,l_pc,l_jump) (pc, xst) = (
  let (xpc, num) = l_pc!(unat pc) in
  let (npc, nxst) = flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) in
  flat_bpf_sem n (l_bin,l_pc,l_jump) (npc, nxst)
)"

lemma n_steps_equiv:
  "flat_bpf_sem n (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
  jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
  x64_sem1 n lt (pc, xst) = xxst \<Longrightarrow>
  fxst = xxst"
proof(induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) (l_bin, l_pc, l_jump) (pc, xst) = fxst" and 
  assm1:"jitflat_bpf lt init_second_layer = (l_bin, l_pc, l_jump)" and
  assm2:"x64_sem1 (Suc n) lt (pc, xst) = xxst" 
  then show ?case sorry
qed


(*

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


fun x64_sem2::"nat \<Rightarrow> x64_bin \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
 "x64_sem2 0 _ st = st" |
 "x64_sem2 (Suc n) lt (pc,xst) = 
  (let xst' = x64_sem 1 lt xst;
   off = (case xst' of Stuck \<Rightarrow> pc |
                Next pc' rs' m' \<Rightarrow> pc') in
    x64_sem2 n lt (off,xst'))"


(*

fun x64_sem2::"nat \<Rightarrow> x64_bin \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
 "x64_sem2 0 _ (pc,st) = (let xst_temp =
   case st of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck in (pc,xst_temp))" |
 "x64_sem2 (Suc n) lt (pc,xst) = 
  (let xst_temp = (
    case xst of
    Next xpc rs m \<Rightarrow> Next 0 rs m |
    Stuck \<Rightarrow> Stuck) in
  (let xst' = x64_sem 1 lt xst_temp;
   off = (case xst' of Stuck \<Rightarrow> pc |
                Next pc' rs' m' \<Rightarrow> pc') in
    x64_sem2 n lt (off,xst')))"


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



lemma refinement_relation_of_two_layers:
  "snd st = Next pc rs m \<Longrightarrow>
  x64_sem1 n x64_prog st = st1 \<Longrightarrow>
  snd st1 = Next pc' rs' m' \<Longrightarrow>
  (l_bin0, pc_info, jump_info) = jitflat x64_prog init_second_layer \<Longrightarrow>
  jitfix jump_info l_bin0 pc_info = x64_prog2 \<Longrightarrow>
  x64_sem2 n x64_prog2 st = st2 \<Longrightarrow>
  st1 = st2"
  sorry
                                                 
*)

end