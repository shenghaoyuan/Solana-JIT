theory JITFlattern2

imports JITFlattern
begin


type_synonym flat_bpf_prog = "x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)"

(*fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
  let curr_pc = of_nat (length l_bin) in 
    if l_bin0!0 = (0x0f::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
      jitflat_bpf xs (
        l_bin@l_bin0,
        l_pc@[(curr_pc,num)],
        l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)])
    else
      jitflat_bpf xs (l_bin@l_bin0, l_pc@[(curr_pc,num)], l_jump)
)"*)

definition update_l_jump::"(nat \<times> u64 \<times> x64_bin) \<Rightarrow> (u64 \<times> nat) list \<Rightarrow> (u64\<times>u64) list \<Rightarrow> (u64\<times>u64) list" where
"update_l_jump x l_pc l_jump \<equiv> let l_bin0 = snd(snd x); off = fst(snd x) in
  if l_bin0!1 = (0x39::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
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

lemma jitflat_bpf_induct:
  "jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> 
   \<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)"
  by (smt (verit) fst_conv jitflat_bpf.elims list.distinct(1) list.sel(3) nth_Cons_0 snd_conv)

lemma not_change_prefix:
  "jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> list_in_list l1 0 l2"
proof(induction l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case using list_in_list_prop
    by fastforce 
next
  case (Cons a l_bin0)
  have assm1:"jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)" using Cons by blast
  have assm2:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> list_in_list l1 (0::nat) l2"
    using Cons by simp

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')"  by (meson prod_cases3)
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')" by auto

  let "?num" = "fst a"
  let "?off" = "fst (snd a)"
  let "?l_bin0" = "snd (snd a)"
  have a3:"jitflat_bpf [(?num,?off,?l_bin0)] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"  
    using jitflat_bpf.simps(2) by blast
  have a4:"l1@?l_bin0 = l2'" using a3
    by (smt (verit) a0 jitflat_bpf.simps(1) split_pairs) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  have a5:"list_in_list l1 (0::nat) l2'" using a4 list_in_list_concat list_in_list_prop by blast
  have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis

  have a7:"list_in_list l2' 0 l2" using a6 by (simp add: Cons.IH) 
  have a6:"list_in_list l1 (0::nat) l2" using a5 list_in_list_x64_decode a7 by blast
  then show ?case by simp
qed

  (*have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')"  by (meson prod_cases3)
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')" by auto
  have a1:"list_in_list l1 (0::nat) l2'" using a0 Cons by auto
  have a2:"jitflat_bpf [a] (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by simp

  let "?num" = "fst a"
  let "?off" = "fst (snd a)"
  let "?l_bin0" = "snd (snd a)"
  have a3:"jitflat_bpf [(?num,?off,?l_bin0)] (l2', l_pc2', l_jump2') =  (
    let curr_pc = of_nat (length l2') in 
    if ?l_bin0!0 = (0x0f::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
      jitflat_bpf [] (
        l2'@?l_bin0,
        l_pc2'@[(curr_pc,?num)],
        l_jump2'@ [(of_nat (length l_pc2'), of_nat (length l_pc2') + ?off)])
    else
      jitflat_bpf [] (l2'@?l_bin0, l_pc2'@[(curr_pc,?num)], l_jump2')
)" using a2  using jitflat_bpf.simps(2) by blast
  have a4:"l2'@?l_bin0 = l2" using a3 a2
    by (smt (verit, ccfv_SIG) jitflat_bpf.simps(1) split_pairs) 
  have a5:"list_in_list l2' 0 l2" using a4 list_in_list_concat list_in_list_prop by blast 
  have a6:"list_in_list l1 (0::nat) l2" using a5 a1 list_in_list_prop2 by auto
    (*by (smt (verit) a2 assm1 jitflat_bpf.simps(2) list_in_list_concat local.Cons(1) split_pairs split_pairs)*)
    (*by (smt (verit) a2 assm1 jitflat_bpf.simps(2) list_in_list_concat local.Cons(1) split_pairs) *)
  then show ?case by simp
qed*)


(*lemma is_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc = 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l = Some(1,Pret)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)
  done  

lemma is_call_insn:"l\<noteq>[] \<Longrightarrow> l!pc = 0xe8 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<exists> d. x64_decode pc l = Some(5, Pcall_i d)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)
  apply(cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)
  done

lemma is_cmp_insn:"l\<noteq>[] \<Longrightarrow> l!(pc+1) = 0x39 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<exists> src dst. x64_decode pc l = Some(3, Pcmpq_rr src dst)"
   apply(simp add: x64_decode_def Let_def)
  apply (cases "l ! pc = (195::8 word)"; simp)
  sorry
*)

(*
fun jitfix :: "((int\<times>u64) list) \<Rightarrow> x64_bin \<Rightarrow> (int \<times> nat) list \<Rightarrow> x64_bin" where
  "jitfix [] l _  = l" |
  "jitfix (x#xs) l l_pc = (let (fix_begin_addr,num1) = l_pc!(nat(fst x)); 
                              (target_begin_addr,num2) = l_pc!(unat (snd x)) in 
                           
                          if (\<exists> d. x64_decode (nat fix_begin_addr) l = Some(5, Pcall_i d)) then
                            
                              let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+5)::i32);
                              u8_list = u8_list_of_i32 offset;
                              l' = x64_bin_update l (nat (fix_begin_addr+1)) u8_list in 
                            jitfix xs l' l_pc
                          
                          else if (\<exists> src dst. x64_decode (nat fix_begin_addr) l = Some(3, Pcmpq_rr src dst)) then 
                           
                              let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+3+6)::i32);
                              u8_list = u8_list_of_i32 offset;
                              l' = x64_bin_update l (nat (fix_begin_addr+3+2)) u8_list in 
                            jitfix xs l' l_pc
                          
                          else                           
                              let offset = ((of_int target_begin_addr)::i32) - ((of_int fix_begin_addr+3+6)::i32);
                              u8_list = u8_list_of_i32 offset;
                              l' = x64_bin_update l (nat (fix_begin_addr+3+2)) u8_list in 
                            jitfix xs l' l_pc)"
*)

(*
fun jitfix :: "((u64\<times>u64) list) \<Rightarrow> x64_bin \<Rightarrow> (u64 \<times> nat) list \<Rightarrow> x64_bin" where
  "jitfix [] _ _  = []" |
  "jitfix (x#xs) l l_pc = (let (place_end,num1) = l_pc!(unat (fst x)); (addr_begin,num2) = l_pc!(unat (snd x-1));
                              u8_list = u8_list_of_u32 ((ucast addr_begin)::u32);
                              l' = x64_bin_update l (unat (place_end-3)) u8_list in 
                          jitfix xs l' l_pc)"
*)

(*
fun last_fix_sem::"nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
 "last_fix_sem 0 _ st = st" |
 "last_fix_sem (Suc n) lt xst = 
  (let xst' = x64_sem 1 lt xst in 
   (case xst' of Stuck \<Rightarrow> Stuck |
                 Next pc' rs' m' ss' \<Rightarrow> 
    last_fix_sem n lt xst'))"*)

(*
fun last_fix_sem::" nat \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
 "last_fix_sem 0 _ _ st = st" |
 "last_fix_sem (Suc n) num lt xst = 
  (let xst' = x64_sem 1 lt xst in 
   (case xst' of Stuck \<Rightarrow> Stuck |
                 Next pc' rs' m' ss' \<Rightarrow> 
    if pc' = num then xst' else 
    last_fix_sem n num lt xst'))"
*)

lemma "jitper insns = Some lt \<Longrightarrow> lt \<noteq> [] \<Longrightarrow> well_formed_prog1 lt"
  using jit_prog_prop3 well_formed_prog1_def sorry



(*
lemma jit_prog_prop1:"x64_encode ins \<noteq> undefined \<Longrightarrow>  x64_encode ins \<noteq> []"
  apply(unfold x64_encode_def)
  apply(cases ins,simp_all)
  subgoal for x7 
    apply(unfold construct_rex_to_u8_def Let_def,simp_all)
    done
  subgoal for x8
    apply(unfold construct_rex_to_u8_def Let_def,simp_all)
    done
  subgoal for x111 x112
apply(unfold construct_rex_to_u8_def Let_def,simp_all)
    done
  subgoal for x151 x152 x153
    apply(cases x151,simp_all)
    subgoal for x1 x2 x3 
      apply(cases x1,simp_all) 
      subgoal for a apply(cases x2,simp_all)
         apply(unfold construct_rex_to_u8_def Let_def,simp_all)
        sorry
      done
    done
  subgoal for x201 x202 x203
    apply(cases x202,simp_all) 
    subgoal for x1 x2 x3
      apply(cases x1,simp_all) 
      subgoal apply(cases x2,simp_all) 
         apply(unfold construct_rex_to_u8_def Let_def,simp_all)
         apply(cases x203,simp_all) 
        sorry
    done
  done
*)

(*lemma "jitper insns = Some lt \<Longrightarrow> insns \<noteq> [] \<Longrightarrow> lt \<noteq> []"
  using jit_prog_prop3 *)


(*lemma jit_prog_prop2:"per_jit_ins ins = Some (num,off,l_bin0) \<Longrightarrow> \<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst) \<Longrightarrow> l_bin0\<noteq>[] \<Longrightarrow> num = 1"*)
lemma jit_prog_prop3:
  "jitper insns = Some lt \<Longrightarrow> 
  lt \<noteq> [] \<Longrightarrow>
  lt!(unat pc) = (num,off,l_bin0) \<Longrightarrow> 
  unat pc < length lt \<and> unat pc \<ge> 0 \<Longrightarrow> 
  num > 0"
  sorry

(*
lemma flattern_lbin_easy:
  assumes a0:"l_bin0!0=(num,off,l)" and
   a1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1) ) = xpc" and
   a4:"well_formed_prog l_bin0"
 shows "list_in_list l (unat xpc) l2"
proof-
  let "?xs" = "tl l_bin0"
  have b0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
  let curr_pc = of_nat (length l1) in 
  let l_jump' = update_l_jump (num,off,l) l_pc1 l_jump1 in  
      jitflat_bpf ?xs (l1@l, l_pc1@[(curr_pc,num)], l_jump'))" using a1 by auto

  have b1:"(num,off,l)#?xs = l_bin0" using a0 a1
    by (metis Nitpick.size_list_simp(2) hd_conv_nth list.collapse not_less0) 
  have c0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) =  (jitflat_bpf ?xs (l1@l, l_pc1@[(of_nat (length l1),num)], update_l_jump (num,off,l) l_pc1 l_jump1))"
      using b0 by auto
  have c1_0:"jitflat_bpf ?xs (l1@l, l_pc1@[((of_nat (length l1)),num)],update_l_jump (num,off,l) l_pc1 l_jump1) = (l2,l_pc2,l_jump2)" using c0 a2 b1 by simp 
  have c1_1:"list_in_list (l_pc1@[((of_nat (length l1)),num)]) 0 l_pc2" using c1_0 not_change_prefix_l_pc by simp
  have c1_2:"list_in_list [((of_nat (length l1)),num)] (length l_pc1) l_pc2" using c1_1 list_in_list_concat by force
  have c1:"l_pc2! (length(l_pc1)) = ((of_nat (length l1)),num)" using not_change_prefix_l_pc c1_2 by simp

  have c2:"xpc = of_nat (length l1)" using c1 a3 by simp

  have c3_1:"list_in_list (l1@l) 0 l2" using c1_0 not_change_prefix_l_bin by blast
  have c3_2:"list_in_list l (length l1) l2" using c3_1 list_in_list_concat by (metis plus_nat.add_0)  
  then have c3_3:"unat (of_nat (length l1)) = (length l1)" sorry   
    then show ?thesis by simp    
  qed
*)

(*lemma flattern_l_bin0:
  assumes a0:"l_bin0!(unat pc)=(num,off,l)" and
   a1:"l_bin0 \<noteq> []" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1 + (unat pc))) = xpc"
 shows "list_in_list l (unat xpc) l2"
  sorry*)

(*lemma flattern_l_bin0:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   unat pc < length l_bin0 \<and> unat pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
   fst (l_pc2 ! (length l_pc1 + (unat pc))) = xpc \<Longrightarrow>
   list_in_list l (unat xpc) l2"
proof(induct l_bin0 arbitrary: pc num off l l1 l_pc1 l_jump1 l2 l_pc2 l_jump2 xpc)
  case Nil
  then show ?case by simp
next
  case (Cons a l_bin0)
  assume assm0:"l_bin0!(unat pc)=(num,off,l)" and
   assm1:"unat pc < length l_bin0 \<and> unat pc \<ge> 0" and
   assm2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   assm3:"fst (l_pc2 ! (length l_pc1 + (unat pc))) = xpc"
  then show ?case sorry
qed*)

(*lemma l_jump_upperbound:
  "is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  snd(snd a) !1 = 0x39 \<Longrightarrow>
  \<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 < of_nat (length l_pc1)"
  using l_jump_elem_increases is_increase_list_def *)


(*
lemma l_jump_upperbound:
  "is_increase_list l_jump1 l_pc1 \<Longrightarrow>
  jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  snd(snd a) !1 = 0x39 \<Longrightarrow>
  \<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 < of_nat (length l_pc1)"
  using l_jump_elem_increases is_increase_list_def 
proof-
  assume 
  assm1:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) " and
  assm2:"snd(snd a) !1 = 0x39" and
  assm3:"is_increase_list l_jump1"
  have a1:"l_jump =  update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims assm1 by force
  hence "l_jump =  (let (num,off,l_bin0) = a in 
  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)]
  else l_jump1)" using update_l_jump_def by simp
  have "[a]\<noteq> []" by simp
  hence a2:"is_increase_list l_jump" using assm1 l_jump_elem_increases assm3 by blast
  hence b0:"l_jump =  l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + fst (snd a))]" using a1 assm2 by (simp add: case_prod_unfold update_l_jump_def) 
  hence b1:"l_jump \<noteq> []" by blast
  have b2:"length l_jump1 < length l_jump" using b0 by simp
  hence b3:"\<forall> idx1. idx1 < length l_jump1 \<and> idx1\<ge>0 \<and> length l_jump1 < length l_jump \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!(length l_jump1))" 
    using a2 b0 b1 b2 is_increase_list_def by blast 
  have b4:"fst (l_jump!(length l_jump1)) = of_nat (length l_pc1)" using b0 by fastforce 
  then show ?thesis using b3 by (smt (z3) assm1 add.commute add.right_neutral add_Suc_right b2 fst_conv in_set_conv_decomp le_add1 le_imp_less_Suc length_Cons length_append list_in_list.simps(2) list_in_list_concat not_change_prefix_l_jump) 
  qed
*)

(*
lemma l_jump_elem_increases:
  "jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1) \<Longrightarrow> 
  \<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_jump1 \<longrightarrow> fst (l_jump1!idx1) < fst (l_jump1!idx2) \<Longrightarrow>
  jitflat_bpf lt (l1, l_pc1, l_jump1) = (l, l_pc, l_jump) \<Longrightarrow> 
  \<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_jump \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!idx2)"
  proof(induct lt arbitrary: somelt l1 l_pc1 l_jump1 l l_pc l_jump)
    case Nil
    have "(l1, l_pc1, l_jump1) = (l, l_pc, l_jump)" using Nil by auto
    then show ?case using Nil.prems(2) by blast 
  next
    case (Cons a lt)
    assume assm0:"jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)"and
      assm1:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l, l_pc, l_jump)" 
      (*and assm2:"(a#lt) \<noteq> []"*)
    have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and>  jitflat_bpf lt (l2',l_pc2',l_jump2') = (l,l_pc,l_jump)"
      using jitflat_bpf_induct assm1 by blast 
    then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1,l_pc1,l_jump1) = (l2',l_pc2',l_jump2') \<and> jitflat_bpf lt (l2',l_pc2',l_jump2') = (l,l_pc,l_jump)" by auto
    have b1:"jitflat_bpf (somelt@[a]) init_second_layer =  (l2',l_pc2',l_jump2')" 
      using b0 assm0 by (metis (no_types, opaque_lifting) jitflat_bpf_induct3 prod_cases3) 
    have "\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_jump \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!idx2)" using b1 b0 using Cons.hyps sorry 
    then show ?case by auto
  qed

lemma l_jump_upperbound:
  "jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1) \<Longrightarrow> 
  jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow>
  snd(snd a) !1 = 0x39 \<Longrightarrow>
  \<forall> elem1 elem2. (elem1,elem2) \<in> set l_jump1 \<longrightarrow> elem1 < of_nat (length l_pc1)"
proof-
  assume assm0:"jitflat_bpf somelt init_second_layer = (l1, l_pc1, l_jump1)" and
  assm1:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) " and
  assm2:"snd(snd a) !1 = 0x39"
  have a1:"l_jump =  update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims assm1 by force
  hence "l_jump =  (let (num,off,l_bin0) = a in 
  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)]
  else l_jump1)" using update_l_jump_def by simp
  have "[a]\<noteq> []" by simp
  hence a2:"\<forall> idx1 idx2. idx1<idx2 \<and> idx1\<ge>0 \<and> idx2 < length l_jump \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!idx2)" using assm0 assm1 l_jump_elem_increases sorry 
  hence b0:"l_jump =  l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + fst (snd a))]" using a1 assm2 by (simp add: case_prod_unfold update_l_jump_def) 
  hence b1:"l_jump \<noteq> []" by blast
  have b2:"length l_jump1 < length l_jump" using b0 by simp
  hence b3:"\<forall> idx1. idx1 < length l_jump1 \<and> idx1\<ge>0 \<and> length l_jump1 < length l_jump \<longrightarrow> fst (l_jump!idx1) < fst (l_jump!(length l_jump1))" using a2 b0 b1 b2 by blast
  have b4:"fst (l_jump!(length l_jump1)) = of_nat (length l_pc1)" using b0 by fastforce 
  then show ?thesis using b3 by (smt (z3) assm1 add.commute add.right_neutral add_Suc_right b2 fst_conv in_set_conv_decomp le_add1 le_imp_less_Suc length_Cons length_append list_in_list.simps(2) list_in_list_concat not_change_prefix_l_jump) 
  qed
*)






(*
lemma l_jump_is_distinct:"jitflat_bpf lt (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump) \<Longrightarrow> distinct (map fst l_jump1) \<Longrightarrow> distinct (map fst l_jump)"
proof(induct lt arbitrary: l1 l_pc1 l_jump1 l_bin l_pc l_jump)
  case Nil
  then show ?case by simp
next
  case (Cons a lt)
  assume a0:"jitflat_bpf (a#lt) (l1, l_pc1, l_jump1) = (l_bin,l_pc,l_jump)" and 
  a1:"distinct (map fst l_jump1)"
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" using jitflat_bpf_induct a0 by simp
  then obtain l2' l_pc2' l_jump2' where b0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf lt (l2', l_pc2', l_jump2') = (l_bin,l_pc,l_jump)" by auto
  hence "l_jump2' = update_l_jump a l_pc1 l_jump1" using jitflat_bpf.elims by force 
  hence b1:"l_jump2' = (let (num,off,l_bin0) = a in  if l_bin0!1 = (0x39::u8) then l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + off)] else l_jump1)" using update_l_jump_def by simp
  thus ?case
  proof(cases "(snd (snd a))!1 \<noteq> (0x39::u8)")
    case True
    have "l_jump2' = l_jump1" using b1 True  by (smt (verit, best) case_prod_conv split_pairs)
    hence b2:"distinct (map fst l_jump2')" using a1 by simp
    have "distinct (map fst l_jump)" using b0 b1 b2 Cons by blast
    then show ?thesis using a1 by simp
  next
    case False
    have "l_jump2' = l_jump1@ [(of_nat (length l_pc1), of_nat (length l_pc1) + (fst (snd a)))]" using False b1 by (smt (verit, ccfv_threshold) old.prod.case prod.collapse) 
    hence b2:"distinct (map fst l_jump2')" sorry
    have "distinct (map fst l_jump)" using b0 b1 b2 Cons by blast
    then show ?thesis by simp
  qed
qed*)

   (*flat_bpf_sem n (l_bin,l_pc,l_jump) (pc,fxst) = fxst' \<Longrightarrow>*)
(*lemma flattern_jump_index:
  "jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  unat pc < length lt \<and> unat pc \<ge> 0  \<Longrightarrow>
  find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow>
  npc = off + pc"
  proof(induct lt arbitrary: l_bin l_pc l_jump pc num off l npc)
    case Nil
    then show ?case  by (simp add: init_second_layer_def) 
  next
    case (Cons a lt)
    assume assm0:"jitflat_bpf (a#lt) init_second_layer = (l_bin,l_pc,l_jump)" and
      assm1:"(a#lt)!(unat pc) = (num,off,l)" and
      assm2:"find_target_pc_in_l_pc l_jump pc = Some npc"and
      assm3:"unat pc < length (a#lt) \<and> unat pc \<ge> 0" 
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
      show ?case
      proof(cases "unat pc = 0")
        case True
        then show ?thesis 
          using flattern_jump_index_easy True assm0 assm1 assm2 assm3 unat_eq_zero by blast  
      next
        case False
        have a1:"pc \<ge>1" using False a0 linorder_le_less_linear by force 
        let "?pc" = "pc -1"
        have b1:"unat ?pc < length lt \<and> (0::nat) \<le> unat ?pc" using assm3 a1 False unat_sub by fastforce 
        let "?x" = "tl lt"
        have b2:"lt ! (unat ?pc) = (num, off, l)" using assm1 False by (simp add: a1 unat_sub) 
 
      
        have b2_1:"jitflat_bpf (a#lt) init_second_layer = (
          jitflat_bpf lt (
            []@(snd(snd a)),
            []@[(0, fst a)],
            update_l_jump a [] []))" using init_second_layer_def 
          by (metis jitflat_bpf.simps(2) list.size(3) prod.exhaust_sel semiring_1_class.of_nat_0) 
        hence b2_2:"jitflat_bpf (a#lt) init_second_layer = jitflat_bpf lt ((snd(snd a)),[(0, fst a)],update_l_jump a [] [])" by auto
      
        have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf lt init_second_layer = (l2',l_pc2',l_jump2') " by (metis surj_pair)
        then obtain l2' l_pc2' l_jump2' where b3_1:"jitflat_bpf lt init_second_layer = (l2',l_pc2',l_jump2')" by auto
        have "jitflat_bpf lt init_second_layer = (l_bin, l_pc, l_jump) \<Longrightarrow> lt ! unat pc = (num, off, l) \<Longrightarrow> 
        unat pc < length lt \<and> (0::nat) \<le> unat pc \<Longrightarrow> find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow> npc = off + pc" using Cons by blast
        have "find_target_pc_in_l_pc l_jump2' ?pc = Some npc" using assm2
        hence "npc = off + ?pc" using Cons b1 b2 b3_1 by blast
        then show ?thesis 
      qed
    qed
*)

(*lemma flattern_jump_index:
  "jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  unat pc < length lt \<and> unat pc \<ge> 0  \<Longrightarrow>
  find_target_pc_in_l_pc l_jump pc = Some npc \<longrightarrow> npc = off + pc"
  proof(induct lt arbitrary: l_bin l_pc l_jump pc num off l npc)
    case Nil
    then show ?case  by (simp add: init_second_layer_def) 
  next
    case (Cons a lt)
    assume assm0:"jitflat_bpf (a#lt) init_second_layer = (l_bin,l_pc,l_jump)" and
      assm1:"(a#lt)!(unat pc) = (num,off,l)" and
      assm3:"unat pc < length (a#lt) \<and> unat pc \<ge> 0" 
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
      show ?case
      proof(cases "unat pc = 0")
        case True
        then show ?thesis 
          using flattern_jump_index_easy True assm0 assm1 assm3 unat_eq_zero by blast  
      next
        case False
        have a1:"pc \<ge>1" using False a0 linorder_le_less_linear by force 
        let "?pc" = "pc -1"
        have b1:"unat ?pc < length lt \<and> (0::nat) \<le> unat ?pc" using assm3 a1 False unat_sub by fastforce 
        let "?x" = "tl lt"
        have b2:"lt ! (unat ?pc) = (num, off, l)" using assm1 False by (simp add: a1 unat_sub)      
        have b2_1:"jitflat_bpf (a#lt) init_second_layer = (
          jitflat_bpf lt (
            []@(snd(snd a)),
            []@[(0, fst a)],
            update_l_jump a [] []))" using init_second_layer_def 
          by (metis jitflat_bpf.simps(2) list.size(3) prod.exhaust_sel semiring_1_class.of_nat_0) 
        hence b2_2:"jitflat_bpf (a#lt) init_second_layer = jitflat_bpf lt ((snd(snd a)),[(0, fst a)],update_l_jump a [] [])" by auto
      
        have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf lt init_second_layer = (l2',l_pc2',l_jump2') " by (metis surj_pair)
        then obtain l2' l_pc2' l_jump2' where b3_1:"jitflat_bpf lt init_second_layer = (l2',l_pc2',l_jump2')" by auto
        have "jitflat_bpf lt init_second_layer = (l_bin, l_pc, l_jump) \<Longrightarrow> lt ! unat pc = (num, off, l) \<Longrightarrow> 
        unat pc < length lt \<and> (0::nat) \<le> unat pc \<Longrightarrow> find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow> npc = off + pc" using Cons by blast
        hence "find_target_pc_in_l_pc l_jump2' ?pc = Some npc \<longrightarrow> npc = off + ?pc" using Cons b1 b2 b3_1 by blast
        hence "find_target_pc_in_l_pc l_jump pc = Some npc \<longrightarrow> npc = off + pc" sorry
        then show ?thesis by force 
      qed
    qed*)

(*
lemma flattern_jump_index_easy:
  "jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
  lt!(unat pc) = (num,off,l) \<Longrightarrow>
  find_target_pc_in_l_pc l_jump pc = Some npc \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow>
  pc = 0 \<Longrightarrow>
  npc = off + pc"
proof-
  assume a0:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
  a1:"lt!(unat pc) = (num,off,l)" and
  a2:"find_target_pc_in_l_pc l_jump pc = Some npc" and
  a3:"lt \<noteq> []" and
  a4:"pc = 0"
  let "?xs" = "tl lt"
  have a5:"(num,off,l)#?xs = lt" using a1 a3 a4
    by (metis list.collapse nth_Cons_0 unat_0) 
  have b0:"jitflat_bpf ((num,off,l)#?xs) init_second_layer = (
  let curr_pc = 0 in 
  let l_jump' = update_l_jump (num,off,l) [] [] in
      jitflat_bpf ?xs (
        []@l,
        []@[(curr_pc,num)],
        l_jump'))" using a0 init_second_layer_def a4
    by (metis jitflat_bpf.simps(2) list.size(3) semiring_1_class.of_nat_0) 
  have b1_1:"l_jump \<noteq> []" using a2 by force 
  have b1:"distinct (map fst l_jump)" using l_jump_is_distinct init_second_layer_def
    by (metis a0 distinct.simps(1) map_fst_zip zip_Nil) 
  hence b2:"(0,npc) \<in> set l_jump" using a2 a4 search_l_jump by blast
  have b3:"update_l_jump (num,off,l) l_pc l_jump = (
  if l!1 = (0x39::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
  else l_jump)" 
    apply(unfold update_l_jump_def Let_def,simp_all) done
  have b4:"l_jump \<noteq> []" using a2 by auto

  have "l!1 = (0x39::u8) \<or> l!1 \<noteq> (0x39::u8)" by auto
  thus ?thesis
  proof(cases "l!1 = (0x39::u8)")
    case True
    have "update_l_jump (num,off,l) [] [] = [(0, off)]" using True b0 by (simp add: update_l_jump_def) 
    hence"jitflat_bpf ((num,off,l)#?xs) init_second_layer = (
        jitflat_bpf ?xs (l,[(0,num)],[(0,off)]))" using b0 init_second_layer_def by fastforce 
    hence "(0,off) \<in> set l_jump" using a0 a5 not_change_prefix_l_jump b1_1
      by (metis (no_types, lifting)  find_target_pc_in_l_pc.elims list.set_intros(1) list_in_list.simps(2) nth_Cons_0) 
    hence "npc = off + pc" using a4 a2 b1 b2 eq_key_imp_eq_value by fastforce   
    then show ?thesis by simp
  next
    case False
    have "update_l_jump (num,off,l) [] [] = []" using False b0 by (simp add: update_l_jump_def)
    hence "jitflat_bpf ((num,off,l)#?xs) init_second_layer = (jitflat_bpf ?xs (l,[(0,num)],[]))" using b0 init_second_layer_def by fastforce
    hence "\<not>(\<exists> x. x \<in> set l_jump \<and> fst x = pc)" using b4 a3 a0 sorry
    hence "find_target_pc_in_l_pc l_jump pc = None" using a4 b2 by auto 
    then show ?thesis using a2 by fastforce 
  qed
qed
*)
lemma not_change_prefix2:
  "jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow> list_in_list l_pc1 0 l_pc2"
  proof(induction l_bin0 arbitrary: l1 l_pc1 l_jump1 l2 l_pc2 l_jump2)
  case Nil
  then show ?case using list_in_list_prop
    by fastforce 
next
  case (Cons a l_bin0)
  have assm1:"jitflat_bpf (a # l_bin0) (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2)" using Cons by blast
  have assm2:"jitflat_bpf l_bin0 (l1, l_pc1, l_jump1) = (l2, l_pc2, l_jump2) \<Longrightarrow> list_in_list l_pc1 0 l_pc2"
    using Cons by simp

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')"  by (meson prod_cases3)
  then obtain l2' l_pc2' l_jump2' where a0:"jitflat_bpf [a] (l1, l_pc1, l_jump1) = (l2', l_pc2', l_jump2')" by auto

  let "?num" = "fst a"
  let "?off" = "fst (snd a)"
  let "?l_bin0" = "snd (snd a)"
  have a3:"jitflat_bpf [(?num,?off,?l_bin0)] (l1, l_pc1, l_jump1) =  (
    let curr_pc = of_nat (length l1) in 
    let l_jump' = update_l_jump (?num,?off,?l_bin0) l_pc1 l_jump1 in
      jitflat_bpf [] (
        l1@?l_bin0,
        l_pc1@[(curr_pc,?num)],
        l_jump'))"  using jitflat_bpf.simps(2) by blast
  have a4:"l_pc1@[(of_nat (length l1),?num)] = l_pc2'" using a3
    by (smt (verit) a0 jitflat_bpf.simps(1) split_pairs) 
      (*lemma list_in_list_concat: "list_in_list (l1 @ l2) pc l = (list_in_list l1 pc l \<and> list_in_list l2 (pc + length l1) l)"*)
  have a5:"list_in_list l_pc1 0 l_pc2'" using a4 list_in_list_concat list_in_list_prop by blast
  have a6:"jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" using a0 assm1 jitflat_bpf_induct by metis

  have a7:"list_in_list l_pc2' 0 l_pc2" using a6 a5 by (simp add: Cons.IH)  
  have a6:"list_in_list l_pc1 (0::nat) l_pc2" using a5 list_in_list_prop2 a7 by blast
  then show ?case by simp
qed


lemma flattern_lbin_easy:
(*  "l_bin!0=(num,off,l) \<Longrightarrow>
   l_bin0 \<noteq> [] \<Longrightarrow>
  jitflat_bpf l_bin (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
  fst (l_pc2 ! (length l_pc1) ) = xpc \<Longrightarrow>
  list_in_list l (unat xpc) l2"*)
  assumes a0:"l_bin0!0=(num,off,l)" and
   a1:"l_bin0 \<noteq> []" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1) ) = xpc"
 shows "list_in_list l (unat xpc) l2"
proof-
  let "?xs" = "tl l_bin0"
  have b0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
  let curr_pc = of_nat (length l1) in 
  let l_jump' = update_l_jump (num,off,l) l_pc1 l_jump1 in  
      jitflat_bpf ?xs (l1@l, l_pc1@[(curr_pc,num)], l_jump'))" using a1 by auto

  have b1:"(num,off,l)#?xs = l_bin0" using a0 a1
    by (metis list.collapse nth_Cons_0) 
  have c0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) =  (jitflat_bpf ?xs (l1@l, l_pc1@[(of_nat (length l1),num)], update_l_jump (num,off,l) l_pc1 l_jump1))"
      using b0 by auto
  have c1_0:"jitflat_bpf ?xs (l1@l, l_pc1@[((of_nat (length l1)),num)],update_l_jump (num,off,l) l_pc1 l_jump1) = (l2,l_pc2,l_jump2)" using c0 a2 b1 by simp 
  have c1_1:"list_in_list (l_pc1@[((of_nat (length l1)),num)]) 0 l_pc2" using c1_0 not_change_prefix2 by simp
  have c1_2:"list_in_list [((of_nat (length l1)),num)] (length l_pc1) l_pc2" using c1_1 list_in_list_concat by force
  have c1:"l_pc2! (length(l_pc1)) = ((of_nat (length l1)),num)" using not_change_prefix2 c1_2 by simp

  have c2:"xpc = of_nat (length l1)" using c1 a3 by simp

  have c3_1:"list_in_list (l1@l) 0 l2" using c1_0 not_change_prefix by blast
  have c3_2:"list_in_list l (length l1) l2" using c3_1 list_in_list_concat by (metis plus_nat.add_0) 
  have c3_3:"unat (of_nat (length l1)) = (length l1)" sorry
  have c3:"list_in_list l (unat xpc) l2" using c2 c3_2 c3_3 by metis
    then show ?thesis by simp    
  qed




lemma flattern_lbin0:
(*  "l_bin!pc=(num,off,l) \<Longrightarrow>
  jitflat_bpf l_bin (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
  fst (l_pc2 ! (length l_pc1 + pc) ) = xpc \<Longrightarrow>
  list_in_list l (length l1 + unat xpc) l2"
  sorry*)
  assumes a0:"l_bin0!pc=(num,off,l)" and
   a1:"l_bin0 \<noteq> []" and
   a2:"jitflat_bpf l_bin0 (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2)" and
   a3:"fst (l_pc2 ! (length l_pc1 + pc)) = xpc"
 shows "list_in_list l (unat xpc) l2"
  sorry
(*proof-
  let "?xs" = "tl l_bin0"
  have b0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) = (
  let curr_pc = of_nat (length l1) in 
  let l_jump' = update_l_jump (num,off,l) l_pc1 l_jump1 in  
      jitflat_bpf ?xs (l1@l, l_pc1@[(curr_pc,num)], l_jump'))" using a1 by auto

  have b1:"(num,off,l)#?xs = l_bin0" using a0 a1
    by (metis list.collapse nth_Cons_0) 
  have c0:"jitflat_bpf ((num,off,l)#?xs) (l1,l_pc1,l_jump1) =  (jitflat_bpf ?xs (l1@l, l_pc1@[(of_nat (length l1),num)], update_l_jump (num,off,l) l_pc1 l_jump1))"
      using b0 by auto
  have c1_0:"jitflat_bpf ?xs (l1@l, l_pc1@[((of_nat (length l1)),num)],update_l_jump (num,off,l) l_pc1 l_jump1) = (l2,l_pc2,l_jump2)" using c0 a2 b1 by simp 
  have c1_1:"list_in_list (l_pc1@[((of_nat (length l1)),num)]) 0 l_pc2" using c1_0 not_change_prefix2 by simp
  have c1_2:"list_in_list [((of_nat (length l1)),num)] (length l_pc1) l_pc2" using c1_1 list_in_list_concat by force
  have c1:"l_pc2! (length(l_pc1)) = ((of_nat (length l1)),num)" using not_change_prefix2 c1_2 by simp

  have c2:"xpc = of_nat (length l1)" using c1 a3 by simp

  have c3_1:"list_in_list (l1@l) 0 l2" using c1_0 not_change_prefix by blast
  have c3_2:"list_in_list l (length l1) l2" using c3_1 list_in_list_concat by (metis plus_nat.add_0) 
  have c3_3:"unat (of_nat (length l1)) = (length l1)" sorry
  have c3:"list_in_list l (unat xpc) l2" using c2 c3_2 c3_3 by metis
    then show ?thesis by simp    
  qed
*)


(*
fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
      jitflat_bpf xs (l_bin@l_bin0, l_pc@[(of_nat (length l_bin),num)],if l_bin0!0 = (0x0f::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
                   else l_jump)
)"*)

fun find_target_pc_in_l_pc :: "((u64\<times>u64) list) \<Rightarrow> u64 \<Rightarrow> u64 option" where
"find_target_pc_in_l_pc [] _ = None" |
"find_target_pc_in_l_pc ((x, y)#xs) pc = (
  if x = pc then Some y
  else find_target_pc_in_l_pc xs pc
)"

definition init_second_layer::"x64_bin \<times> (u64 \<times> nat) list \<times> ((u64\<times>u64) list)" where
"init_second_layer \<equiv> ([],[],[])"


definition flat_bpf_one_step :: "nat \<Rightarrow> nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step xpc num lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
    (case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc_old rs m ss \<Rightarrow> (
      if xpc \<noteq> xpc_old then \<comment>\<open> In this case, xpc should be equal to xpc_old \<close>
        (pc, Stuck)
      else
        if l_bin!(xpc+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem 1 l_bin (Next xpc rs m ss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (unat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, xst)
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc rs m ss))
)))"

fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ (pc,st) = (pc,st)" |
"flat_bpf_sem (Suc n) (l_bin,l_pc,l_jump) (pc, xst) = (
  let (xpc, num) = l_pc!(unat pc) ;
   pair = flat_bpf_one_step (unat xpc) num (l_bin,l_pc,l_jump) (pc, xst) in
  flat_bpf_sem n (l_bin,l_pc,l_jump) pair
)"

definition flat_bpf_one_step :: "flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_one_step lp st = (
  let (l_bin,l_pc,l_jump) = lp in
  let (pc, xst) = st in
  let num = snd (l_pc!(unat pc)) in 
    (case xst of
    Stuck \<Rightarrow> (pc, Stuck) |
    Next xpc rs m ss \<Rightarrow> (
        if l_bin!(xpc+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem 1 l_bin (Next xpc rs m ss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (unat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, xst)
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

(*
lemma one_step_equiv:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, xst) = fxst" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xst) = xxst" and
   a3:"xst = Next xpc xrs xm xss" and
   a4:"lt \<noteq> []"
  shows"fxst = xxst"
proof-
  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst (lt!(unat pc))"
  let "?off" = "fst (snd (lt!(unat pc)))"
  let "?l" = "snd (snd (lt!(unat pc)))"
  have b0:"(?num, ?off, ?l) = lt!(unat pc)" by simp
 
  let "?xpc" = "fst (l_pc ! (unat pc))"
  have c0:"list_in_list ?l (unat ?xpc) l_bin" 
    using flattern_l_bin0 init_second_layer_def a1 b0 a4 by (metis add_0 list.size(3)) 
  have c1:"unat ?xpc= xpc" sorry



  have "fxst = flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, xst)" using a0
    by (metis One_nat_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) old.prod.exhaust) 
  hence c2:"fxst = (
  let num = snd (l_pc!(unat pc)) in 
        if l_bin!(xpc+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem 1 l_bin (Next xpc xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (unat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, xst)
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc xrs xm xss)))" 
    apply(unfold flat_bpf_one_step_def Let_def) 
    using a3 apply(cases xst,simp_all)
    subgoal for x11 by meson 
    done


  have "xxst = perir_step lt (pc,xst)
    " using a2 by (metis One_nat_def perir_sem.simps(1) perir_sem.simps(2) split_pairs)

  hence b1:"xxst = (let (num,off,l) = lt!(unat pc) in 
       if l!0 = 0xc3 then
          let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss')
      else if (l!0 = 0xe8) then 
        let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (off, Next xpc rs' xm ra))
      else if l!1 = (0x39::u8)  then
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck)      
      else
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          (pc+1, xst'))" using perir_step_def b0 a2 a3 apply(cases xst,simp_all)
    done

  thus ?thesis
  proof(cases "?l!0 = 0xc3")
    case True
    have "xxst = (let (num,off,l) = lt!(unat pc) in (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss')))"
      using b1 True by (smt (z3) b0 case_prod_conv)
    then show ?thesis sorry
  next
    case False
    have b2:"?l!0 \<noteq> 0xc3" using False by simp
    then show ?thesis   
    proof(cases "?l!0 = 0xe8")
      case True
      have b3:"?l!0 = 0xe8" using True by simp
      have "xxst = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (?off, Next xpc rs' xm ra)))" using True b1 b0
        by (smt (z3) False case_prod_conv option.case_eq_if) 
      then show ?thesis sorry
    next
      case False
      have b5:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3" using False b2 by simp
      then show ?thesis
      proof(cases "?l!1 = (0x39::u8)")
        case True
        hence "xxst = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (?off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck) )" using True b1 b0 b5
          by (smt (z3) case_prod_conv outcome.exhaust outcome.simps(4) outcome.simps(5))  
        then show ?thesis sorry
      next
        case False
          have b6:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3 \<and> ?l!1 \<noteq> (0x39::u8)" using b5 False by blast
          have d0:"xxst = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          (pc+1, xst'))" using b6 by (smt (verit) b0 b1 case_prod_conv)
          
          have c3_0:"list_in_list ?l xpc l_bin" using c0 c1 by simp
          have c3_1:"?l \<noteq> []" sorry
          have c3:"l_bin!xpc = ?l!0" using c3_0 c3_1
            by (metis list_in_list.simps(2) list_in_list_prop neq_Nil_conv) 
           (* by (metis list.collapse list_in_list.simps(2)) *)
          have c3_2:"l_bin!(xpc+1) \<noteq> (0x39::u8)" sorry
          
          have c4:"fxst = (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin (Next xpc xrs xm xss)))"
            using c2 c3 b6 c3_2 by auto
          have c5_1:"l_pc \<noteq> []" sorry 
          have c5:"fxst = (pc+1, x64_sem ?num l_bin (Next xpc xrs xm xss))"using flattern_num b0 c5_1 a1 init_second_layer_def c4
            by (metis add_0 list.size(3)) 
          have c6_1:"?num>0" sorry
          have "x64_sem ?num l_bin (Next xpc xrs xm xss) = 
              (case x64_decode xpc l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem (?num-1) l_bin (exec_instr ins sz xpc xrs xm xss))" 
            using c5 c6_1 by (metis Suc_diff_1 x64_sem.simps(3)) 
          hence c6:"snd fxst = (case x64_decode xpc l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem (?num-1) l_bin (exec_instr ins sz xpc xrs xm xss))"
            by (simp add: c5) 
          have d1:"snd xxst = 
              (case x64_decode 0 ?l of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem (?num-1) ?l (exec_instr ins sz 0 xrs xm xss))"
            using d0 c6_1 by (metis Suc_diff_1 snd_conv x64_sem.simps(3)) 
          have c7:"x64_decode 0 ?l = x64_decode xpc l_bin" 
            using d1 c6 c0 c1 c3_1 list_in_list_prop2 by simp
          have "snd fxst = snd xxst" using d1 c6 c0 c1 c7 sorry
        then show ?thesis by (simp add: c5 d0) 
      qed
    qed
  qed
qed
 *) 

(*

definition match_state::"hybrid_state \<Rightarrow> hybrid_state \<Rightarrow> nat \<Rightarrow> bool" where
  "match_state fxst xxst num \<equiv> 
  (case fxst of (pc,Next xst xrs xm xss) \<Rightarrow>
    (case xxst of (pc1,Next xst1 xrs1 xm1 xss1) \<Rightarrow> 
      pc = pc1 \<and> xrs = xrs1 \<and> xm = xm1 \<and> xss = xss1 \<and> num = xst1-xst |
                   _ \<Rightarrow> False)|
                 _ \<Rightarrow> False)"

  a6:"match_state (pc, xxst) (pc, fxst) (xpc1-xpc)"
lemma one_step_equiv:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, fxst) = fxst'" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xxst) = xxst'" and
   a3:"xxst = Next xpc xrs xm xss" and
   a4:"lt \<noteq> []" and
   a5:"fxst = Next xpc1 xrs xm xss" 
  shows"\<exists> n. match_state fxst' xxst' n"
proof-
  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst (lt!(unat pc))"
  let "?off" = "fst (snd (lt!(unat pc)))"
  let "?l" = "snd (snd (lt!(unat pc)))"
  have b0:"(?num, ?off, ?l) = lt!(unat pc)" by simp
 
  let "?xpc" = "fst (l_pc ! (unat pc))"
  have c0:"list_in_list ?l (unat ?xpc) l_bin" 
    using flattern_l_bin0 init_second_layer_def a1 b0 a4 by (metis add_0 list.size(3)) 
  have c1:"unat ?xpc= xpc" sorry


  have "fxst' = flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, fxst)" using a0
    by (metis One_nat_def flat_bpf_sem.simps(1) flat_bpf_sem.simps(2) old.prod.exhaust) 
  hence c2:"fxst' = (
  let num = snd (l_pc!(unat pc)) in 
        if l_bin!(xpc1+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
          \<comment>\<open> case: BPF JMP \<close>
          (case x64_sem 1 l_bin (Next xpc1 xrs xm xss) of
          Stuck \<Rightarrow> (pc, Stuck) | \<comment>\<open> if one step error, stop, it should be impossible \<close>
          Next xpc1 rs1 m1 ss1 \<Rightarrow> (
            if rs1 (CR ZF) = 1 then \<comment>\<open> must JUMP \<close>
              (case find_target_pc_in_l_pc l_jump pc of
              None \<Rightarrow> (pc, Stuck) |
              Some npc \<Rightarrow>
                (npc, (Next (unat (fst (l_pc!(unat npc)))) rs1 m1 ss1))) \<comment>\<open> go to the target address in the jited x64 binary \<close>
            else \<comment>\<open> donot JUMP \<close>
              (pc+1, fxst)
          ))
         else
          \<comment>\<open> case: NOT BPF JMP \<close>
          (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))" 
    apply(unfold flat_bpf_one_step_def Let_def) 
    using a3 a5 apply(cases fxst,simp_all)
    subgoal for x11 apply(cases "x64_sem (1::nat) l_bin (Next xpc1 xrs xm xss)",simp_all)
      done
    done

  have "xxst' = perir_step lt (pc,xxst)" using a2 by (metis One_nat_def perir_sem.simps(1) perir_sem.simps(2) split_pairs)

  hence b1:"xxst' = (let (num,off,l) = lt!(unat pc) in 
       if l!0 = 0xc3 then
          let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss')
      else if (l!0 = 0xe8) then 
        let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (off, Next xpc rs' xm ra))
      else if l!1 = (0x39::u8)  then
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck)      
      else
        let xst_temp = Next 0 xrs xm xss; xst' = x64_sem num l xst_temp in
          (pc+1, xst'))" using perir_step_def b0 a2 a3 apply(cases xxst,simp_all)
    done

  thus ?thesis
  proof(cases "?l!0 = 0xc3")
    case True
    have "xxst' = (let (num,off,l) = lt!(unat pc) in (let (pc', ss', caller,fp) = update_stack2 xss in 
          let rs' = restore_x64_caller xrs caller fp in (pc', Next xpc rs' xm ss')))"
      using b1 True by (smt (z3) b0 case_prod_conv)
    then show ?thesis sorry
  next
    case False
    have b2:"?l!0 \<noteq> 0xc3" using False by simp
    then show ?thesis   
    proof(cases "?l!0 = 0xe8")
      case True
      have b3:"?l!0 = 0xe8" using True by simp
      have "xxst' = (let caller = save_x64_caller xrs; fp = save_x64_frame_pointer xrs; 
            rs' = upate_x64_stack_pointer xrs (stack_pointer xss) in
        let ss' = update_stack caller fp (pc+1) xss in
          (case ss' of None \<Rightarrow> (pc, Stuck) | 
          Some ra \<Rightarrow> (?off, Next xpc rs' xm ra)))" using True b1 b0
        by (smt (z3) False case_prod_conv option.case_eq_if) 
      then show ?thesis sorry
    next
      case False
      have b5:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3" using False b2 by simp
      then show ?thesis
      proof(cases "?l!1 = (0x39::u8)")
        case True
        hence "xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          case xst' of
          Next xpc' rs' m' ss'\<Rightarrow>
            if rs' (CR ZF) = 1 then (?off+pc, xst')
            else (pc+1, xst') |
          Stuck \<Rightarrow> (pc, Stuck) )" using True b1 b0 b5
          by (smt (z3) case_prod_conv outcome.exhaust outcome.simps(4) outcome.simps(5))  
        then show ?thesis sorry
      next
        case False
          have b6:"?l!0 \<noteq> 0xe8 \<and> ?l!0 \<noteq> 0xc3 \<and> ?l!1 \<noteq> (0x39::u8)" using b5 False by blast
          have d0:"xxst' = (let xst_temp = Next 0 xrs xm xss; xst' = x64_sem ?num ?l xst_temp in
          (pc+1, xst'))" using b6 by (smt (verit) b0 b1 case_prod_conv)
          
          have c3_0:"list_in_list ?l xpc l_bin" using c0 c1 by simp
          have c3_1:"?l \<noteq> []" sorry
          have c3:"l_bin!xpc = ?l!0" using c3_0 c3_1
            by (metis list_in_list.simps(2) list_in_list_prop neq_Nil_conv) 
           (* by (metis list.collapse list_in_list.simps(2)) *)
          have c3_2:"l_bin!(xpc+1) \<noteq> (0x39::u8)" sorry
          
          have c4:"fxst' = (let num = snd (l_pc!(unat pc)) in (pc+1, x64_sem num l_bin (Next xpc1 xrs xm xss)))"
            using c2 c3 b6 c3_2 a5  
          have c5_1:"l_pc \<noteq> []" sorry 
          have c5:"fxst' = (pc+1, x64_sem ?num l_bin (Next xpc xrs xm xss))"using flattern_num b0 c5_1 a1 init_second_layer_def c4
            by (metis add_0 list.size(3)) 
          have c6_1:"?num>0" sorry
          have "x64_sem ?num l_bin (Next xpc xrs xm xss) = 
              (case x64_decode xpc l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem (?num-1) l_bin (exec_instr ins sz xpc xrs xm xss))" 
            using c5 c6_1 by (metis Suc_diff_1 x64_sem.simps(3)) 
          hence c6:"snd fxst' = (case x64_decode xpc l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem (?num-1) l_bin (exec_instr ins sz xpc xrs xm xss))"
            by (simp add: c5) 
          have d1:"snd xxst' = 
              (case x64_decode 0 ?l of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem (?num-1) ?l (exec_instr ins sz 0 xrs xm xss))"
            using d0 c6_1 by (metis Suc_diff_1 snd_conv x64_sem.simps(3)) 
          have c7:"x64_decode 0 ?l = x64_decode xpc l_bin" 
            using d1 c6 c0 c1 c3_1 list_in_list_prop2 by simp
          have "match_state fxst' xxst'" using d1 c6 c0 c1 c7 sorry
        then show ?thesis by (simp add: c5 d0) 
      qed
    qed
  qed
qed
*)

(*
lemma flattern_l_bin0:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   unat pc < length l_bin0 \<and> unat pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow>
   fst (l_pc2 ! (unat pc)) = xpc \<Longrightarrow>
   list_in_list l (unat xpc) l2"
proof(induct l_bin0 arbitrary: pc num off l l2 l_pc2 l_jump2 xpc)
  case Nil
  then show ?case by simp
next
  case (Cons a l_bin0)
  then show ?case
  proof-
  assume assm0:"(a#l_bin0)!(unat pc)=(num,off,l)" and
   assm1:"unat pc < length (a#l_bin0) \<and> unat pc \<ge> 0" and
   assm2:"jitflat_bpf (a#l_bin0) init_second_layer = (l2,l_pc2,l_jump2)" and
   assm3:"fst (l_pc2 ! (unat pc)) = xpc"
  have a0:"unat pc = 0 \<or> unat pc \<ge>1" by auto
   show ?thesis
   proof(cases "unat pc = 0")
     case True
    then show ?thesis using Cons flattern_lbin by (metis init_second_layer_def list.size(3)) 
   next
     case False
     have b0:"unat pc \<ge>1" using False a0 by simp
     let "?pc" = "unat pc -1"
      have b1:"?pc < length l_bin0 \<and> (0::nat) \<le> ?pc" 
        using assm2 b0 diff_le_self by (metis One_nat_def assm1 less_diff_conv2 list.size(4) zero_le) 
      let "?x" = "tl l_bin0"
      have b2:"l_bin0 ! ?pc = (num, off, l)" using assm0 by (simp add: False order_neq_le_trans) 
      have "l_bin0!?pc=(num,off,l) \<Longrightarrow>
   ?pc < ?pc \<and> ?pc \<ge> 0 \<Longrightarrow>
   jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow>
   fst (l_pc2 ! (unat pc)) = xpc \<Longrightarrow>
   list_in_list l (unat xpc) l2" using Cons by blast

  let "?prefix" = "take (unat pc) (a#l_bin0)"
  let "?suffix" = "drop (unat pc+1) (a#l_bin0)"
  have "?prefix@[(num,off,l)]@?suffix= (a#l_bin0)" using append_take_drop_id assm0
    by (metis (no_types, opaque_lifting) Cons_nth_drop_Suc append_eq_Cons_conv assm1 drop_0 drop_Suc_Cons drop_drop plus_1_eq_Suc self_append_conv2)  
  hence "?prefix@((num,off,l)#?suffix)= (a#l_bin0)" by simp

  hence "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf ?prefix init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf ((num,off,l)#?suffix) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" 
    using init_second_layer_def jitflat_bpf_induct3 by (metis assm2) 

  then obtain l2' l_pc2' l_jump2' where c0:"jitflat_bpf ?prefix init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf ((num,off,l)#?suffix) (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" by auto

  have c1:"jitflat_bpf ((num,off,l)#?suffix) (l2', l_pc2', l_jump2') = (
    let l_jump' = update_l_jump (num,off,l) l_pc2' l_jump2' in
        jitflat_bpf ?suffix (
          l2'@l,
          l_pc2'@[(of_nat(length l2'),num)],
          l_jump')
  )" using assm2 init_second_layer_def of_nat_def c0 using jitflat_bpf.simps(2) by presburger   

  have c2:"list_in_list l_pc2' 0 l_pc2" using not_change_prefix_l_pc c0 c1 by blast

  have c2_0:"l_pc2 \<noteq> []" using c1 sorry

  (*hence c2_1:"take (length l_pc2') l_pc2 = l_pc2'" using c2 list_in_list_prop4 by blast*)

  (*have d0:"jitflat_bpf (?prefix@[(num,off,l)]) init_second_layer = jitflat_bpf [(num,off,l)] (l2', l_pc2', l_jump2')" sorry
  have "\<exists> l2'' l_pc2'' l_jump2''. jitflat_bpf [(num,off,l)] (l2', l_pc2', l_jump2') = (l2'', l_pc2'', l_jump2'')" by auto
  then obtain l2'' l_pc2'' l_jump2'' where "jitflat_bpf [(num,off,l)] (l2', l_pc2', l_jump2') = (l2'', l_pc2'', l_jump2'')" by auto
  hence d1:"l_pc2'' = l_pc2'@[(of_nat(length l2'),num)]" using d0 by simp
  have d2:"jitflat_bpf ?suffix  (l2'', l_pc2'', l_jump2'') = (l2, l_pc2, l_jump2)" sorry
  hence d3:"list_in_list l_pc2'' 0 l_pc2" using  not_change_prefix_l_pc by blast
  hence d4:"take (length l_pc2'') l_pc2 = l_pc2''" using c2_0 using list_in_list_prop4 by blast 
  have c3:"(l_pc2 ! (unat pc)) = (of_nat(length l2'),num)" 
    using d2 d1 l_pc_length_prop by (smt (z3) Cons_nth_drop_Suc One_nat_def d3 add.right_neutral add_Suc_right assm1 assm2 c0 diff_add_inverse diff_diff_cancel init_second_layer_def length_Cons length_drop less_or_eq_imp_le list.size(3) list_in_list.simps(2) list_in_list_concat plus_nat.add_0) *)

  have c3:"(l_pc2 ! (unat pc)) = (of_nat(length l2'),num)" using c2 l_pc_length_prop
    by (smt (z3) Cons_nth_drop_Suc Suc_eq_plus1 ab_semigroup_add_class.add_ac(1) add.commute assm1 assm2 c0 c1 diff_add_inverse diff_diff_cancel init_second_layer_def length_drop less_or_eq_imp_le list.size(3) list.size(4) list_in_list.simps(2) list_in_list_concat not_change_prefix_l_pc) 
    
  have c4:"fst (l_pc2 ! (unat pc)) = (of_nat(length l2'))" using c3 by auto
  
  have c6:"list_in_list l (length l2') l2" using c0 c1 not_change_prefix_l_bin
    by (metis (mono_tags, lifting) list_in_list_concat plus_nat.add_0) 
  hence c7:"list_in_list l (unat(of_nat(length l2'))) l2" sorry
  
  have "list_in_list l (unat(fst (l_pc2 ! (unat pc)))) l2" using c7 c4 by metis 
     then show ?thesis using assm3 by force 
   qed
 qed
qed*)
(*
lemma num_corr:"jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow> map snd l_pc2 = map fst l_bin0"
(* apply(induction l_bin0 arbitrary: l2 l_pc2 l_jump2)
   apply (simp add: init_second_layer_def)
  subgoal for a l_bin0 l2 l_pc2 l_jump2 apply (simp add: init_second_layer_def)*)
proof(induction l_bin0 arbitrary: l2 l_pc2 l_jump2)
  case Nil
  then show ?case by (simp add: init_second_layer_def)
next
  case (Cons a l_bin0)
  have assms1:"jitflat_bpf (a#l_bin0) init_second_layer = (l2,l_pc2,l_jump2)" using Cons by simp
  have b0:"jitflat_bpf (a#l_bin0) init_second_layer = (
      jitflat_bpf l_bin0 (
        []@(snd(snd a)),
        []@[(0, fst a)],
        update_l_jump a [] []))" using init_second_layer_def 
    by (metis jitflat_bpf.simps(2) list.size(3) prod.exhaust_sel semiring_1_class.of_nat_0) 
  (*hence b1:"jitflat_bpf (a#l_bin0) init_second_layer = jitflat_bpf l_bin0 ((snd(snd a)),[(0, fst a)],update_l_jump a [] [])" by auto
  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf l_bin0 init_second_layer = (l2',l_pc2',l_jump2')" by (metis surj_pair)
  then obtain l2' l_pc2' l_jump2' where b2:"jitflat_bpf l_bin0 init_second_layer = (l2',l_pc2',l_jump2')" by auto

  have b3:"map snd l_pc2' = map fst l_bin0" using b2 Cons by blast*)

  have "\<exists> l2' l_pc2' l_jump2'. jitflat_bpf [a] init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" 
    using jitflat_bpf_induct assms1 by (simp add: init_second_layer_def) 
  then obtain l2' l_pc2' l_jump2' where b4:"jitflat_bpf [a] init_second_layer = (l2', l_pc2', l_jump2') \<and> 
         jitflat_bpf l_bin0 (l2', l_pc2', l_jump2') = (l2, l_pc2, l_jump2)" by auto

  have b5:"map snd l_pc2 = map fst l_bin0" using b4 Cons 


  have b2_3:"list_in_list [(0, fst a)] 0 l_pc2" using not_change_prefix_l_pc b1 by (metis assms1) 

  have b4:"(fst a)#map snd l_pc2' = map snd l_pc2" 
  have b2_4:"l_pc2!0 = (0, fst a)" using b2_3 by auto

  then show ?case sorry
qed*)

(*
lemma flattern_num_easy:
  "l_bin0!(unat pc)=(num,off,l) \<Longrightarrow>
   l_bin0 \<noteq> [] \<and> unat pc < length l \<and> unat pc \<ge> 0 \<Longrightarrow>
  jitflat_bpf l_bin0 init_second_layer = (l2,l_pc2,l_jump2) \<Longrightarrow>
  snd (l_pc2!(unat pc)) = num"
proof(induct pc arbitrary: l_bin0 num off l l2 l_pc2 l_jump2)
  case zero
  then show ?case
    by (smt (verit, ccfv_threshold) append_Nil fst_eqD init_second_layer_def jitflat_bpf.elims list_in_list.simps(2) not_change_prefix_l_pc nth_Cons_0 snd_conv unat_0) 
next
  case (suc pc)
  have assm1:"l_bin0 ! unat (1 + pc) = (num, off, l)" using suc by simp
  have assm2:"l_bin0 \<noteq> [] \<and> unat (1 + pc) < length l \<and> (0::nat) \<le> unat ((1::'a word) + pc)" using suc by simp
  have assm3:"jitflat_bpf l_bin0 init_second_layer = (l2, l_pc2, l_jump2)" using suc by simp
  
  have "l_bin0 ! unat pc = (num, off, l) \<Longrightarrow> l_bin0 \<noteq> [] \<and> unat pc < length l \<and> (0::nat) \<le> unat pc \<Longrightarrow> 
  jitflat_bpf l_bin0 init_second_layer = (l2, l_pc2, l_jump2) \<Longrightarrow> snd (l_pc2 ! unat pc) = num" using suc by auto


  have a0:"l_bin0 \<noteq> [] \<and> unat pc < length l \<and> (0::nat) \<le> unat pc"
    using assm2 by (simp add: suc.hyps(1) unatSuc)
  have "\<exists> num' off' l'. l_bin0!(unat pc)=(num',off',l') " by (metis surj_pair) 
  then obtain num' off' l' where a1:"l_bin0!(unat pc)=(num',off',l')" by auto

  have "snd (l_pc2!(unat pc)) = num'" using a1 suc assm3 a0  
  then show ?case
qed
*)

(*value "jitflat_bpf [(1, 1, [0x48,0x01,0xD8]),(1, 2, [0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8])] init_second_layer"

value "jitflat_bpf [(1, 2, [0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0xc3]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8]),(1, -3, [0x0f, 0x84, 0x00, 0x00, 0x00, 0x00])] init_second_layer"

*)
(*lemma one_step_equiv:
 (* "flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
   jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
   perir_step lt (pc,xst) = xxst \<Longrightarrow>
   fxst = xxst"*)
  assumes a0:"flat_bpf_one_step (l_bin,l_pc,l_jump) (pc, xst) = fxst" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_step lt (pc,xst) = xxst" and
   a3:"xst = Next xpc xrs xm xss"
  shows"fxst = xxst"
 (*proof-
  have "l_pc!(unat pc) = "
let "?l_bin0" = "map snd (map snd lt)"
  have a4:"l_bin = concat ?l_bin0" using a1 jitflat_bpf.simps init_second_layer_def
  have "l_bin!(unat xpc) = (0x0f::u8) \<or> l_bin!(unat xpc) \<noteq> (0x0f::u8)" by auto
  thus ?thesis
  proof(cases "l_bin!(unat xpc)  = (0x0f::u8)")
    case True
    then show ?thesis sorry
  next
    case False
    have b0:"l_bin!(unat xpc) \<noteq> (0x0f::u8)" using False by simp
    have b1:""
    then show ?thesis sorry
  qed*)
  sorry*)

lemma one_step_equiv:
  assumes a0:"flat_bpf_sem 1 (l_bin,l_pc,l_jump) (pc, xst) = fxst" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"perir_sem 1 lt (pc,xst) = xxst" and
   a3:"xst = Next xpc xrs xm xss"
  shows"fxst = xxst"
(*proof-
  let "?curr_ins" = "lt!(unat pc)"
  let "?num" = "fst ?curr_ins"
  let "?off" = "fst (snd ?curr_ins)"
  let "?l_bin0" = "snd (snd ?curr_ins)"
  have b0:"(?num, ?off, ?l_bin0) = ?curr_ins" by simp*)
  sorry


(*lemma flat_bpf_sem_induct_aux1:
 "flat_bpf_sem (m+n) x64_prog (pc, xst) = (pc',xst')\<Longrightarrow> 
  \<exists> pc1 xst1. flat_bpf_sem m x64_prog (pc, xst) = (pc1,xst1) \<and>
  flat_bpf_sem n x64_prog (pc1,xst1) = (pc',xst')"
 apply(induct m arbitrary: n x64_prog pc xst pc' xst' )
   apply auto[1]
  subgoal for m n x64_prog pc xst pc' xst'
    (*apply (simp add: Let_def)*)
    apply(cases xst;simp)
    subgoal for x11 x12 x13 x14 
    done
  done*)

lemma flat_bpf_sem_induct_aux1:
 "flat_bpf_sem (m+n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem m x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
 apply(induct m arbitrary: n x64_prog xst xst' )
   apply auto[1]
  subgoal for m n x64_prog xst xst'
    apply (simp add: Let_def)
    apply(cases xst;simp)
    done
  done

lemma flat_bpf_sem_induct_aux2:
"flat_bpf_sem (Suc n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem 1 x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
  using flat_bpf_sem_induct_aux1 by simp


lemma err_is_still_err:"perir_sem n lt (pc,Stuck) = (pc',s') \<Longrightarrow> s' = Stuck "
  apply(induct n, simp)
  using perir_step_def
  by auto

lemma intermediate_step_is_ok:"perir_sem n lt (pc,s) = s' \<Longrightarrow> n > 0 \<Longrightarrow> snd s' \<noteq> Stuck \<Longrightarrow> 
  \<exists> xpc xrs xm xss. s = (Next xpc xrs xm xss)"
  apply(induct n arbitrary: lt pc s s')
  apply simp 
  using err_is_still_err
  by (metis eq_snd_iff outcome.exhaust) 


lemma n_steps_equiv:
  "flat_bpf_sem n prog xst = fxst \<Longrightarrow>
  jitflat_bpf lt init_second_layer = prog \<Longrightarrow>
  perir_sem n lt xst = xxst \<Longrightarrow>
  snd xst = Next xpc xrs xm xss \<Longrightarrow>
  snd xxst = Next xpc' xrs' xm' xss' \<Longrightarrow>
  fxst = xxst"
proof(induct n arbitrary: prog xst fxst lt xxst xpc xrs xm xss xpc' xrs' xm' xss')
  case 0
  then show ?case by (metis flat_bpf_sem.simps(1) perir_sem.simps(1) prod.collapse)
    
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) prog xst = fxst" and 
  assm1:"jitflat_bpf lt init_second_layer = prog" and
  assm2:"perir_sem (Suc n) lt xst = xxst" and
  assm3:"snd xst = Next xpc xrs xm xss" and
  assm4:"snd xxst = Next xpc' xrs' xm' xss'"
  have "\<exists> next_s. next_s = perir_sem 1 lt xst" by simp
  then obtain next_s where b0:"next_s = perir_sem 1 lt xst" by auto
  have "\<exists> next_f. flat_bpf_sem 1 prog xst = next_f" by blast
  then obtain next_f where b1:"flat_bpf_sem 1 prog xst = next_f" by simp
  have bn:"next_s = next_f" using assm1 b0 b1 assm3 one_step_equiv 
    by (metis prod.collapse)
  have a0:"perir_sem n lt next_s = xxst" using x64_sem1_induct_aux3 assm2 b0 by blast
  have "\<exists> xrs1 xpc1 m1 xss1. snd next_s = Next xrs1 xpc1 m1 xss1" using assm4 a0 intermediate_step_is_ok a0 assm4 
    by (metis One_nat_def b0 less_SucE outcome.distinct(1) prod.collapse x64_sem1_induct_aux3 zero_less_Suc)
  then obtain xrs1 xpc1 m1 xss1 where a1:"snd next_s = Next xrs1 xpc1 m1 xss1" by auto

  have c0:"flat_bpf_sem n prog next_f = fxst" using flat_bpf_sem_induct_aux2 assm0 b1 by blast
  have c1:"snd next_f = Next xrs1 xpc1 m1 xss1" using a1 bn b0 by blast
  
  have "flat_bpf_sem n prog xst = fxst \<Longrightarrow>
    jitflat_bpf lt init_second_layer = prog \<Longrightarrow> 
    perir_sem n lt xst = xxst \<Longrightarrow> 
    snd xst = Next xpc xrs xm xss \<Longrightarrow> 
    fxst = xxst" using Suc by blast
  have "fxst = xxst" using a0 a1 c1 c1 Suc bn c0 by blast 
  then show ?case by simp
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


value "x64_encode (Pjcc Cond_e 3 )"
value "x64_encode (Pjcc Cond_e (-3) )"
value "x64_decode 0 [0x48,0x01,0xD8]"

fun jitflat :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump " where
  "jitflat [] last_comp = last_comp"| 
  "jitflat ((num,off,l_bin0)#xs) (fst_comp,snd_comp,trd_comp) = 
        (let curr_pc = of_nat (length fst_comp) in 
         (if l_bin0!0 = (0x0f::u8) then 
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

definition getIndex ::"u64 \<Rightarrow> l_pc \<Rightarrow> nat" where
  "getIndex pc snd_comp \<equiv> SOME place. snd_comp!place = pc"

definition getPair ::"nat \<Rightarrow> l_jump \<Rightarrow> (location\<times>target_pc)" where
  "getPair idx thrd_comp \<equiv> SOME pair. pair \<in> set thrd_comp \<and> fst pair = of_nat idx"

fun x64_sem2::"nat \<Rightarrow> x64_bin \<times> l_pc \<times> l_jump \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
 "x64_sem2 0 _ st = st" |
 "x64_sem2 (Suc n) (lt,snd_comp,thrd_comp) (pc,xst) = 
   (let xst' = (if lt!(unat pc) = 0x0f then 
                    case xst of Stuck \<Rightarrow> Stuck |
                                Next xpc xrs xm \<Rightarrow>
                                    let place = getIndex pc snd_comp;
                                        pair = getPair place thrd_comp;
                                        target_idx = snd pair;
                                        target_place = snd_comp !(unat target_idx) in
                                    Next target_place xrs xm 
                else x64_sem 1 lt xst) in
   let off = (case xst' of Stuck \<Rightarrow> pc |
                           Next pc' rs' m' \<Rightarrow> pc') in
   x64_sem2 n (lt,snd_comp,thrd_comp) (off,xst'))"




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
                              offset = (scast (target_begin_addr)::i32) - (scast(fix_begin_addr+6)::i32);
                              u8_list = u8_list_of_i32 offset;
                              l' = x64_bin_update l (unat (fix_begin_addr+2)) u8_list in 
                          jitfix xs l' pcs)"


value "jitfix [(1::64 word, 3::64 word)] 
  [72::8 word, 1::8 word, 216::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word] 
  [0::64 word, 3::64 word, 9::64 word, 12::64 word]"

value "jitfix [(0::64 word, 2::64 word), (4::64 word, 1::64 word)] 
  [15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 195::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word, 15::8 word, 132::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word] 
  [0::64 word, 6::64 word, 7::64 word, 10::64 word, 13::64 word]"
(*value "jitfix [(1::64 word, 3::64 word)]
  [72::8 word, 1::8 word, 216::8 word, 233::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word]
  [0::64 word, 3::64 word, 8::64 word, 11::64 word]"

value "jitfix [(0::64 word, 2::64 word), (4::64 word, 1::64 word)]
[233::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word, 195::8 word, 72::8 word, 1::8 word, 216::8 word, 72::8 word, 1::8 word, 216::8 word, 233::8 word, 0::8 word, 0::8 word, 0::8 word, 0::8 word]
[0::64 word, 5::64 word, 6::64 word, 9::64 word, 12::64 word]  "*)




(*
fun x64_sem2::"nat \<Rightarrow> x64_bin \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
 "x64_sem2 0 _ st = st" |
 "x64_sem2 (Suc n) lt (pc,xst) = 
  (let xst' = x64_sem 1 lt xst;
   off = (case xst' of Stuck \<Rightarrow> pc |
                Next pc' rs' m' \<Rightarrow> pc') in
    x64_sem2 n lt (off,xst'))"
*)

lemma refinement_relation_of_two_layers:
  "snd st = Next pc rs m \<Longrightarrow>
  perir_sem n x64_prog st = st1 \<Longrightarrow>
  snd st1 = Next pc' rs' m' \<Longrightarrow>
  (l_bin0, pc_info, jump_info) = jitflat x64_prog init_second_layer \<Longrightarrow>
  jitfix jump_info l_bin0 pc_info = x64_prog2 \<Longrightarrow>
  x64_sem2 n x64_prog2 st = st2 \<Longrightarrow>
  st1 = st2"
  sorry
                   
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


                              
*)

end