theory JITFlat

imports JITPer_aux JITPer
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


fun jitflat_bpf :: "(nat \<times> u64 \<times> x64_bin) list \<Rightarrow> flat_bpf_prog \<Rightarrow> flat_bpf_prog" where
"jitflat_bpf [] st = st"| 
"jitflat_bpf ((num,off,l_bin0)#xs) (l_bin,l_pc,l_jump) = (
      jitflat_bpf xs (l_bin@l_bin0, l_pc@[(of_nat (length l_bin),num)],if l_bin0!0 = (0x0f::u8) then l_jump@ [(of_nat (length l_pc), of_nat (length l_pc) + off)]
                   else l_jump)
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
        if l_bin!(unat xpc+1) = (0x39::u8) then \<comment>\<open> TODO: if the first byte is the opcode of cmp? \<close>
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

fun flat_bpf_sem :: "nat \<Rightarrow> flat_bpf_prog \<Rightarrow> hybrid_state \<Rightarrow> hybrid_state" where
"flat_bpf_sem 0 _ hst = hst" |
"flat_bpf_sem (Suc n) (l_bin,l_pc,l_jump) (pc, xst) = (
  let (xpc, num) = l_pc!(unat pc) ;
   (npc, nxst) = flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) in
  flat_bpf_sem n (l_bin,l_pc,l_jump) (npc, nxst)
)"

value "jitflat_bpf [(1, 1, [0x48,0x01,0xD8]),(1, 2, [0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8])] init_second_layer"

value "jitflat_bpf [(1, 2, [0x0f, 0x84, 0x00, 0x00, 0x00, 0x00]), (1, 1, [0xc3]), (1, 1, [0x48,0x01,0xD8]), (1, 1, [0x48,0x01,0xD8]),(1, -3, [0x0f, 0x84, 0x00, 0x00, 0x00, 0x00])] init_second_layer"


lemma 
  "l_bin!pc=(num,off,l) \<Longrightarrow>
  jitflat_bpf l_bin (l1,l_pc1,l_jump1) = (l2,l_pc2,l_jump2) \<Longrightarrow>
  fst (l_pc2 ! (length l_pc1 + pc) ) = xpc \<Longrightarrow>
  list_in_list l (length l1 + unat xpc) l2"

lemma one_step_equiv:
 (* "flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
   jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
   one_step lt (pc,xst) = xxst \<Longrightarrow>
   fxst = xxst"*)
  assumes a0:"flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"one_step lt (pc,xst) = xxst" and
   a3:"xst = Next xpc xrs xm"
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
  sorry



lemma flat_bpf_sem_induct_aux1:
 "flat_bpf_sem (m+n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem m x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
 apply(induct m arbitrary: n x64_prog xst xst' )
   apply auto[1]
  subgoal for m n x64_prog xst xst'
    apply (simp add: Let_def)
    apply(cases xst;simp)
    subgoal for a b sorry
    done
  done

lemma flat_bpf_sem_induct_aux2:
"flat_bpf_sem (Suc n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. flat_bpf_sem 1 x64_prog xst = xst1 \<and>
  flat_bpf_sem n x64_prog xst1 = xst'"
  using flat_bpf_sem_induct_aux1 by simp



lemma one_step_equiv:
 (* "flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst \<Longrightarrow>
   jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump) \<Longrightarrow>
   one_step lt (pc,xst) = xxst \<Longrightarrow>
   fxst = xxst"*)
  assumes a0:"flat_bpf_one_step xpc num (l_bin,l_pc,l_jump) (pc, xst) = fxst" and
   a1:"jitflat_bpf lt init_second_layer = (l_bin,l_pc,l_jump)" and
   a2:"one_step lt (pc,xst) = xxst" and
   a3:"xst = Next xpc xrs xm"
 shows"fxst = xxst"
  sorry



lemma n_steps_equiv:
  "flat_bpf_sem n prog xst = fxst \<Longrightarrow>
  jitflat_bpf lt init_second_layer = prog \<Longrightarrow>
  x64_sem1 n lt xst = xxst \<Longrightarrow>
  snd xst = Next xpc xrs xm \<Longrightarrow>
  fxst = xxst"
proof(induct n)
  case 0
  then show ?case 
    by (metis flat_bpf_sem.simps(1) prod.collapse x64_sem1.simps(1))
next
  case (Suc n)
  assume assm0:"flat_bpf_sem (Suc n) prog xst = fxst" and 
  assm1:"jitflat_bpf lt init_second_layer = prog" and
  assm2:"x64_sem1 (Suc n) lt xst = xxst" and
  assm3:"snd xst = Next xpc xrs xm"
  have "\<exists> next_s. next_s = one_step lt xst" by simp
  then obtain next_s where b0:"next_s = one_step lt xst" by auto
  have "\<exists> next_f num. flat_bpf_one_step xpc num prog xst = next_f" by blast
  then obtain next_f num where b1:"flat_bpf_one_step xpc num prog xst = next_f" by simp
  have bn:"next_s = next_f" using  assm1 b0 b1 assm3 one_step_equiv 
    by (metis prod.collapse)
  have "\<exists> xrs1 xpc1 m1. snd next_s = Next xrs1 xpc1 m1" sorry
  then obtain xrs1 xpc1 m1 where b2:"snd next_s = Next xrs1 xpc1 m1" by auto

  have "flat_bpf_sem n prog xst = fxst" using flat_bpf_sem_induct_aux2 assm0 b1 sorry
  
  have "flat_bpf_sem n prog xst = fxst \<Longrightarrow>
    jitflat_bpf lt init_second_layer = prog \<Longrightarrow> 
    x64_sem1 n lt xst = xxst \<Longrightarrow> 
    snd xst = Next xpc xrs xm \<Longrightarrow> 
    fxst = xxst" using Suc by blast
  have "fxst = xxst" using x64_sem1_induct_aux3 flat_bpf_sem_induct_aux1 bn Suc b2 
  then show ?case sorry
qed



end