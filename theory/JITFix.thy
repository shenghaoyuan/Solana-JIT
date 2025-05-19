theory JITFix
  imports JITFlattern
begin

definition x64_bin_update ::"x64_bin \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> x64_bin " where
 "x64_bin_update l pc u8_list \<equiv>  ( let l1 = list_update l pc (u8_list!0);
                                       l2 = list_update l1 (pc+1) (u8_list!1);
                                       l3 = list_update l2 (pc+2) (u8_list!2);   
                                       l4 = list_update l3 (pc+3) (u8_list!3) in l4)"
(*input: l_jump x64_bin l_pc*)
fun jitfix :: "((u64\<times>u64) list) \<Rightarrow> x64_bin \<Rightarrow> (u64 \<times> nat) list \<Rightarrow> x64_bin" where
  "jitfix [] l _  = l" |
  "jitfix (x#xs) l l_pc = (let (fix_begin_addr,num1) = l_pc!(unat (fst x)); 
                              (target_begin_addr,num2) = l_pc!(unat (snd x));
                              offset = (scast (target_begin_addr)::i32) - (scast(fix_begin_addr+6)::i32);
                              u8_list = u8_list_of_i32 offset;
                              l' = x64_bin_update l (unat (fix_begin_addr+2)) u8_list in 
                          jitfix xs l' l_pc)"


(*
fun jitfix :: "((u64\<times>u64) list) \<Rightarrow> x64_bin \<Rightarrow> (u64 \<times> nat) list \<Rightarrow> x64_bin" where
  "jitfix [] _ _  = []" |
  "jitfix (x#xs) l l_pc = (let (place_end,num1) = l_pc!(unat (fst x)); (addr_begin,num2) = l_pc!(unat (snd x-1));
                              u8_list = u8_list_of_u32 ((ucast addr_begin)::u32);
                              l' = x64_bin_update l (unat (place_end-3)) u8_list in 
                          jitfix xs l' l_pc)"
*)

(*
fun jit_fix_sem::"nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
 "jit_fix_sem 0 _ st = st" |
 "jit_fix_sem (Suc n) lt xst = 
  (let xst' = x64_sem 1 lt xst in 
   (case xst' of Stuck \<Rightarrow> Stuck |
                 Next pc' rs' m' ss' \<Rightarrow> 
    jit_fix_sem n lt xst'))"*)

(*
fun jit_fix_sem::" nat \<Rightarrow> nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
 "jit_fix_sem 0 _ _ st = st" |
 "jit_fix_sem (Suc n) num lt xst = 
  (let xst' = x64_sem 1 lt xst in 
   (case xst' of Stuck \<Rightarrow> Stuck |
                 Next pc' rs' m' ss' \<Rightarrow> 
    if pc' = num then xst' else 
    jit_fix_sem n num lt xst'))"
*)

definition jit_fix_sem::"nat \<Rightarrow> x64_bin \<Rightarrow> outcome \<Rightarrow> outcome" where
  "jit_fix_sem n lt xst = x64_sem n lt xst"

lemma one_steps_equiv_layer2:
  "flat_bpf_sem 1 (l_bin0,l_pc,l_jump) (pc,xst) = fxst' \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = prog \<Longrightarrow>
  num = snd (l_pc!(unat pc)) \<Longrightarrow> 
  jit_fix_sem num prog xst = fst' \<Longrightarrow>
  match_state1 fst' (snd fxst')"
  sorry


(*(l_bin0,l_pc,l_jump) *)
lemma n_steps_equiv_layer2:
  "flat_bpf_sem n (l_bin0,l_pc,l_jump) (pc,xst) = fxst' \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>
  jitfix l_jump l_bin0 l_pc = prog \<Longrightarrow>
  jit_fix_sem n prog xst = fst' \<Longrightarrow>
  match_state1 fst' (snd fxst')"
  sorry


lemma n_steps_equiv:
  "perir_sem n lt (pc,xxst) = xxst' \<Longrightarrow>
  xxst = Next xpc xrs xm xss \<Longrightarrow>
  snd xxst' = Next xpc' xrs' xm' xss' \<Longrightarrow>
  match_state (pc,xxst) (pc,fxst) \<Longrightarrow>
  lt \<noteq> [] \<Longrightarrow> 
  well_formed_prog lt \<Longrightarrow>

  jitflat_bpf lt init_second_layer = (l_bin0,l_pc,l_jump) \<Longrightarrow>
  flat_bpf_sem n (l_bin0,l_pc,l_jump) (pc,fxst) = fxst' \<Longrightarrow>
  snd fxst' = Next xpc'' xrs'' xm'' xss'' \<Longrightarrow>

  jitfix l_jump l_bin0 l_pc = prog \<Longrightarrow>
  jit_fix_sem n prog xst = fst' \<Longrightarrow>
  match_state1 fst' (snd xxst')"
  sorry

end