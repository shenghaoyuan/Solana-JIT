theory JITFlattern_prob
  imports JITFlattern_def JITFlattern_aux
begin 
 (*l!x \<noteq> 0xe8 \<and> l!x \<noteq> 0xc3 \<and> l!(x+1) \<noteq> (0x39::u8) \<Longrightarrow>*)
lemma list_in_list_prop3:"x64_sem num l_bin (Next (xpc+x) xrs xm xss) = fxst \<Longrightarrow>
   x64_sem num l (Next x xrs xm xss) = xxst \<Longrightarrow>
   list_in_list l xpc l_bin \<Longrightarrow>
   xxst \<noteq> Stuck \<Longrightarrow>
   match_state1 xxst fxst"
proof(induction num arbitrary:l_bin xpc x xrs xm xss fxst l xrs xm xss xxst)
  case 0
  then show ?case using match_state1_def by auto
next
  case (Suc num)
  assume assm0:"x64_sem (Suc num) l_bin (Next (xpc+x) xrs xm xss) = fxst" and
      assm1:"x64_sem (Suc num) l (Next x xrs xm xss) = xxst" and
      assm2:"list_in_list l xpc l_bin" and
      assm3:"xxst \<noteq> Stuck" 
      (*and assm4:"l!x \<noteq> 0xe8 \<and> l!x \<noteq> 0xc3 \<and> l!(x+1) \<noteq> (0x39::u8)"*)

  have "x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) = 
              (case x64_decode (xpc+x) l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem 0 l_bin (exec_instr ins sz (xpc+x) xrs xm xss))" by simp
  hence b0:"x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) = 
              (case x64_decode (xpc+x) l_bin of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             (exec_instr ins sz (xpc+x) xrs xm xss))"
    using x64_sem.simps(1) by presburger 

  have "x64_sem 1 l (Next x xrs xm xss) = 
              (case x64_decode x l of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             x64_sem 0 l (exec_instr ins sz x xrs xm xss))" by simp
  hence d0:"x64_sem 1 l (Next x xrs xm xss) = 
              (case x64_decode x l of
                None \<Rightarrow> Stuck |
                Some (sz, ins) \<Rightarrow>
             (exec_instr ins sz x xrs xm xss))"
    using x64_sem.simps(1) by presburger  

  hence "x64_decode x l \<noteq> None" using d0
    by (metis Suc.prems(2) assm3 option.simps(4) x64_sem.simps(3)) 
  hence a0:"x64_decode x l = x64_decode (xpc+x) l_bin"  
   using assm2 list_in_list_prop2 by force

  have d1_0:"x64_sem 1 l (Next x xrs xm xss) \<noteq> Stuck" 
    using assm3 assm1 by (metis err_is_still_err2 plus_1_eq_Suc x64_sem_add) 
  hence d1_1:"x64_decode x l \<noteq> None" using d0 by(cases "x64_decode x l",simp_all)
  hence "\<exists> sz ins. x64_decode x l = Some (sz,ins)" by simp
  then obtain sz ins where d1_2:"x64_decode x l = Some (sz,ins)" by auto
  hence d1:"x64_sem 1 l (Next x xrs xm xss) = (exec_instr ins sz x xrs xm xss)" 
    using d0 by fastforce 

  hence "\<exists> xpc'' xrs'' xm'' xss''. exec_instr ins sz x xrs xm xss = Next xpc'' xrs'' xm'' xss''" 
    using d1 outcome.exhaust d1_0 by metis
  then obtain xpc'' xrs'' xm'' xss'' where d2:"exec_instr ins sz x xrs xm xss = Next xpc'' xrs'' xm'' xss''" by auto

  have b1:"x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) = (exec_instr ins sz (xpc+x) xrs xm xss)"
    using d1_1 d1_2 b0 a0 by simp
  (* have "x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) \<noteq> Stuck" using intermediate_step_is_ok2 sorry*)
  thus ?case
  proof(cases "x64_sem 1 l_bin (Next (xpc+x) xrs xm xss) \<noteq> Stuck")
    case True
    hence "\<exists> xpc' xrs' xm' xss'. exec_instr ins sz (xpc+x) xrs xm xss = Next xpc' xrs' xm' xss'"
       using b1 outcome.exhaust by metis
    then obtain xpc' xrs' xm' xss' where b2:"exec_instr ins sz (xpc+x) xrs xm xss = Next xpc' xrs' xm' xss'" by auto
            (*xpc' = xpc1 + sz \<and> xpc'' = 0 + sz \<and> *)
    have a1:"xrs'' = xrs' \<and> xm'' = xm' \<and> xss'' = xss'"
              using b2 d2 apply(unfold exec_instr_def)
              apply(cases ins,simp_all)
              subgoal for x7 apply(unfold exec_push_def Let_def)
                apply(cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR x7)))",simp_all)
                done
              subgoal for x8 apply(unfold exec_pop_def Let_def)
                apply(cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))",simp_all)
                subgoal for a apply(cases a,simp_all)
                  done
                done
              subgoal for x131 x132 apply(cases "eval_testcond x131 xrs",simp_all)
                subgoal for a 
                  by (metis outcome.inject) 
                done
              subgoal for x151 x152 x153
                apply(unfold exec_store_def,simp_all)
                apply(cases "storev x153 xm (Vlong (eval_addrmode64 x151 xrs)) (Vlong (xrs (IR x152)))",simp_all)
                done
              subgoal for x201 x202 x203 
                apply(unfold exec_load_def,simp_all)
                apply(cases "loadv x203 xm (Vlong (eval_addrmode64 x202 xrs))",simp_all)
                subgoal for a apply(cases a,simp_all)
                  done
                done
              subgoal for x21a 
                apply(unfold exec_call_def,simp_all)
                done
              done

    have a2:"xpc'' = x + sz \<and> xpc'= xpc + x + sz" sorry
  
    let "?x" = "sz+x"
  
    have a3:"match_state1 (Next ?x xrs' xm' xss') (Next (?x + xpc) xrs' xm' xss')"
      using a1 apply(unfold match_state1_def)
      apply(cases "Next ?x xrs' xm' xss'",simp_all)
      done
  
    (*hence a4:"match_state1 (x64_sem 1 l (Next x xrs xm xss)) (x64_sem 1 l_bin (Next (xpc+x) xrs xm xss))" sorry*)
  
    have "x64_sem num l_bin (Next (xpc+x) xrs xm xss) = fxst \<Longrightarrow> 
    x64_sem num l (Next x xrs xm xss) = xxst \<Longrightarrow> 
    list_in_list l xpc l_bin \<Longrightarrow> 
    match_state1 xxst fxst" using Suc by simp
  
    have a5:"x64_sem num l_bin (Next (xpc+?x) xrs' xm' xss') = fxst" 
      using a2 a1
      by (metis Suc.prems(1) ab_semigroup_add_class.add_ac(1) add.commute b1 b2 plus_1_eq_Suc x64_sem_add) 
    have a6:"x64_sem num l (Next ?x xrs' xm' xss') = xxst" using a1 a2
      by (metis Suc.prems(2) add.commute d1 d2 plus_1_eq_Suc x64_sem_add) 
    have "match_state1 xxst fxst" using a6 a5 assm2 Suc by blast
    then show ?thesis by simp
  next
    case False
    have "exec_instr ins sz (xpc+x) xrs xm xss = Stuck" using b1 False by simp
    hence "exec_instr ins sz x xrs xm xss = Stuck" 
       apply(unfold exec_instr_def)
       apply(cases ins,simp_all)
       subgoal for x7 apply(unfold exec_push_def Let_def)
         apply(cases "storev M64 xm (Vptr sp_block (xrs (IR SP) - u64_of_memory_chunk M64)) (Vlong (xrs (IR x7)))",simp_all)
           done
       subgoal for x8 apply(unfold exec_pop_def Let_def)
         apply(cases "loadv M64 xm (Vptr sp_block (xrs (IR SP)))",simp_all)
         subgoal for a apply(cases a,simp_all)
         done
       done
       subgoal for x131 x132 apply(cases "eval_testcond x131 xrs",simp_all)
          subgoal for a by (metis outcome.distinct(1))          
          done
          subgoal for x151 x152 x153
            apply(unfold exec_store_def,simp_all)
            apply(cases "storev x153 xm (Vlong (eval_addrmode64 x151 xrs)) (Vlong (xrs (IR x152)))",simp_all)
          done
          subgoal for x201 x202 x203 
            apply(unfold exec_load_def,simp_all)
            apply(cases "loadv x203 xm (Vlong (eval_addrmode64 x202 xrs))",simp_all)
            subgoal for a apply(cases a,simp_all)
            done
          done
          subgoal for x21a 
            apply(unfold exec_call_def,simp_all)
            done
          done
    then show ?thesis using d2 by simp 
  qed
qed

lemma not_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l \<noteq> Some(1,Pret)"
  sorry

lemma not_call_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xe8 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<forall> d. x64_decode pc l \<noteq> Some(5, Pcall_i d)"
  sorry

lemma not_cmp_insn:"l\<noteq>[] \<Longrightarrow> l!(pc+1) \<noteq> 0x39 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> \<forall> src dst. x64_decode pc l \<noteq> Some(3, Pcmpq_rr src dst)"
  sorry

(*
lemma not_ret_insn:"l\<noteq>[] \<Longrightarrow> l!pc \<noteq> 0xc3 \<Longrightarrow> x64_decode pc l \<noteq> None \<Longrightarrow> x64_decode pc l \<noteq> Some(1,Pret)"
  apply(unfold x64_decode_def Let_def)
  apply(split if_splits,simp_all)+
      apply(cases "u32_of_u8_list [137::8 word, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)

       apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
  subgoal for a
apply rule+
      apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (4::8 word) (and (1::8 word) (l ! pc >> (2::nat))))",simp_all)
    apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
    subgoal for aa
    apply rule+
  apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
apply rule+
     apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word)) ",simp_all)
apply rule+
      apply(cases "u32_of_u8_list [1::8 word, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)
      done
    done
subgoal for a
apply rule+
     apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word)) ",simp_all)
apply rule+
      apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
     apply rule+

      apply(cases " u32_of_u8_list [137::8 word, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))]",simp_all)

    apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
  
  apply(cases "u32_of_u8_list [l ! Suc pc, l ! Suc (Suc pc), l ! (pc + (3::nat)), l ! (pc + (4::nat))] ",simp_all)
  
  apply(cases "ireg_of_u8 (bitfield_insert_u8 (3::nat) (Suc (0::nat)) (and (7::8 word) (l ! pc)) (0::8 word))",simp_all)
  subgoal for aa  
     apply(split if_splits,simp_all)+
  sorry

*)

lemma list_in_list_implies_set_relation:"list_in_list [x] pos l_jump \<Longrightarrow>  x \<in> set l_jump" 
  sorry
end
