theory JITFlattern_aux_well_formed
  imports JITPer_aux JITFlattern_def
begin

lemma jit_prog_prop1:"per_jit_ins ins \<noteq> None \<Longrightarrow>
  \<exists> num off l_bin0. per_jit_ins ins = Some (num,off,l_bin0) \<and> num > 0 "
  apply(unfold per_jit_ins_def )
  apply(unfold per_jit_load_reg64_def per_jit_add_reg64_1_def per_jit_add_imm64_1_def  per_jit_sub_reg64_1_def per_jit_mov_reg64_1_def 
per_jit_or_reg64_1_def per_jit_and_reg64_1_def per_jit_xor_reg64_1_def per_jit_mul_reg64_def per_jit_jcc_def per_jit_shift_lsh_reg64_def per_jit_shift_rsh_reg64_def
per_jit_shift_arsh_reg64_def per_jit_load_reg64_def  per_jit_store_reg64_def per_jit_call_reg_def per_jit_exit_def Let_def)
 apply(cases ins,simp_all)
  subgoal for x31 x32 x33 x34
    by(cases x33,simp_all)
  subgoal for x91 x92 x93 
    apply(cases x91,simp_all)
             apply(cases x93,simp_all)
            apply(cases x93,simp_all)
    apply(cases x93,simp_all)
    subgoal for x2 by(cases "bpf_to_x64_reg x92",simp_all)
          apply(cases x93,simp_all)
         apply(cases x93,simp_all)
        apply(cases x93,simp_all)
    subgoal for x2 apply(cases "bpf_to_x64_reg x92",simp_all)
      by(cases "bpf_to_x64_reg x2",simp_all)
       apply(cases x93,simp_all)
    subgoal for x2 apply(cases "bpf_to_x64_reg x92",simp_all) 
      by(cases "bpf_to_x64_reg x2",simp_all)
      apply(cases x93,simp_all)
     apply(cases x93,simp_all)
    apply(cases x93,simp_all)
    subgoal for x2 apply(cases "bpf_to_x64_reg x92",simp_all)  
      by(cases "bpf_to_x64_reg x2",simp_all)
    done
  subgoal for x161 x162 x163 x164
    apply(cases x163,simp_all)
    subgoal for x2 apply(cases x161,simp_all)
      by (metis option.discI) 
    done
  done

(*lemma jit_prog_prop2:"per_jit_ins ins = Some (num,off,l_bin0) \<Longrightarrow> \<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst) \<Longrightarrow> l_bin0\<noteq>[] \<Longrightarrow> num = 1"*)
lemma jit_prog_prop3:
  "jitper insns = Some lt \<Longrightarrow> 
  lt \<noteq> [] \<Longrightarrow>
  lt!(unat pc) = (num,off,l_bin0) \<Longrightarrow> 
  unat pc < length lt \<and> unat pc \<ge> 0 \<Longrightarrow> 
  num > 0"
  sorry

lemma jit_prog_prop2:"per_jit_ins ins = Some (num,off,l_bin0) \<Longrightarrow> \<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst) \<Longrightarrow>  num = 1"
  using x64_encode_decode_consistency 
  apply(unfold per_jit_ins_def,simp_all)
apply(unfold per_jit_load_reg64_def per_jit_add_reg64_1_def per_jit_add_imm64_1_def  per_jit_sub_reg64_1_def per_jit_mov_reg64_1_def 
per_jit_or_reg64_1_def per_jit_and_reg64_1_def per_jit_xor_reg64_1_def per_jit_mul_reg64_def per_jit_jcc_def per_jit_shift_lsh_reg64_def per_jit_shift_rsh_reg64_def
per_jit_shift_arsh_reg64_def per_jit_load_reg64_def  per_jit_store_reg64_def per_jit_call_reg_def per_jit_exit_def Let_def)
  apply(cases ins,simp_all)
     prefer 4
  subgoal for x161 x162 x163 x164
    apply(cases x163,simp_all)
    subgoal for x2
      apply(cases x161,simp_all)
      apply(split if_splits,simp_all)
      done
    done

  subgoal for x21 x22 x23 x24
    apply(subgoal_tac "x64_decode 0 l_bin0 = Some (12,Pmovl_ri REG_SCRATCH (scast x24))")
     apply auto[1]
    apply(subgoal_tac "list_in_list (x64_encode (Pmovl_ri REG_SCRATCH (scast x24))) 0 l_bin0",simp_all)
    by (metis append.left_neutral list.size(3) list_in_list_prop_aux2)

  subgoal for x31 x32 x33 x34
    apply(cases x33,simp_all)
    subgoal for x2
      apply(subgoal_tac "x64_decode 0 l_bin0 = Some (12,Pmovl_ri REG_SCRATCH (scast x34))")
       apply auto[1]
apply(subgoal_tac "list_in_list (x64_encode (Pmovl_ri REG_SCRATCH (scast x34))) 0 l_bin0",simp_all)
      by (metis append.left_neutral list.size(3) list_in_list_prop_aux2)
    done

  subgoal for x91 x92 x93
    apply(cases x91,simp_all)
             apply(cases x93,simp_all)
    subgoal for x1
apply(subgoal_tac "x64_decode 0 l_bin0 = Some (12,Pmovl_ri REG_OTHER_SCRATCH (scast x1))")
      apply auto[1]
apply(subgoal_tac "list_in_list (x64_encode (Pmovl_ri REG_OTHER_SCRATCH (scast x1))) 0 l_bin0",simp_all)
      by (metis append.left_neutral list.size(3) list_in_list_prop_aux2)

            apply(cases x93,simp_all)
           defer 
           apply(cases x93,simp_all)
          apply(cases x93,simp_all)
         prefer 3 apply(cases x93,simp_all)
        prefer 3 apply(cases x93,simp_all)
           apply(cases x93,simp_all)
    subgoal for x2
      apply(cases "bpf_to_x64_reg x92",simp_all)
                     apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)
                     apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                    apply (meson list_in_list_concat list_in_list_prop)
                   apply(cases "bpf_to_x64_reg x2",simp_all)
                          apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RAX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RAX)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RBX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RBX)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RDX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RDX)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RSI)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RSI)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)

            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RDI)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RDI)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
                          apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RBP)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RBP)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r SP)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r SP)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R8)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R8)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R9)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R9)) 0 l_bin0",simp_all)
                         apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r REG_OTHER_SCRATCH)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r REG_OTHER_SCRATCH)) 0 l_bin0",simp_all)
                        apply (meson list_in_list_concat list_in_list_prop)
        apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r REG_SCRATCH)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r REG_SCRATCH)) 0 l_bin0",simp_all)
                       apply (meson list_in_list_concat list_in_list_prop)
        apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R12)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R12)) 0 l_bin0",simp_all)
                      apply (meson list_in_list_concat list_in_list_prop)

   apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R13)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R13)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R14)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R14)) 0 l_bin0",simp_all)
                    apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R15)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R15)) 0 l_bin0",simp_all)
                   apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                  apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
      done
      apply(cases x93,simp_all)
    subgoal for x2
      apply(cases "bpf_to_x64_reg x92",simp_all)
apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)
apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
      apply (meson list_in_list_concat list_in_list_prop)
                   apply(cases "bpf_to_x64_reg x2",simp_all)
  apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RAX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RAX)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RBX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RBX)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RDX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RDX)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RSI)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RSI)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)

            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RDI)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RDI)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
                          apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RBP)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RBP)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r SP)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r SP)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R8)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R8)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R9)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R9)) 0 l_bin0",simp_all)
                         apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r REG_OTHER_SCRATCH)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r REG_OTHER_SCRATCH)) 0 l_bin0",simp_all)
                        apply (meson list_in_list_concat list_in_list_prop)
        apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r REG_SCRATCH)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r REG_SCRATCH)) 0 l_bin0",simp_all)
                       apply (meson list_in_list_concat list_in_list_prop)
        apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R12)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R12)) 0 l_bin0",simp_all)
                      apply (meson list_in_list_concat list_in_list_prop)

   apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R13)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R13)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R14)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R14)) 0 l_bin0",simp_all)
                    apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R15)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R15)) 0 l_bin0",simp_all)
                   apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                  apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
      done
 apply(cases x93,simp_all)
    subgoal for x2
      apply(cases "bpf_to_x64_reg x92",simp_all)
apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)
apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
      apply (meson list_in_list_concat list_in_list_prop)
                   apply(cases "bpf_to_x64_reg x2",simp_all)
  apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RAX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RAX)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RBX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RBX)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RDX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RDX)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RSI)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RSI)) 0 l_bin0",simp_all)
                     apply (meson list_in_list_concat list_in_list_prop)

            apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RDI)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RDI)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
                          apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RBP)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RBP)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r SP)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r SP)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R8)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R8)) 0 l_bin0",simp_all)
                          apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R9)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R9)) 0 l_bin0",simp_all)
                         apply (meson list_in_list_concat list_in_list_prop)
              apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r REG_OTHER_SCRATCH)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r REG_OTHER_SCRATCH)) 0 l_bin0",simp_all)
                        apply (meson list_in_list_concat list_in_list_prop)
        apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r REG_SCRATCH)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r REG_SCRATCH)) 0 l_bin0",simp_all)
                       apply (meson list_in_list_concat list_in_list_prop)
        apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R12)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R12)) 0 l_bin0",simp_all)
                      apply (meson list_in_list_concat list_in_list_prop)

   apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R13)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R13)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R14)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R14)) 0 l_bin0",simp_all)
                    apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r R15)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r R15)) 0 l_bin0",simp_all)
                   apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
                  apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)

           apply(subgoal_tac "x64_decode 0 l_bin0 = Some (1,Ppushl_r RCX)")
                      apply auto[1]
                     apply(subgoal_tac "list_in_list (x64_encode (Ppushl_r RCX)) 0 l_bin0",simp_all)
        apply (meson list_in_list_concat list_in_list_prop)
      done
    apply(cases x93,simp_all)
    subgoal for x2
      apply(cases "bpf_to_x64_reg x92",simp_all)
      apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                     apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                    apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                   apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                  apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                 apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
               apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
              apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
             apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
            apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
           apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
          apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
         apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
        apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
       apply (meson list_in_list_concat list_in_list_prop)
 apply(subgoal_tac "x64_decode 0 l_bin0 = Some (3,Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))")
       apply auto[1]
      apply(subgoal_tac "list_in_list (x64_encode (Pmovq_rr REG_SCRATCH (bpf_to_x64_reg x2))) 0 l_bin0",simp_all)                   
                     apply (meson list_in_list_concat list_in_list_prop)
      done
    done
  done



lemma jit_prog_prop4:
  "jitper insns = Some lt \<Longrightarrow> 
  lt!(unat pc) = (num,off,l_bin0) \<Longrightarrow> 
  unat pc < length lt \<and> unat pc \<ge> 0 \<Longrightarrow> 
  \<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst) \<Longrightarrow> 
  num = 1"

  proof(induct lt arbitrary:insns pc num off l_bin0)
    case Nil
    then show ?case by simp
  next
    case (Cons a lt)
    assume assm0: "jitper insns = Some (a#lt)" and
      assm1:"(a#lt)!(unat pc) = (num,off,l_bin0)" and
      assm2:"unat pc < length (a#lt) \<and> unat pc \<ge> 0" and
      assm3:"\<exists> src dst. x64_decode 0 l_bin0 = Some(3, Pcmpq_rr src dst)"
    have a0:"unat pc = 0 \<or> unat pc \<ge> 1" by auto
    show ?case
    proof (cases "unat pc = 0")
      case True
      have b0:"\<exists> ins. per_jit_ins ins = Some a" using Cons
        by (smt (verit) True aux5 is_none_code(2) is_none_simps(1) jitper.elims length_greater_0_conv list.simps(3) nth_Cons_0 option.inject option.split_sel) 
      then obtain ins where b1:"per_jit_ins ins = Some a" by auto
      then show ?thesis using jit_prog_prop2
        using True assm3 local.Cons(3) by auto 
    next
      case False
      let "?pc" = "unat pc -1"
      have b0:"unat pc \<ge> 1" using False a0 by simp     
      hence b1:"0 \<le> ?pc \<and> ?pc < length lt \<and> lt!(?pc) = (num,off,l_bin0)"
        by (metis (no_types, lifting) False One_nat_def assm1 assm2 less_diff_conv2 list.size(4) nth_Cons' zero_le) 
      have b2_1:"insns \<noteq> []" using assm0 by force
      let "?ins" = "hd insns"
      have b2:"per_jit_ins ?ins = Some a" using assm0 b2_1
        by (metis (no_types, lifting) aux5 is_none_code(2) is_none_simps(1) jitper.elims length_greater_0_conv list.sel(1) nth_Cons_0 option.collapse option.simps(4) unsigned_0 zero_order(1)) 
      let "?prog" = "tl insns"
      have b2_2:"?ins#?prog = insns" by (simp add: b2_1) 
      have "jitper ?prog = Some lt" using assm0 b2_1 b2 apply(cases "per_jit_ins ?ins",simp_all) apply(cases "jitper ?prog",simp_all)
         apply (metis (no_types, lifting) b2_2 jitper.simps(2) not_None_eq old.prod.case option.simps(4) option.simps(5) split_pairs) 
        subgoal for aa by (metis (no_types, lifting) b2_2 jitper.simps(2) list.sel(3) old.prod.case option.simps(5) prod.collapse) 
        done
        thus ?thesis using b0 b1 by (metis (no_types, lifting) Cons.hyps False local.Cons(5) unat_minus_one unsigned_0 zero_le)       
      qed     
    qed

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

end