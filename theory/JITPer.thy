section \<open> JIT-Per: translate SBPF assembly to IR1 \<close>

text\<open> IR1 is a list-list binary code:

- each SBPF assembly is mapped a list of binary code
  where SBPF_JUMP ofs is set to 0 in the target binary 
- SBPF assembly and IR1 have the same pc value because JIT-Per is one-by-one 

SBPF: 0: BPF_ADD; 1: BPF_SUB; 2: BPF_EXIT

x64:  0:[add...]; 1:[sub...]; 2: [ret...]
 \<close>

theory JITPer
imports
  Main
  rBPFCommType rBPFSyntax rBPFSem
  x64Syntax x64Semantics x64Assembler
   x64DecodeProofAux
  JITPer_add JITPer_mul_rax JITPer_mul_rdx JITPer_mul_other
  JITPer_exit JITPer_jump
  JITPer_load JITPer_shift
  JITPer_store JITPer_call JITPer_exit
  JITPer_sub JITPer_and JITPer_xor JITPer_or JITPer_mov_rr
  JITPer_shift JITPer_shift_rcx JITPer_load_32   
  JITPer_add_imm
begin


lemma one_step_equiv_proof: 
  assumes a0:"s' = sbpf_step prog s" and
  a1:"s = (SBPF_OK pc rs m ss)" and
  a2:"s' = (SBPF_OK pc' rs' m' ss')" and
  a3:"xst = (Next xpc xrs xm xss')" and
  a4:"match_state s (pc,xst)" and
  a5:"jitper prog = Some x64_prog" and                      
  a6:"prog \<noteq> [] \<and> unat pc < length prog \<and> unat pc \<ge> 0" 
shows "\<exists> xst'. perir_sem 1 x64_prog (pc,xst) = (pc',xst') \<and> 
  match_state s' (pc',xst')"
(* \<and> snd xst' = unat (pc+1)*)
proof-
  let "?bpf_ins" = "prog!(unat pc)"
  have b1:"(\<exists> dst src. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_AND dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_MUL dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_LSH dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
    prog!(unat pc) = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or>
    prog!(unat pc) = BPF_ALU64 BPF_MOV dst (SOReg src)) \<or> 
  (\<exists> dst src chk off. prog!(unat pc) = BPF_LDX chk dst src off) \<or>
  (\<exists> dst src chk off. prog!(unat pc) = BPF_ST chk dst (SOReg src) off) \<or>
  (\<exists> x cond dst src. prog!(unat pc) = BPF_JUMP cond dst (SOReg src) x) \<or>
  (\<exists> src imm. prog!(unat pc) = BPF_CALL_IMM src imm) \<or>
  (\<exists> dst imm. prog!(unat pc) = BPF_ALU64 BPF_ADD dst (SOImm imm)) \<or>
  prog!(unat pc) = BPF_EXIT"
     using a0 a1 a2 a6 aux1 by (metis length_0_conv)  
  obtain src dst x cond chk off imm where 
    b2:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or>  
        ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
        ?bpf_ins  = BPF_ALU64 BPF_MOV dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_LSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or>
        ?bpf_ins = BPF_LDX chk dst src off \<or> 
        ?bpf_ins = BPF_ST chk dst (SOReg src) off \<or> 
        ?bpf_ins = BPF_JUMP cond dst (SOReg src) x \<or>
        ?bpf_ins = BPF_CALL_IMM src imm \<or>
        ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm) \<or>
        ?bpf_ins = BPF_EXIT" using b1 by blast
  show ?thesis
  proof (cases "?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src) ")
    case True
      have c0:"?bpf_ins = BPF_ALU64 BPF_MUL dst (SOReg src)" using True by simp
      have c1:"(bpf_to_x64_reg dst) = RDX \<or> (bpf_to_x64_reg dst) = RAX \<or> (bpf_to_x64_reg dst) \<notin> {RAX, RDX}"  by blast
      then show ?thesis
      proof(cases "(bpf_to_x64_reg dst) = RDX")
        case True   
          then show ?thesis using mulq_one_step_rdx a0 a1 a2 a3 a4 a5 a6 True c1 c0 by blast
        next
        case False
          have c2:"(bpf_to_x64_reg dst) = RAX \<or> (bpf_to_x64_reg dst) \<notin> {RAX, RDX}" using c1 False by simp
          thus ?thesis
        proof (cases "(bpf_to_x64_reg dst) = RAX")
          case True
            then show ?thesis using mulq_one_step_rax a0 a1 a2 a3 a4 a5 a6 False c1 c0 by blast
        next
          case False
            have c3:"(bpf_to_x64_reg dst) \<notin> {RAX, RDX}" using c2 False by blast
            then show ?thesis using mulq_one_step_other a0 a1 a2 a3 a4 a5 a6 False c1 c0 by blast
        qed   
      qed 
    next
    case False
    have c4:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_LSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_LDX chk dst src off \<or> 
        ?bpf_ins = BPF_ST chk dst (SOReg src) off \<or> 
        ?bpf_ins = BPF_JUMP cond dst (SOReg src) x\<or>
        ?bpf_ins = BPF_CALL_IMM src imm \<or>
        ?bpf_ins = BPF_EXIT \<or>
        ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using False b2 by blast
      thus ?thesis 
      proof(cases "(?bpf_ins = BPF_JUMP cond dst (SOReg src) x)")
        case True
          then show ?thesis using True False a0 a1 a2 a3 a4 a5 a6 jump_one_step by simp
        next
        case False
        have c5:"?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src) \<or>  
        ?bpf_ins = BPF_ALU64 BPF_LSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or> 
        ?bpf_ins = BPF_LDX chk dst src off \<or> 
        ?bpf_ins = BPF_ST chk dst (SOReg src) off\<or>
        ?bpf_ins = BPF_CALL_IMM src imm \<or>
        ?bpf_ins = BPF_EXIT \<or>
        ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src) \<or>
        ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
        ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using False c4 by simp
        thus ?thesis
        proof(cases "?bpf_ins = BPF_ALU64 BPF_ADD dst (SOReg src)")
          case True
          then show ?thesis using False True a0 a1 a2 a3 a4 a5 a6 addq_one_step c5 by blast
        next
          case False
          have c6:"?bpf_ins = BPF_ALU64 BPF_LSH dst (SOReg src) \<or> 
          ?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
          ?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or> 
          ?bpf_ins = BPF_LDX chk dst src off \<or> 
          ?bpf_ins = BPF_ST chk dst (SOReg src) off\<or>
          ?bpf_ins = BPF_CALL_IMM src imm \<or>
          ?bpf_ins = BPF_EXIT\<or>
          ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
          ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
          ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
          ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src) \<or>
          ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
          ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using False c5 by presburger 
          thus ?thesis
          proof(cases "?bpf_ins = BPF_ALU64 BPF_LSH dst (SOReg src)")
            case True
            have c6_1:"?bpf_ins = BPF_ALU64 BPF_LSH dst (SOReg src)" using True by simp
            then show ?thesis 
              proof(cases "(bpf_to_x64_reg dst) \<noteq> RCX")
              case True
                then show ?thesis using True a0 a1 a2 a3 a4 a5 a6 True c6_1 by (meson JITPer_shift.shiftq_lsh_one_step1) 
              next
              case False
                have c6_2:"(bpf_to_x64_reg dst) = RCX" using False by auto
                then show ?thesis
                proof(cases "(bpf_to_x64_reg src) \<noteq> RCX")
                   case True
                   then show ?thesis using c6_1 c6_2 a0 a1 a2 a3 a4 a5 a6 JITPer_shift_rcx.shiftq_lsh_one_step1 by auto
                 next
                   case False
                   have "(bpf_to_x64_reg src) = RCX" using False by simp
                   then show ?thesis using c6_1 a0 a1 a2 a3 a4 a5 a6 c6_2 JITPer_shift_rcx.shiftq_lsh_one_step by auto
                 qed
               qed

          next
            case False
            have c7:"?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src) \<or> 
            ?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or> 
            ?bpf_ins = BPF_LDX chk dst src off \<or> 
            ?bpf_ins = BPF_ST chk dst (SOReg src) off\<or>
            ?bpf_ins = BPF_CALL_IMM src imm \<or>
            ?bpf_ins = BPF_EXIT\<or>
            ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
            ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
            ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
            ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
            ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
            ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c6 False by simp
            then show ?thesis 
            proof(cases "?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src)")
              case True
                have c7_1:"?bpf_ins = BPF_ALU64 BPF_RSH dst (SOReg src)" using True by simp
                then show ?thesis 
                proof(cases "(bpf_to_x64_reg dst) \<noteq> RCX")
                  case True
                  then show ?thesis using True a0 a1 a2 a3 a4 a5 a6 True c7_1 by (meson JITPer_shift.shiftq_rsh_one_step1) 
                next
                  case False
                  have c7_2:"(bpf_to_x64_reg dst) = RCX" using False by auto
                  then show ?thesis
                  proof(cases "(bpf_to_x64_reg src) \<noteq> RCX")
                   case True
                   then show ?thesis using c7_1 c7_2 a0 a1 a2 a3 a4 a5 a6 JITPer_shift_rcx.shiftq_rsh_one_step1 by auto
                 next
                   case False
                   have "(bpf_to_x64_reg src) = RCX" using False by simp
                   then show ?thesis using c7_1 a0 a1 a2 a3 a4 a5 a6 c7_2 JITPer_shift_rcx.shiftq_rsh_one_step by auto
                 qed
               qed
            next
              case False
              have c7:"?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src) \<or> 
              ?bpf_ins = BPF_LDX chk dst src off \<or> 
              ?bpf_ins = BPF_ST chk dst (SOReg src) off\<or>
              ?bpf_ins = BPF_CALL_IMM src imm \<or>
              ?bpf_ins = BPF_EXIT \<or>
              ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
              ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
              ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
              ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
              ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
              ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c7 False by simp
              then show ?thesis 
              proof(cases "?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src)")
                case True
                have c8_1:"?bpf_ins = BPF_ALU64 BPF_ARSH dst (SOReg src)" using True by simp
                then show ?thesis 
                proof(cases "(bpf_to_x64_reg dst) \<noteq> RCX")
                  case True
                  then show ?thesis using True a0 a1 a2 a3 a4 a5 a6 True c8_1 by (meson JITPer_shift.shiftq_arsh_one_step1) 
                next
                  case False
                  have c8_2:"(bpf_to_x64_reg dst) = RCX" using False by auto
                  then show ?thesis
                  proof(cases "(bpf_to_x64_reg src) \<noteq> RCX")
                   case True
                   then show ?thesis using c8_1 c8_2 a0 a1 a2 a3 a4 a5 a6 JITPer_shift_rcx.shiftq_arsh_one_step1 by auto
                 next
                   case False
                   have "(bpf_to_x64_reg src) = RCX" using False by simp
                   then show ?thesis using c8_1 a0 a1 a2 a3 a4 a5 a6 c8_2 JITPer_shift_rcx.shiftq_arsh_one_step by auto
                 qed
               qed
              next
                case False
                have c8:"?bpf_ins = BPF_LDX chk dst src off \<or> 
                ?bpf_ins = BPF_ST chk dst (SOReg src) off\<or>
                ?bpf_ins = BPF_CALL_IMM src imm \<or>
                ?bpf_ins = BPF_EXIT\<or>
                ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
                ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
                ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c7 False by simp
                then show ?thesis
                proof(cases "?bpf_ins = BPF_LDX chk dst src off")
                  case True
                    have c8_1:"chk = M64 \<or> chk = M32" using a0 a1 a2 a6 True apply(cases "prog!(unat pc)",simp_all)
                      subgoal for x21 by(cases chk,simp_all) done
                  thus ?thesis
                  proof(cases chk)
                    case M8
                    then show ?thesis using c8_1 by blast
                  next
                    case M16
                    then show ?thesis using c8_1 by simp
                  next
                    case M32
                    then show ?thesis using load_m32_one_step1 a0 a1 a2 a3 a4 a5 a6 True by simp
                  next
                    case M64
                    then show ?thesis using load_m64_one_step1 a0 a1 a2 a3 a4 a5 a6 True by simp
                  qed
             
                next
                  case False
                  have c9:"?bpf_ins = BPF_ST chk dst (SOReg src) off\<or>
                  ?bpf_ins = BPF_CALL_IMM src imm \<or>
                  ?bpf_ins = BPF_EXIT\<or>
                  ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
                  ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
                  ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                  ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                  ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                  ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using False c8 by simp
                  then show ?thesis
                   proof(cases "?bpf_ins = BPF_ST chk dst (SOReg src) off")
                     case True
                     have c9_1:"chk = M64" using a0 a1 a2 a6 True apply(cases "prog!(unat pc)",simp_all)
                      subgoal for x21 by(cases chk,simp_all) done
                     thus ?thesis
                     proof(cases chk)
                       case M8
                       then show ?thesis using c9_1 by simp
                     next
                       case M16
                       then show ?thesis using c9_1 by simp
                     next
                       case M32
                       then show ?thesis using c9_1 by simp
                     next
                       case M64
                       then show ?thesis using store_one_step1 a0 a1 a2 a3 a4 a5 a6 True by simp
                     qed
                   next
                     case False
                     have c10:"?bpf_ins = BPF_CALL_IMM src imm \<or>
                     ?bpf_ins = BPF_EXIT\<or>
                     ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
                     ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
                     ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                     ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                     ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                     ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using False c9 by simp
                     then show ?thesis
                      proof(cases "?bpf_ins = BPF_CALL_IMM src imm")
                        case True
                        then show ?thesis using call_imm_one_step a0 a1 a2 a3 a4 a5 a6 True by simp
                      next
                        case False
                        have c11:"?bpf_ins = BPF_EXIT\<or>
                              ?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c10 False by simp

                        then show ?thesis 
                        proof(cases "?bpf_ins = BPF_EXIT")
                          case True
                          then show ?thesis using exit_one_step a0 a1 a2 a3 a4 a5 a6 True by blast
                        next
                          case False
                          have c12:"?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c11 False by simp
                          then show ?thesis 
                          proof(cases "?bpf_ins  = BPF_ALU64 BPF_SUB dst (SOReg src)")
                            case True
                            then show ?thesis using subq_one_step a0 a1 a2 a3 a4 a5 a6 True by blast
                          next
                            case False
                              have c13:"?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c12 False by simp
                            then show ?thesis 
                            proof(cases "?bpf_ins = BPF_ALU64 BPF_XOR dst (SOReg src)")
                              case True
                              then show ?thesis using xorq_one_step a0 a1 a2 a3 a4 a5 a6 True by blast
                            next
                              case False
                              have c14:"?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src) \<or>
                              ?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                              ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c13 False by simp
                              then show ?thesis 
                              proof(cases "?bpf_ins = BPF_ALU64 BPF_OR dst (SOReg src)")
                                case True
                                then show ?thesis using orq_one_step a0 a1 a2 a3 a4 a5 a6 True by blast
                              next
                                case False
                                have c15:"?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)\<or>
                                      ?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                                      ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c14 False by simp

                                then show ?thesis 
                                proof(cases "?bpf_ins = BPF_ALU64 BPF_AND dst (SOReg src)")
                                  case True
                                  then show ?thesis using andq_one_step a0 a1 a2 a3 a4 a5 a6  by blast
                                next
                                  case False
                                  have c16:"?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)\<or>
                                        ?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using False c15 by simp
                                  thus ?thesis
                                  proof(cases "?bpf_ins = BPF_ALU64 BPF_MOV dst (SOReg src)")
                                    case True
                                    then show ?thesis using movq_one_step a0 a1 a2 a3 a4 a5 a6 by blast
                                  next
                                    case False
                                    hence "?bpf_ins = BPF_ALU64 BPF_ADD dst (SOImm imm)" using c16 by auto
                                    then show ?thesis using addq_imm_one_step a0 a1 a2 a3 a4 a5 a6 by blast  
                                  qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                   qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed


lemma x64_sem1_induct_aux1:
 "perir_sem (m+n) x64_prog xst = xst'\<Longrightarrow> 
  \<exists> xst1. perir_sem m x64_prog xst = xst1 \<and>
  perir_sem n x64_prog xst1 = xst'"
 apply(induct m arbitrary: n x64_prog xst xst' )
   apply auto[1]
  subgoal for m n x64_prog xst xst'
    apply (simp add: Let_def)
    apply(cases xst;simp)
    done
  done

lemma x64_sem1_induct_aux3:
  "perir_sem (Suc n) x64_prog xst = xst' \<Longrightarrow> 
  perir_sem 1 x64_prog xst = xst1 \<Longrightarrow> 
  perir_sem n x64_prog xst1 = xst'"  
using x64_sem1_induct_aux1
  by (metis plus_1_eq_Suc)


lemma n_steps_equiv_proof_aux:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m ss);
   s' = (SBPF_OK pc' rs' m' ss');
   xst = (Next xpc xrs xm xss);
   match_state s (pc,xst);
   jitper prog = Some x64_prog;
   prog \<noteq> [];
   perir_sem n x64_prog (pc,xst) = xst' \<rbrakk> \<Longrightarrow>
   match_state s' xst'"
(* \<exists> xst'. perir_sem n pc x64_prog xst = xst' \<and> match_state s' xst'"*)
proof (induction n arbitrary: prog s s' pc rs m ss pc' rs' m' ss' xst' xst xpc xrs xm xss x64_prog xst')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume 
       assm1: "sbpf_sem (Suc n) prog s = s'" and
       assm2:"s = SBPF_OK pc rs m ss" and
       assm3:"s' = SBPF_OK pc' rs' m' ss'" and
       assm4:"xst = Next xpc xrs xm xss" and
       assm5:"match_state s (pc,xst)" and
       assm6:"jitper prog = Some x64_prog" and
       assm7:"prog \<noteq> [] " and
       assm9:"perir_sem (Suc n) x64_prog (pc,xst) = xst'"
  then obtain s1 where s1_eq: "s1 = sbpf_step prog s" by simp
  have n_step_def:"sbpf_sem n prog s1 = s'" using s1_eq assm1 sbpf_sem_induct
    by (metis sbpf_sem.simps(2))
  have a0:"unat pc < length prog \<and> unat pc \<ge> 0" using assm1 assm3 
    using Suc.prems(2) assm7 pc_scope_aux
    by (metis (no_types, lifting) err_is_still_err n_step_def s1_eq sbpf_state.simps(6) sbpf_step.simps(1) verit_comp_simplify1(3)) 
  moreover have a1:"\<exists> pc1 rs1 m1 ss1 . s1 = (SBPF_OK pc1 rs1 m1 ss1)"
    by (metis Suc.prems(3) bot_nat_0.not_eq_extremum intermediate_step_is_ok n_step_def sbpf_sem.simps(1) sbpf_state.simps(6))
  obtain pc1 rs1 m1 ss1 where a2:"s1 = (SBPF_OK pc1 rs1 m1 ss1)" using a1 by auto

  have "\<exists> num off l. x64_prog!(unat pc) = (num,off,l)" by (metis split_pairs)
  then obtain num off l where a6:"x64_prog!(unat pc) = (num,off,l)" by auto
  have a7:"l = (snd (snd ((x64_prog!(unat pc)))))" using a6 by simp

  have "\<exists> xst1. perir_sem 1 x64_prog (pc,xst) = (pc1,xst1) \<and> match_state s1 (pc1,xst1)"
    using s1_eq assm2 a2 assm4 assm5 assm6 assm7 one_step_equiv_proof a6 a7 a0 by blast
  then obtain xst1 where a4:"perir_sem 1 x64_prog (pc,xst) = (pc1,xst1) \<and> match_state s1 (pc1,xst1)" by auto
  hence a4_1:"perir_sem 1 x64_prog (pc,xst) = (pc1,xst1)" by auto
  have an:"\<exists> xpc1 xrs1 xm1 xss1. xst1 = Next xpc1 xrs1 xm1 xss1" using a4 by (metis match_s_not_stuck outcome.exhaust)
  then obtain xpc1 xrs1 xm1 xss1 where a10:"xst1 = Next xpc1 xrs1 xm1 xss1" by auto
  have a5:"match_state s1 (pc1,xst1)" using an match_state_def
    using a10 a2 a4 by fastforce
  have    "sbpf_sem n prog s = s' \<Longrightarrow>
           s = SBPF_OK pc rs m ss \<Longrightarrow>
           s' = SBPF_OK pc' rs' m' ss' \<Longrightarrow>
           xst = Next xpc xrs xm xss \<Longrightarrow>
           match_state s (pc, xst) \<Longrightarrow>
           jitper prog = Some x64_prog \<Longrightarrow> 
           prog \<noteq> [] \<Longrightarrow> 
           perir_sem n x64_prog (pc, xst) = xst' \<Longrightarrow> 
           match_state s' xst'" using Suc by blast

  have "\<exists> xst''. perir_sem n x64_prog (pc1, xst1) = xst''" by blast
  then obtain xst'' where b0:"perir_sem n x64_prog (pc1, xst1) = xst''" by auto
  hence b1:"xst' = xst''" 
    using x64_sem1_induct_aux1 a2 assm2 s1_eq assm4 assm9 a6 a4 a10 by (metis plus_1_eq_Suc)
  hence "match_state s' xst''"
    using n_step_def a2 assm3 a10 a5 assm6 assm7 Suc b0 by simp
  hence an:"match_state s' xst'" using b1 by simp
  then show ?case using an by auto
qed

lemma n_steps_equiv_proof:
  "\<lbrakk> sbpf_sem n prog s = s';
   s = (SBPF_OK pc rs m ss);
   s' = (SBPF_OK pc' rs' m' ss');
   xst = (Next xpc xrs xm xss');
   match_state s (pc,xst);
   jitper prog = Some x64_prog;
   prog \<noteq> [] \<rbrakk> \<Longrightarrow>
   \<exists> xst'.  perir_sem n x64_prog (pc,xst) = xst' \<and>
   match_state s' xst'"
  using n_steps_equiv_proof_aux
  by blast
                                 
end