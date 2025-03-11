section \<open> Axiom Memory model \<close>

theory Mem
imports
  Main
  rBPFCommType Val
begin

type_synonym mem = "nat \<Rightarrow> (int, u8) map"

(*type_synonym mem = "(u64, u8) map"*)

definition init_mem :: "mem" where
"init_mem = (\<lambda> _ _ . None)"

datatype memory_chunk = M8 | M16 | M32 | M64 

definition memory_chunk_to_byte_int :: "memory_chunk \<Rightarrow> int" where
"memory_chunk_to_byte_int mc = (
  case mc of
  M8 \<Rightarrow> 0 |
  M16 \<Rightarrow> 1 |
  M32 \<Rightarrow> 3 |
  M64 \<Rightarrow> 7
)"

type_synonym addr_type = val
(*type_synonym addr_type = u64*)

definition option_u64_of_u8_1 :: "u8 option \<Rightarrow> u64 option" where
"option_u64_of_u8_1 v0 = (
  case v0 of None \<Rightarrow> None |
  Some v \<Rightarrow> Some (ucast v)
)"

definition option_u64_of_u8_2 :: "u8 option \<Rightarrow> u8 option \<Rightarrow> u64 option" where
"option_u64_of_u8_2 v0 v1 = (
  case v0 of None \<Rightarrow> None |
  Some n0 \<Rightarrow> (
    case v1 of None \<Rightarrow> None |
    Some n1 \<Rightarrow> Some (or ((ucast n1) << 8) (ucast n0))
  )
)"

definition option_u64_of_u8_4 :: "u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u64 option" where
"option_u64_of_u8_4 v0 v1 v2 v3 = (
  case v0 of None \<Rightarrow> None |
  Some n0 \<Rightarrow> (
    case v1 of None \<Rightarrow> None |
    Some n1 \<Rightarrow> (
      case v2 of None \<Rightarrow> None |
      Some n2 \<Rightarrow> (
        case v3 of None \<Rightarrow> None |
        Some n3 \<Rightarrow>
          Some (or ((ucast n3) << 24)
                    (or ((ucast n2) << 16)
                        (or ((ucast n1) << 8) (ucast n0) ) ))))
  )
)"

definition sp_block ::"nat" where "sp_block = 1"


definition option_u64_of_u8_8 :: "u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow>
  u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow> u8 option \<Rightarrow>  u64 option" where
"option_u64_of_u8_8 v0 v1 v2 v3 v4 v5 v6 v7 = (
  case v0 of None \<Rightarrow> None |
  Some n0 \<Rightarrow> (
    case v1 of None \<Rightarrow> None |
    Some n1 \<Rightarrow> (
      case v2 of None \<Rightarrow> None |
      Some n2 \<Rightarrow> (
        case v3 of None \<Rightarrow> None |
        Some n3 \<Rightarrow> (
          case v4 of None \<Rightarrow> None |
          Some n4 \<Rightarrow> (
            case v5 of None \<Rightarrow> None |
            Some n5 \<Rightarrow> (
              case v6 of None \<Rightarrow> None |
              Some n6 \<Rightarrow> (
                case v7 of None \<Rightarrow> None |
                Some n7 \<Rightarrow>
                  Some (or ((ucast n7) << 56)
                            (or ((ucast n6) << 48)
                              (or ((ucast n5) << 40)
                                  (or ((ucast n4) << 32)
                                      (or ((ucast n3) << 24)
                                          (or ((ucast n2) << 16)
                                              (or ((ucast n1) << 8) (ucast n0) ) ))))))))))))
  )
)"


definition memory_chunk_value_of_u64 :: "memory_chunk \<Rightarrow> u64 \<Rightarrow> val" where
"memory_chunk_value_of_u64 mc v = (
  case mc of
  M8 \<Rightarrow> Vbyte (ucast v) |
  M16 \<Rightarrow> Vshort (ucast v) |
  M32 \<Rightarrow> Vint (ucast v) |
  M64 \<Rightarrow> Vlong (ucast v)
)"

definition option_val_of_u64 :: "memory_chunk \<Rightarrow> u64 option \<Rightarrow> val option" where
"option_val_of_u64 mc v = (
  case v of
  None \<Rightarrow> None |
  Some v1 \<Rightarrow> Some (memory_chunk_value_of_u64 mc v1)
)"

(*
definition loadv :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" where
"loadv mc m addr = ( option_val_of_u64 mc (
  case mc of
  M8  \<Rightarrow> option_u64_of_u8_1 (m addr) |
  M16 \<Rightarrow> option_u64_of_u8_2 (m addr) (m (addr+1))|
  M32 \<Rightarrow> option_u64_of_u8_4 (m addr) (m (addr+1)) (m (addr+2)) (m (addr+3))|
  M64 \<Rightarrow> option_u64_of_u8_8 (m addr) (m (addr+1)) (m (addr+2)) (m (addr+3))
                        (m (addr+4)) (m (addr+5)) (m (addr+6)) (m (addr+7))
))"
*)

definition loadv :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val option" where
"loadv mc m addr = (
  case addr of 
     Vptr b off \<Rightarrow>
        if b = 0 then None
        else 
          ( option_val_of_u64 mc (case mc of
            M8  \<Rightarrow> option_u64_of_u8_1 (m b (uint off)) |
            M16 \<Rightarrow> option_u64_of_u8_2 (m b (uint off)) (m b ((uint off)+1))|
            M32 \<Rightarrow> option_u64_of_u8_4 (m b (uint off)) (m b ((uint off)+1)) (m b ((uint off)+2)) (m b ((uint off)+3))|
            M64 \<Rightarrow> option_u64_of_u8_8 (m b (uint off)) (m b ((uint off)+1)) (m b ((uint off)+2)) (m b ((uint off)+3))
                        (m b ((uint off)+4)) (m b ((uint off)+5)) (m b ((uint off)+6)) (m b ((uint off)+7))
    ))|
    Vlong off \<Rightarrow> (option_val_of_u64 mc (
        case mc of
          M8  \<Rightarrow> option_u64_of_u8_1 (m 0 (uint off)) |
          M16 \<Rightarrow> option_u64_of_u8_2 (m 0 (uint off)) (m 0 ((uint off)+1))|
          M32 \<Rightarrow> option_u64_of_u8_4 (m 0 (uint off)) (m 0 ((uint off)+1)) (m 0 ((uint off)+2)) (m 0 ((uint off)+3))|
          M64 \<Rightarrow> option_u64_of_u8_8 (m 0 (uint off)) (m 0 ((uint off)+1)) (m 0 ((uint off)+2)) (m 0 ((uint off)+3))
                        (m 0 ((uint off)+4)) (m 0 ((uint off)+5)) (m 0 ((uint off)+6)) (m 0 ((uint off)+7))
    ))|
    _ \<Rightarrow> None)"

value "option_u64_of_u8_2 (Some 0b10000000) (Some 0b01000000)"
value "0b10000000::u8"
value "0b01000000::u8"

(*definition storev :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option" where
"storev mc m addr v = (
  case mc of
  M8  \<Rightarrow> (
    case v of
    Vbyte n \<Rightarrow> Some (\<lambda> i. if i = addr then Some n else m i) |
    _ \<Rightarrow> None) |
  M16 \<Rightarrow> (
    case v of
    Vshort n \<Rightarrow>
      let l = u8_list_of_u16 n in
        Some (\<lambda> i. if i = addr    then Some (l!(0)) else
                   if i = addr+1  then Some (l!(1)) else
                      m i) |
    _ \<Rightarrow> None) |
  M32 \<Rightarrow> (
    case v of
    Vint n \<Rightarrow>
      let l = u8_list_of_u32 n in
        Some (\<lambda> i. if i = addr    then Some (l!(0)) else
                   if i = addr+1  then Some (l!(1)) else
                   if i = addr+2  then Some (l!(2)) else
                   if i = addr+3  then Some (l!(3)) else
                      m i) |
    _ \<Rightarrow> None) |
  M64 \<Rightarrow> (
    case v of
    Vlong n \<Rightarrow>
      let l = u8_list_of_u64 n in
        Some (\<lambda> i. if i = addr    then Some (l!(0)) else
                   if i = addr+1  then Some (l!(1)) else
                   if i = addr+2  then Some (l!(2)) else
                   if i = addr+3  then Some (l!(3)) else
                   if i = addr+4  then Some (l!(4)) else
                   if i = addr+5  then Some (l!(5)) else
                   if i = addr+6  then Some (l!(6)) else
                   if i = addr+7  then Some (l!(7)) else
                      m i) |
    _ \<Rightarrow> None)
)"
*)
definition storev :: "memory_chunk \<Rightarrow> mem \<Rightarrow> addr_type \<Rightarrow> val \<Rightarrow> mem option" where
"storev mc m addr v = (
  case addr of 
    Vptr b off \<Rightarrow>
      if b = 0 then None
      else
        (case mc of
          M8  \<Rightarrow> (
             case v of
                Vbyte n \<Rightarrow> Some (\<lambda> x i. if x = b \<and> i = (uint off) then Some n else m x i ) |
                _ \<Rightarrow> None) |
          M16 \<Rightarrow> (
             case v of
                Vshort n \<Rightarrow>
                  let l = u8_list_of_u16 n in
                    Some (\<lambda> x i. if x = b \<and> i = (uint off)      then Some (l!(0)) else
                                 if x = b \<and> i = ((uint off)+1)  then Some (l!(1)) else
                           m x i) |
                _ \<Rightarrow> None) |
         M32 \<Rightarrow> (
            case v of
              Vint n \<Rightarrow>
                let l = u8_list_of_u32 n in
                  Some (\<lambda> x i. if x = b \<and> i = (uint off)      then Some (l!(0)) else
                             if x = b \<and> i = ((uint off)+1)    then Some (l!(1)) else
                             if x = b \<and> i = ((uint off)+2)    then Some (l!(2)) else
                             if x = b \<and> i = ((uint off)+3)    then Some (l!(3)) else
                             m x i) |
              _ \<Rightarrow> None) |
        M64 \<Rightarrow> (
          case v of
            Vlong n \<Rightarrow>
              let l = u8_list_of_u64 n in
                Some (\<lambda> x i. if x = b \<and> i = (uint off)    then Some (l!(0)) else
                             if x = b \<and> i = ((uint off)+1)  then Some (l!(1)) else
                             if x = b \<and> i = ((uint off)+2)  then Some (l!(2)) else
                             if x = b \<and> i = ((uint off)+3)  then Some (l!(3)) else
                             if x = b \<and> i = ((uint off)+4)  then Some (l!(4)) else
                             if x = b \<and> i = ((uint off)+5)  then Some (l!(5)) else
                             if x = b \<and> i = ((uint off)+6)  then Some (l!(6)) else
                             if x = b \<and> i = ((uint off)+7)  then Some (l!(7)) else
                              m x i) |
            _ \<Rightarrow> None))|

  Vlong off \<Rightarrow> 
      (case mc of
          M8  \<Rightarrow> (
            case v of
              Vbyte n \<Rightarrow> Some (\<lambda> x i. if x = 0 \<and> i = (uint off) then Some n else m 0 i) |
              _ \<Rightarrow> None) |
          M16 \<Rightarrow> (
             case v of
              Vshort n \<Rightarrow>
                let l = u8_list_of_u16 n in
                Some (\<lambda> x i. if x = 0 \<and> i = (uint off)    then Some (l!(0)) else
                   if x = 0 \<and> i = (uint off)+1  then Some (l!(1)) else
                      m 0 i) |
              _ \<Rightarrow> None) |
        M32 \<Rightarrow> (
            case v of
              Vint n \<Rightarrow>
                let l = u8_list_of_u32 n in
                Some (\<lambda> x i. if x = 0 \<and> i = (uint off)    then Some (l!(0)) else
                   if x = 0 \<and> i = (uint off)+1  then Some (l!(1)) else
                   if x = 0 \<and> i = (uint off)+2  then Some (l!(2)) else
                   if x = 0 \<and> i = (uint off)+3  then Some (l!(3)) else
                      m 0 i) |
             _ \<Rightarrow> None) |
       M64 \<Rightarrow> (
          case v of
            Vlong n \<Rightarrow>
              let l = u8_list_of_u64 n in
               Some (\<lambda> x i. if x = 0 \<and> i = (uint off)    then Some (l!(0)) else
                   if x = 0 \<and> i = (uint off)+1  then Some (l!(1)) else
                   if x = 0 \<and> i = (uint off)+2  then Some (l!(2)) else
                   if x = 0 \<and> i = (uint off)+3  then Some (l!(3)) else
                   if x = 0 \<and> i = (uint off)+4  then Some (l!(4)) else
                   if x = 0 \<and> i = (uint off)+5  then Some (l!(5)) else
                   if x = 0 \<and> i = (uint off)+6  then Some (l!(6)) else
                   if x = 0 \<and> i = (uint off)+7  then Some (l!(7)) else
                      m 0 i) |
           _ \<Rightarrow> None))|
  _ \<Rightarrow> None
)"

definition init_mem2 :: "mem" where
"init_mem2 = (\<lambda> x i. if x = 1 \<and> i = (0b0000000000000000000000000000000000000000000000000000000000000001::int) then Some 0 else None)"


value "loadv M16 init_mem2 ((Vptr 1 1)::val)"

value "loadv M16 init_mem2 ((Vlong 1)::val)"

value "(storev M16 init_mem2 (Vptr 0 1) (Vshort 1))"

value "(storev M16 init_mem2 (Vlong 1) (Vshort 1))"

value "loadv M16 (the (storev M16 init_mem2 (Vlong 1) (Vshort 1))) (Vlong 1)"

value "loadv M16 (the (storev M16 init_mem2 (Vptr 1 1) (Vshort 1))) (Vptr 1 1)"


definition vlong_of_memory_chunk :: "memory_chunk \<Rightarrow> val" where
"vlong_of_memory_chunk chunk = (
  case chunk of
  M8  \<Rightarrow> Vlong 8 |
  M16 \<Rightarrow> Vlong 16 |
  M32 \<Rightarrow> Vlong 32 |
  M64 \<Rightarrow> Vlong 64
)"

definition u64_of_memory_chunk :: "memory_chunk \<Rightarrow> u64" where
"u64_of_memory_chunk chunk = (
  case chunk of
  M8  \<Rightarrow> 8 |
  M16 \<Rightarrow> 16 |
  M32 \<Rightarrow> 32 |
  M64 \<Rightarrow> 64
)"

lemma sub_8_eq: "k \<le> n \<Longrightarrow> (n::nat) < k+8 \<Longrightarrow> n-k < 8" by simp

lemma le_255_int: "k < 8 \<Longrightarrow>  bit (255::int) k"
  apply (cases k, simp)
  subgoal for n1 apply (cases n1, simp)
    subgoal for n2 apply (cases n2, simp)
      subgoal for n3 apply (cases n3, simp)
        subgoal for n4 apply (cases n4, simp)
          subgoal for n5 apply (cases n5, simp)
            subgoal for n6 apply (cases n6, simp)
              subgoal for n7 apply (cases n7, simp)
                subgoal for n8 by simp
                done
              done
            done
          done
        done
      done
    done
  done

lemma int_255_8_eq: "k \<le> n \<Longrightarrow> n < k+8 \<Longrightarrow> bit (255::int) (n - k)"
  using sub_8_eq le_255_int
  by presburger

(*prove load_store_other *)
(*lemma store_load_consistency_aux: "Some m' = storev M32 m place v \<Longrightarrow> loadv M32 m' place = Some v"
  apply (simp add: storev_def loadv_def option_val_of_u64_def option_u64_of_u8_4_def)
  apply (cases v; simp add: Let_def memory_chunk_value_of_u64_def u8_list_of_u32_def)
  subgoal for x4
    apply (simp add: bit_eq_iff [of _ x4])
    apply (simp add: bit_simps)
    apply (rule allI)
    subgoal for n
      apply (cases "24 \<le> n"; simp)
      subgoal
        apply (cases "bit x4 n"; simp)
        apply (rule impI)
        apply (subgoal_tac "n - 24 < 64 \<and> n - 24 < 8 \<and> n - 24 < 32 \<and> bit (255::int) (n - 24)")
        subgoal by simp
        subgoal using int_255_8_eq
          by auto
        done
  
      subgoal
        apply (cases "16 \<le> n"; simp)
        subgoal
          apply (cases "bit x4 n"; simp)
          apply (subgoal_tac "n - 16 < 64 \<and> n - 16 < 8 \<and> n - 16 < 32 \<and> bit (255::int) (n - 16)")
          subgoal by simp
          subgoal using int_255_8_eq
            by auto
          done
    
        subgoal
          apply (cases "8 \<le> n"; simp)
          subgoal
            apply (drule Orderings.linorder_class.not_le_imp_less)
            subgoal using int_255_8_eq
              by auto
            done
          subgoal
            apply (drule Orderings.linorder_class.not_le_imp_less)
            apply (cases "bit x4 n"; simp)
            using int_255_8_eq
            using le_255_int by blast
          done
        done
      done
    done
  done
*)

lemma u32_shift_u8_eq: "
 ucast
     ((or (ucast ((ucast (and (x4 >> 24) 255)) ::u8) << 24)
       (or (ucast ((ucast (and (x4 >> 16) 255)) ::u8) << 16)
         (or (ucast ((ucast (and (x4 >> 8) 255)) ::u8) << 8)
             (ucast ((ucast (and x4 255)) ::u8)) ))) ::u64) =
    (x4::u32)
"
  apply (simp add: bit_eq_iff [of _ x4])
  apply (simp add: bit_simps)
  apply (rule allI)
  subgoal for n
    apply (cases "24 \<le> n"; simp)
    subgoal
      apply (cases "bit x4 n"; simp)
      apply (rule impI)
      apply (subgoal_tac "n - 24 < 64 \<and> n - 24 < 8 \<and> n - 24 < 32 \<and> bit (255::int) (n - 24)")
      subgoal by simp
      subgoal using int_255_8_eq
        by auto
      done
  
    subgoal
      apply (cases "16 \<le> n"; simp)
      subgoal
        apply (cases "bit x4 n"; simp)
        apply (subgoal_tac "n - 16 < 64 \<and> n - 16 < 8 \<and> n - 16 < 32 \<and> bit (255::int) (n - 16)")
        subgoal by simp
        subgoal using int_255_8_eq
          by auto
        done
  
      subgoal
        apply (cases "8 \<le> n"; simp)
        subgoal
          apply (drule Orderings.linorder_class.not_le_imp_less)
          subgoal using int_255_8_eq
            by auto
          done
        subgoal
          apply (drule Orderings.linorder_class.not_le_imp_less)
          apply (cases "bit x4 n"; simp)
          using int_255_8_eq
          using le_255_int by blast
        done
      done
    done
  done
      


lemma store_load_consistency_aux: "Some m' = storev M32 m place v \<Longrightarrow> loadv M32 m' place = Some v"
  apply (simp add: storev_def loadv_def option_val_of_u64_def option_u64_of_u8_4_def)
  apply (cases v; simp add: Let_def memory_chunk_value_of_u64_def u8_list_of_u32_def)
       apply(cases place,simp_all)
  subgoal for x61 x62
    apply(split if_splits,simp_all)
    done
  subgoal for x2 apply(cases place,simp_all)
    subgoal for x61 x62
      apply(split if_splits,simp_all)
      done
    done
  subgoal for x3
    apply(cases place,simp_all)
 subgoal for x61 x62
   apply(split if_splits,simp_all)
   done
  done
  subgoal for x4
    apply(cases place,simp_all)
    subgoal for x5
      apply(unfold Let_def,simp_all)
      apply(unfold u8_list_of_u32_def option_u64_of_u8_4_def option_val_of_u64_def memory_chunk_value_of_u64_def,simp_all)

      using u32_shift_u8_eq
      by blast
      
    subgoal for x61 x62
      apply(split if_splits,simp_all)
      apply(unfold Let_def option_u64_of_u8_4_def option_val_of_u64_def memory_chunk_value_of_u64_def u8_list_of_u32_def,simp_all)
      
      using u32_shift_u8_eq
      by blast

    done
  subgoal for x5
    apply(cases place,simp_all) 
    subgoal for x61 x62 
      apply(split if_splits,simp_all)
      done
    done
  subgoal for x61 x62 
    apply(cases place,simp_all) 
    subgoal for x61a x62a
      apply(split if_splits,simp_all)
      done
    done
  done


lemma store_load_consistency1: "storev M32 m place v = Some m' \<Longrightarrow> loadv M32 m' place = Some v"
  using store_load_consistency_aux by metis

lemma u64_shift_u8_eq: "
  or (ucast ((ucast (and (x4 >> 56) 255)) ::u8) << 56)
 (or (ucast ((ucast (and (x4 >> 48) 255)) ::u8) << 48)
 (or (ucast ((ucast (and (x4 >> 40) 255)) ::u8) << 40)
 (or (ucast ((ucast (and (x4 >> 32) 255)) ::u8) << 32)
 (or (ucast ((ucast (and (x4 >> 24) 255)) ::u8) << 24)
 (or (ucast ((ucast (and (x4 >> 16) 255)) ::u8) << 16)
 (or (ucast ((ucast (and (x4 >> 8) 255)) ::u8) << 8)
     (ucast ((ucast (and x4 255)) ::u8) ))))))) =
    (x4::u64)
"
  apply (simp add: bit_eq_iff [of _ x4])
  apply (simp add: bit_simps)
  apply (rule allI)
  subgoal for n
    apply (cases "56 \<le> n"; simp)
    subgoal
      apply (cases "bit x4 n"; simp)
      apply (rule impI)
      apply (subgoal_tac "n - 56 < 64 \<and> n - 56 < 8 \<and> n - 56 < 64 \<and> bit (255::int) (n - 56)")
      subgoal by simp
      subgoal using int_255_8_eq
        by auto
      done
  
    subgoal
      apply (cases "48 \<le> n"; simp)
      subgoal
        apply (cases "bit x4 n"; simp)
        apply (subgoal_tac "n - 48 < 64 \<and> n - 48 < 8 \<and> n - 48 < 64 \<and> bit (255::int) (n - 48)")
        subgoal by simp
        subgoal using int_255_8_eq
          by auto
        done
  
      subgoal
        apply (cases "40 \<le> n"; simp)
        subgoal
          apply (cases "bit x4 n"; simp)
          apply (subgoal_tac "n - 40 < 64 \<and> n - 40 < 8 \<and> n - 40 < 64 \<and> bit (255::int) (n - 40)")
          subgoal by simp
          subgoal using int_255_8_eq
            by auto
          done
  
        subgoal
          apply (cases "32 \<le> n"; simp)
          subgoal
            apply (cases "bit x4 n"; simp)
            apply (subgoal_tac "n - 32 < 64 \<and> n - 32 < 8 \<and> n - 32 < 64 \<and> bit (255::int) (n - 32)")
            subgoal by simp
            subgoal using int_255_8_eq
              by auto
            done
  
          subgoal
            apply (cases "24 \<le> n"; simp)
            subgoal
              apply (cases "bit x4 n"; simp)
              apply (subgoal_tac "n - 24 < 64 \<and> n - 24 < 8 \<and> n - 24 < 32 \<and> bit (255::int) (n - 24)")
              subgoal by simp
              subgoal using int_255_8_eq
                by auto
              done
          
            subgoal
              apply (cases "16 \<le> n"; simp)
              subgoal
                apply (cases "bit x4 n"; simp)
                apply (subgoal_tac "n - 16 < 64 \<and> n - 16 < 8 \<and> n - 16 < 32 \<and> bit (255::int) (n - 16)")
                subgoal by simp
                subgoal using int_255_8_eq
                  by auto
                done

              subgoal
                apply (cases "8 \<le> n"; simp)
                subgoal
                  apply (drule Orderings.linorder_class.not_le_imp_less)
                  subgoal using int_255_8_eq
                    by auto
                  done
                subgoal
                  apply (drule Orderings.linorder_class.not_le_imp_less)
                  apply (cases "bit x4 n"; simp)
                  using int_255_8_eq
                  using le_255_int by blast
                done
              done
            done
          done
        done
      done
    done
  done
      


lemma store_load_consistency2_aux: "Some m' = storev M64 m place v \<Longrightarrow> loadv M64 m' place = Some v"
  apply (simp add: storev_def loadv_def option_val_of_u64_def option_u64_of_u8_4_def)
  apply (cases v; simp add: Let_def memory_chunk_value_of_u64_def u8_list_of_u64_def)
       apply(cases place,simp_all)
  subgoal for x61 x62
    apply(split if_splits,simp_all)
    done

  subgoal for x2 apply(cases place,simp_all)
    subgoal for x61 x62
      apply(split if_splits,simp_all)
      done
    done

  subgoal for x3
    apply(cases place,simp_all)
    subgoal for x61 x62
      apply(split if_splits,simp_all)
      done
    done

  subgoal for x4
    apply(cases place,simp_all)
    subgoal for x61 x62
      apply (cases "x61 = 0"; simp)
      done
    done

  subgoal for x5
    apply(cases place,simp_all add: u8_list_of_u64_def Let_def option_val_of_u64_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def) 
    subgoal for x5a
      using u64_shift_u8_eq by blast
    subgoal for x61 x62 
      apply (cases "x61 = 0"; simp add: u8_list_of_u64_def Let_def option_val_of_u64_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
      using u64_shift_u8_eq by blast
    done
  subgoal for x61 x62 
    apply(cases place,simp_all) 
    subgoal for x61a x62a
      apply(split if_splits,simp_all)
      done
    done
  done

lemma store_load_consistency: "storev M64 m place v = Some m' \<Longrightarrow> loadv M64 m' place = Some v"
  using store_load_consistency2_aux
  by metis

lemma store_load_other_blk_if:"storev mc m (Vptr blk off) x = Some m' \<Longrightarrow>
  loadv mc1 m (Vlong place) = Some v \<Longrightarrow> loadv mc1 m' (Vlong place) = Some v"
  using store_load_consistency 
  apply(simp add: storev_def loadv_def)
  apply(cases "blk = 0"; simp)
  apply(cases mc; cases x; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def)
  subgoal for x2
    using n_not_Suc_n option.inject
    apply force
    done
  subgoal
    using One_nat_def option.inject zero_neq_one
    by auto
  subgoal
    using One_nat_def option.inject zero_neq_one
    by auto
  subgoal
    using One_nat_def option.inject zero_neq_one
    by auto
  done

lemma store_load_other_blk_only_if:"storev mc m (Vptr blk off) x = Some m' \<Longrightarrow>
  loadv mc1 m' (Vlong place) = Some v \<Longrightarrow> loadv mc1 m (Vlong place) = Some v"
  using store_load_consistency 
  apply(simp add: storev_def loadv_def)
  apply(cases "blk = 0"; simp)
  apply(cases mc; cases x; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def)
  subgoal for x2
    using n_not_Suc_n option.inject
    apply (cases mc1; force)
    done
  subgoal
    using One_nat_def option.inject zero_neq_one not_gr_zero memory_chunk_value_of_u64_def
    apply (cases mc1)
    apply force
    apply force
    apply force
    apply force
    done
  subgoal
    using One_nat_def option.inject zero_neq_one memory_chunk_value_of_u64_def
    apply (cases mc1)
    apply force
    apply force
    apply force
    apply force
    done
  subgoal
    using One_nat_def option.inject zero_neq_one memory_chunk_value_of_u64_def
    apply (cases mc1)
    apply force
    apply force
    apply force
    apply force
    done
  done

lemma store_load_other_blk:"storev mc m (Vptr blk off) x = Some m' \<Longrightarrow>
  loadv mc1 m' (Vlong place) = Some v \<longleftrightarrow> loadv mc1 m (Vlong place) = Some v"
  using store_load_other_blk_only_if store_load_other_blk_if by blast

lemma store_load_other_blk2_0:"blk \<noteq> blk1 \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m (Vptr blk1 off1) = Some v \<Longrightarrow> loadv mc1 m' (Vptr blk1 off1) = Some v"
  apply(simp add: storev_def loadv_def memory_chunk_to_byte_int_def)
  apply(cases "blk = 0"; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
  apply(cases mc; cases x; simp)
  subgoal for x2
    apply (cases "blk1 = 0"; simp)
    using n_not_Suc_n option.inject
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def option_val_of_u64_def; auto)
    done
  subgoal for x3
    apply (cases "blk1 = 0"; simp)
    using  option.inject zero_neq_one
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    using not_gr_zero option_u64_of_u8_1_def option_val_of_u64_def apply fastforce
    apply (metis option_u64_of_u8_2_def option_val_of_u64_def)
    using nat_neq_iff option_u64_of_u8_4_def option_val_of_u64_def apply fastforce
    using linorder_neq_iff option_u64_of_u8_8_def option_val_of_u64_def by fastforce

  subgoal for x4
    apply (cases "blk1 = 0"; simp)
    using  option.inject zero_neq_one
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    using not_gr_zero option_u64_of_u8_1_def option_val_of_u64_def apply fastforce
    apply (metis option_u64_of_u8_2_def option_val_of_u64_def)
    using nat_neq_iff option_u64_of_u8_4_def option_val_of_u64_def apply fastforce
    using linorder_neq_iff option_u64_of_u8_8_def option_val_of_u64_def by fastforce

  subgoal for x5
    apply (cases "blk1 = 0"; simp)
    using  option.inject zero_neq_one
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    using not_gr_zero option_u64_of_u8_1_def option_val_of_u64_def apply fastforce
    apply (metis option_u64_of_u8_2_def option_val_of_u64_def)
    using nat_neq_iff option_u64_of_u8_4_def option_val_of_u64_def apply fastforce
    using linorder_neq_iff option_u64_of_u8_8_def option_val_of_u64_def by fastforce
  done

lemma store_load_other_blk2_0_0:"blk \<noteq> blk1 \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m' (Vptr blk1 off1) = Some v \<Longrightarrow> loadv mc1 m (Vptr blk1 off1) = Some v"
  apply(simp add: storev_def loadv_def memory_chunk_to_byte_int_def)
  apply(cases "blk = 0"; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
  apply(cases mc; cases x; simp)
  subgoal for x2
    apply (cases "blk1 = 0"; simp)
    using n_not_Suc_n option.inject
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def option_val_of_u64_def; auto)
    done
  subgoal for x3
    apply (cases "blk1 = 0"; simp)
    using  option.inject zero_neq_one
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    using not_gr_zero option_u64_of_u8_1_def option_val_of_u64_def apply fastforce
    apply (metis option_u64_of_u8_2_def option_val_of_u64_def)
    using nat_neq_iff option_u64_of_u8_4_def option_val_of_u64_def apply fastforce
    using linorder_neq_iff option_u64_of_u8_8_def option_val_of_u64_def by fastforce

  subgoal for x4
    apply (cases "blk1 = 0"; simp)
    using  option.inject zero_neq_one
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    using not_gr_zero option_u64_of_u8_1_def option_val_of_u64_def apply fastforce
    apply (metis option_u64_of_u8_2_def option_val_of_u64_def)
    using nat_neq_iff option_u64_of_u8_4_def option_val_of_u64_def apply fastforce
    using linorder_neq_iff option_u64_of_u8_8_def option_val_of_u64_def by fastforce

  subgoal for x5
    apply (cases "blk1 = 0"; simp)
    using  option.inject zero_neq_one
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    using not_gr_zero option_u64_of_u8_1_def option_val_of_u64_def apply fastforce
    apply (metis option_u64_of_u8_2_def option_val_of_u64_def)
    using nat_neq_iff option_u64_of_u8_4_def option_val_of_u64_def apply fastforce
    using linorder_neq_iff option_u64_of_u8_8_def option_val_of_u64_def by fastforce
  done

lemma store_load_other_blk2_1:"((uint off) + memory_chunk_to_byte_int mc < (uint off1)) \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m (Vptr blk off1) = Some v \<Longrightarrow> loadv mc1 m' (Vptr blk off1) = Some v"
  apply(simp add: storev_def loadv_def memory_chunk_to_byte_int_def)
  apply(cases "blk = 0"; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
  apply(cases mc; cases x; simp)
  subgoal for x2
    using n_not_Suc_n option.inject
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  done

lemma store_load_other_blk2_1_0:"((uint off) + memory_chunk_to_byte_int mc < (uint off1)) \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m' (Vptr blk off1) = Some v \<Longrightarrow> loadv mc1 m (Vptr blk off1) = Some v"
  apply(simp add: storev_def loadv_def memory_chunk_to_byte_int_def)
  apply(cases "blk = 0"; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
  apply(cases mc; cases x; simp)
  subgoal for x2
    using n_not_Suc_n option.inject
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  done

lemma store_load_other_blk2_2:"((uint off1) + memory_chunk_to_byte_int mc1 < (uint off)) \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m (Vptr blk off1) = Some v \<Longrightarrow> loadv mc1 m' (Vptr blk off1) = Some v"
  apply(simp add: storev_def loadv_def memory_chunk_to_byte_int_def)
  apply(cases "blk = 0"; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
  apply(cases mc; cases x; simp)
  subgoal for x2
    using n_not_Suc_n option.inject
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  done

lemma store_load_other_blk2_2_0:"((uint off1) + memory_chunk_to_byte_int mc1 < (uint off)) \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m' (Vptr blk off1) = Some v \<Longrightarrow> loadv mc1 m (Vptr blk off1) = Some v"
  apply(simp add: storev_def loadv_def memory_chunk_to_byte_int_def)
  apply(cases "blk = 0"; simp add: Let_def option_val_of_u64_def
        option_u64_of_u8_1_def option_u64_of_u8_2_def
        option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
  apply(cases mc; cases x; simp)
  subgoal for x2
    using n_not_Suc_n option.inject
    apply (cases mc1; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  subgoal for x3
    using  option.inject zero_neq_one
    apply (cases mc1; cases "m blk (uint off1)"; simp add: option_u64_of_u8_1_def option_u64_of_u8_2_def
      option_u64_of_u8_4_def option_u64_of_u8_8_def memory_chunk_value_of_u64_def
      u8_list_of_u16_def Let_def)
    done
  done


lemma store_load_other_blk2:" (blk \<noteq> blk1) \<or>
  (blk = blk1 \<and>(uint off) + memory_chunk_to_byte_int mc < (uint off1)) \<or>
  (blk = blk1 \<and>(uint off1) + memory_chunk_to_byte_int mc1 < (uint off)) \<Longrightarrow>
  Some m' = storev mc m (Vptr blk off) x  \<Longrightarrow>
  loadv mc1 m (Vptr blk1 off1) = Some v \<longleftrightarrow> loadv mc1 m' (Vptr blk1 off1) = Some v"
  using store_load_other_blk2_0 store_load_other_blk2_1 store_load_other_blk2_2
  store_load_other_blk2_0_0 store_load_other_blk2_1_0 store_load_other_blk2_2_0
  by metis 

lemma storev_stack_some: "\<exists> m'. storev M64 m (Vptr sp_block ofs) (Vlong v) = Some m'"
  apply (simp add: storev_def sp_block_def)
  by metis

end
