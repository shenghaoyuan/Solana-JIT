module Jit_eval : sig
  type num
  type myint
  type nat
  type 'a word
  type 'a bit0
  type num1
  type bpf_instruction
  val jit_evaluation : myint list -> myint list -> bool
  val int_of_standard_int : int64 -> myint
  val int_list_of_standard_int_list : int64 list -> myint list
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

type myint = Zero_int | Pos of num | Neg of num;;

let rec times_inta k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
                     | Neg m, Pos n -> Neg (times_num m n)
                     | Pos m, Neg n -> Neg (times_num m n)
                     | Pos m, Pos n -> Pos (times_num m n)
                     | Zero_int, l -> Zero_int
                     | k, Zero_int -> Zero_int;;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_int = ({times = times_inta} : myint times);;

let dvd_int = ({times_dvd = times_int} : myint dvd);;

let one_inta : myint = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : myint one);;

let rec uminus_inta = function Neg m -> Pos m
                      | Pos m -> Neg m
                      | Zero_int -> Zero_int;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec minus_inta k l = match k, l with Neg m, Neg n -> sub n m
                     | Neg m, Pos n -> Neg (plus_num m n)
                     | Pos m, Neg n -> Pos (plus_num m n)
                     | Pos m, Pos n -> sub m n
                     | Zero_int, l -> uminus_inta l
                     | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with
    Bit0 m, Bit1 n -> minus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_inta k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
                | Neg m, Pos n -> sub n m
                | Pos m, Neg n -> sub m n
                | Pos m, Pos n -> Pos (plus_num m n)
                | Zero_int, l -> l
                | k, Zero_int -> k;;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add;
    semiring_0_cancel_ring : 'a semiring_0_cancel};;

let plus_int = ({plus = plus_inta} : myint plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : myint semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    myint cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    myint ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : myint minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : myint cancel_ab_semigroup_add);;

let zero_int = ({zero = Zero_int} : myint zero);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    myint monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : myint comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : myint cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : myint mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : myint semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : myint semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : myint semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : myint semiring_0_cancel);;

let uminus_int = ({uminus = uminus_inta} : myint uminus);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : myint group_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : myint ab_group_add);;

let ring_int =
  ({ab_group_add_ring = ab_group_add_int;
     semiring_0_cancel_ring = semiring_0_cancel_int}
    : myint ring);;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    myint numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_int = ({one_power = one_int; times_power = times_int} : myint power);;

let rec less_eq_num x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
                      | Bit1 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit0 n -> less_eq_num m n
                      | Bit1 m, One -> false
                      | Bit0 m, One -> false
                      | One, n -> true
and less_num m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
               | Bit1 m, Bit1 n -> less_num m n
               | Bit0 m, Bit1 n -> less_eq_num m n
               | Bit0 m, Bit0 n -> less_num m n
               | One, Bit1 n -> true
               | One, Bit0 n -> true
               | m, One -> false;;

let rec less_eq_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_eq_num l k
                      | Neg k, Pos l -> true
                      | Neg k, Zero_int -> true
                      | Pos k, Neg l -> false
                      | Pos k, Pos l -> less_eq_num k l
                      | Pos k, Zero_int -> false
                      | Zero_int, Neg l -> false
                      | Zero_int, Pos l -> true
                      | Zero_int, Zero_int -> true;;

let rec less_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_num l k
                   | Neg k, Pos l -> true
                   | Neg k, Zero_int -> true
                   | Pos k, Neg l -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Zero_int -> false
                   | Zero_int, Neg l -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Zero_int -> false;;

let rec abs_int i = (if less_int i Zero_int then uminus_inta i else i);;

let rec divmod_step_int
  l qr =
    (let (q, r) = qr in
      (if less_eq_int (abs_int l) (abs_int r)
        then (plus_inta (times_inta (Pos (Bit0 One)) q) one_inta,
               minus_inta r l)
        else (times_inta (Pos (Bit0 One)) q, r)));;

let rec divmod_int
  m x1 = match m, x1 with
    Bit1 m, Bit1 n ->
      (if less_num m n then (Zero_int, Pos (Bit1 m))
        else divmod_step_int (Pos (Bit1 n))
               (divmod_int (Bit1 m) (Bit0 (Bit1 n))))
    | Bit0 m, Bit1 n ->
        (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
          else divmod_step_int (Pos (Bit1 n))
                 (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
    | Bit1 m, Bit0 n ->
        (let (q, r) = divmod_int m n in
          (q, plus_inta (times_inta (Pos (Bit0 One)) r) one_inta))
    | Bit0 m, Bit0 n ->
        (let (q, r) = divmod_int m n in (q, times_inta (Pos (Bit0 One)) r))
    | One, Bit1 n -> (Zero_int, Pos One)
    | One, Bit0 n -> (Zero_int, Pos One)
    | m, One -> (Pos m, Zero_int);;

let rec fst (x1, x2) = x1;;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

let rec equal_int x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
                    | Neg k, Pos l -> false
                    | Neg k, Zero_int -> false
                    | Pos k, Neg l -> false
                    | Pos k, Pos l -> equal_num k l
                    | Pos k, Zero_int -> false
                    | Zero_int, Neg l -> false
                    | Zero_int, Pos l -> false
                    | Zero_int, Zero_int -> true;;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    myint zero_neq_one);;

let rec adjust_div
  (q, r) = plus_inta q (of_bool zero_neq_one_int (not (equal_int r Zero_int)));;

let rec divide_inta
  k ka = match k, ka with Neg m, Neg n -> fst (divmod_int m n)
    | Pos m, Neg n -> uminus_inta (adjust_div (divmod_int m n))
    | Neg m, Pos n -> uminus_inta (adjust_div (divmod_int m n))
    | Pos m, Pos n -> fst (divmod_int m n)
    | k, Neg One -> uminus_inta k
    | k, Pos One -> k
    | Zero_int, k -> Zero_int
    | k, Zero_int -> Zero_int;;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

let divide_int = ({divide = divide_inta} : myint divide);;

let rec snd (x1, x2) = x2;;

let rec adjust_mod
  l r = (if equal_int r Zero_int then Zero_int else minus_inta (Pos l) r);;

let rec modulo_inta
  k ka = match k, ka with Neg m, Neg n -> uminus_inta (snd (divmod_int m n))
    | Pos m, Neg n -> uminus_inta (adjust_mod n (snd (divmod_int m n)))
    | Neg m, Pos n -> adjust_mod n (snd (divmod_int m n))
    | Pos m, Pos n -> snd (divmod_int m n)
    | k, Neg One -> Zero_int
    | k, Pos One -> Zero_int
    | Zero_int, k -> Zero_int
    | k, Zero_int -> k;;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_int =
  ({divide_modulo = divide_int; dvd_modulo = dvd_int; modulo = modulo_inta} :
    myint modulo);;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral};;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : myint monoid_mult);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : myint semiring_numeral);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : myint semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : myint semiring_1_cancel);;

let neg_numeral_int =
  ({group_add_neg_numeral = group_add_int; numeral_neg_numeral = numeral_int} :
    myint neg_numeral);;

let ring_1_int =
  ({neg_numeral_ring_1 = neg_numeral_int; ring_ring_1 = ring_int;
     semiring_1_cancel_ring_1 = semiring_1_cancel_int}
    : myint ring_1);;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel;
    ring_comm_ring : 'a ring};;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    myint ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : myint comm_semiring);;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : myint comm_semiring_0);;

let comm_semiring_0_cancel_int =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
    : myint comm_semiring_0_cancel);;

let comm_ring_int =
  ({comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int;
     ring_comm_ring = ring_int}
    : myint comm_ring);;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring;
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel;
    ring_1_comm_ring_1 : 'a ring_1};;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : myint comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : myint comm_semiring_1);;

let comm_semiring_1_cancel_int =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
    : myint comm_semiring_1_cancel);;

let comm_ring_1_int =
  ({comm_ring_comm_ring_1 = comm_ring_int;
     comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int;
     ring_1_comm_ring_1 = ring_1_int}
    : myint comm_ring_1);;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semiring_parity =
  {semiring_modulo_semiring_parity : 'a semiring_modulo};;

type 'a ring_parity =
  {semiring_parity_ring_parity : 'a semiring_parity;
    comm_ring_1_ring_parity : 'a comm_ring_1};;

let semiring_modulo_int =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int;
     modulo_semiring_modulo = modulo_int}
    : myint semiring_modulo);;

let semiring_parity_int =
  ({semiring_modulo_semiring_parity = semiring_modulo_int} :
    myint semiring_parity);;

let ring_parity_int =
  ({semiring_parity_ring_parity = semiring_parity_int;
     comm_ring_1_ring_parity = comm_ring_1_int}
    : myint ring_parity);;

type 'a divide_trivial =
  {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
    divide_divide_trivial : 'a divide};;

let divide_trivial_int =
  ({one_divide_trivial = one_int; zero_divide_trivial = zero_int;
     divide_divide_trivial = divide_int}
    : myint divide_trivial);;

type nat = Zero_nat | Suc of nat;;

let rec inc = function One -> Bit0 One
              | Bit0 x -> Bit1 x
              | Bit1 x -> Bit0 (inc x);;

let rec bit_int
  x0 n = match x0, n with Neg (Bit1 m), Suc n -> bit_int (Neg (inc m)) n
    | Neg (Bit0 m), Suc n -> bit_int (Neg m) n
    | Pos (Bit1 m), Suc n -> bit_int (Pos m) n
    | Pos (Bit0 m), Suc n -> bit_int (Pos m) n
    | Pos One, Suc n -> false
    | Neg (Bit1 m), Zero_nat -> true
    | Neg (Bit0 m), Zero_nat -> false
    | Pos (Bit1 m), Zero_nat -> true
    | Pos (Bit0 m), Zero_nat -> false
    | Pos One, Zero_nat -> true
    | Neg One, n -> true
    | Zero_int, n -> false;;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};;

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity;
    semiring_modulo_trivial_semiring_bits : 'a semiring_modulo_trivial;
    bit : 'a -> nat -> bool};;
let bit _A = _A.bit;;

let semiring_modulo_trivial_int =
  ({divide_trivial_semiring_modulo_trivial = divide_trivial_int;
     semiring_modulo_semiring_modulo_trivial = semiring_modulo_int}
    : myint semiring_modulo_trivial);;

let semiring_bits_int =
  ({semiring_parity_semiring_bits = semiring_parity_int;
     semiring_modulo_trivial_semiring_bits = semiring_modulo_trivial_int;
     bit = bit_int}
    : myint semiring_bits);;

let rec push_bit_int
  x0 i = match x0, i with Suc n, i -> push_bit_int n (dup i)
    | Zero_nat, i -> i;;

let rec or_num x0 x1 = match x0, x1 with One, One -> One
                 | One, Bit0 n -> Bit1 n
                 | One, Bit1 n -> Bit1 n
                 | Bit0 m, One -> Bit1 m
                 | Bit0 m, Bit0 n -> Bit0 (or_num m n)
                 | Bit0 m, Bit1 n -> Bit1 (or_num m n)
                 | Bit1 m, One -> Bit1 m
                 | Bit1 m, Bit0 n -> Bit1 (or_num m n)
                 | Bit1 m, Bit1 n -> Bit1 (or_num m n);;

let rec numeral _A
  = function
    Bit1 n ->
      (let m = numeral _A n in
        plus _A.semigroup_add_numeral.plus_semigroup_add
          (plus _A.semigroup_add_numeral.plus_semigroup_add m m)
          (one _A.one_numeral))
    | Bit0 n ->
        (let m = numeral _A n in
          plus _A.semigroup_add_numeral.plus_semigroup_add m m)
    | One -> one _A.one_numeral;;

let rec suba _A
  k l = minus _A.group_add_neg_numeral.minus_group_add
          (numeral _A.numeral_neg_numeral k)
          (numeral _A.numeral_neg_numeral l);;

let rec not_int = function Neg n -> suba neg_numeral_int n One
                  | Pos n -> Neg (inc n)
                  | Zero_int -> uminus_inta one_inta;;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec and_not_num
  x0 x1 = match x0, x1 with One, One -> None
    | One, Bit0 n -> Some One
    | One, Bit1 n -> None
    | Bit0 m, One -> Some (Bit0 m)
    | Bit0 m, Bit0 n -> map_option (fun a -> Bit0 a) (and_not_num m n)
    | Bit0 m, Bit1 n -> map_option (fun a -> Bit0 a) (and_not_num m n)
    | Bit1 m, One -> Some (Bit0 m)
    | Bit1 m, Bit0 n ->
        (match and_not_num m n with None -> Some One
          | Some na -> Some (Bit1 na))
    | Bit1 m, Bit1 n -> map_option (fun a -> Bit0 a) (and_not_num m n);;

let rec or_not_num_neg x0 x1 = match x0, x1 with One, One -> One
                         | One, Bit0 m -> Bit1 m
                         | One, Bit1 m -> Bit1 m
                         | Bit0 n, One -> Bit0 One
                         | Bit0 n, Bit0 m -> bitM (or_not_num_neg n m)
                         | Bit0 n, Bit1 m -> Bit0 (or_not_num_neg n m)
                         | Bit1 n, One -> One
                         | Bit1 n, Bit0 m -> bitM (or_not_num_neg n m)
                         | Bit1 n, Bit1 m -> bitM (or_not_num_neg n m);;

let rec and_num
  x0 x1 = match x0, x1 with One, One -> Some One
    | One, Bit0 n -> None
    | One, Bit1 n -> Some One
    | Bit0 m, One -> None
    | Bit0 m, Bit0 n -> map_option (fun a -> Bit0 a) (and_num m n)
    | Bit0 m, Bit1 n -> map_option (fun a -> Bit0 a) (and_num m n)
    | Bit1 m, One -> Some One
    | Bit1 m, Bit0 n -> map_option (fun a -> Bit0 a) (and_num m n)
    | Bit1 m, Bit1 n ->
        (match and_num m n with None -> Some One | Some na -> Some (Bit1 na));;

let rec and_int
  i j = match i, j with
    Neg (Bit1 n), Pos m -> suba neg_numeral_int (or_not_num_neg (Bit0 n) m) One
    | Neg (Bit0 n), Pos m ->
        suba neg_numeral_int (or_not_num_neg (bitM n) m) One
    | Neg One, Pos m -> Pos m
    | Pos n, Neg (Bit1 m) ->
        suba neg_numeral_int (or_not_num_neg (Bit0 m) n) One
    | Pos n, Neg (Bit0 m) ->
        suba neg_numeral_int (or_not_num_neg (bitM m) n) One
    | Pos n, Neg One -> Pos n
    | Neg n, Neg m ->
        not_int
          (or_int (suba neg_numeral_int n One) (suba neg_numeral_int m One))
    | Pos n, Pos m ->
        (match and_num n m with None -> Zero_int | Some a -> Pos a)
    | i, Zero_int -> Zero_int
    | Zero_int, j -> Zero_int
and or_int
  i j = match i, j with
    Neg (Bit1 n), Pos m ->
      (match and_not_num (Bit0 n) m with None -> uminus_inta one_inta
        | Some na -> Neg (inc na))
    | Neg (Bit0 n), Pos m ->
        (match and_not_num (bitM n) m with None -> uminus_inta one_inta
          | Some na -> Neg (inc na))
    | Neg One, Pos m -> Neg One
    | Pos n, Neg (Bit1 m) ->
        (match and_not_num (Bit0 m) n with None -> uminus_inta one_inta
          | Some na -> Neg (inc na))
    | Pos n, Neg (Bit0 m) ->
        (match and_not_num (bitM m) n with None -> uminus_inta one_inta
          | Some na -> Neg (inc na))
    | Pos n, Neg One -> Neg One
    | Neg n, Neg m ->
        not_int
          (and_int (suba neg_numeral_int n One) (suba neg_numeral_int m One))
    | Pos n, Pos m -> Pos (or_num n m)
    | i, Zero_int -> i
    | Zero_int, j -> j;;

let rec unset_bit_int n k = and_int k (not_int (push_bit_int n one_inta));;

let rec power _A a x1 = match a, x1 with a, Zero_nat -> one _A.one_power
                   | a, Suc n -> times _A.times_power a (power _A a n);;

let rec take_bit_int n k = modulo_inta k (power power_int (Pos (Bit0 One)) n);;

let rec xor_num
  x0 x1 = match x0, x1 with One, One -> None
    | One, Bit0 n -> Some (Bit1 n)
    | One, Bit1 n -> Some (Bit0 n)
    | Bit0 m, One -> Some (Bit1 m)
    | Bit0 m, Bit0 n -> map_option (fun a -> Bit0 a) (xor_num m n)
    | Bit0 m, Bit1 n ->
        Some (match xor_num m n with None -> One | Some a -> Bit1 a)
    | Bit1 m, One -> Some (Bit0 m)
    | Bit1 m, Bit0 n ->
        Some (match xor_num m n with None -> One | Some a -> Bit1 a)
    | Bit1 m, Bit1 n -> map_option (fun a -> Bit0 a) (xor_num m n);;

let rec xor_int
  i j = match i, j with
    Pos n, Neg m -> not_int (xor_int (Pos n) (suba neg_numeral_int m One))
    | Neg n, Pos m -> not_int (xor_int (suba neg_numeral_int n One) (Pos m))
    | Neg n, Neg m ->
        xor_int (suba neg_numeral_int n One) (suba neg_numeral_int m One)
    | Pos n, Pos m ->
        (match xor_num n m with None -> Zero_int | Some a -> Pos a)
    | i, Zero_int -> i
    | Zero_int, j -> j;;

let rec flip_bit_int n k = xor_int k (push_bit_int n one_inta);;

let rec drop_bit_int
  x0 i = match x0, i with Suc n, Neg (Bit1 m) -> drop_bit_int n (Neg (inc m))
    | Suc n, Neg (Bit0 m) -> drop_bit_int n (Neg m)
    | Suc n, Neg One -> uminus_inta one_inta
    | Suc n, Pos (Bit1 m) -> drop_bit_int n (Pos m)
    | Suc n, Pos (Bit0 m) -> drop_bit_int n (Pos m)
    | Suc n, Pos One -> Zero_int
    | Suc n, Zero_int -> Zero_int
    | Zero_nat, i -> i;;

let rec set_bit_int n k = or_int k (push_bit_int n one_inta);;

let rec mask_int n = minus_inta (power power_int (Pos (Bit0 One)) n) one_inta;;

type 'a semiring_bit_operations =
  {semiring_bits_semiring_bit_operations : 'a semiring_bits;
    anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
    mask : nat -> 'a; set_bit : nat -> 'a -> 'a; unset_bit : nat -> 'a -> 'a;
    flip_bit : nat -> 'a -> 'a; push_bit : nat -> 'a -> 'a;
    drop_bit : nat -> 'a -> 'a; take_bit : nat -> 'a -> 'a};;
let anda _A = _A.anda;;
let ora _A = _A.ora;;
let xor _A = _A.xor;;
let mask _A = _A.mask;;
let set_bit _A = _A.set_bit;;
let unset_bit _A = _A.unset_bit;;
let flip_bit _A = _A.flip_bit;;
let push_bit _A = _A.push_bit;;
let drop_bit _A = _A.drop_bit;;
let take_bit _A = _A.take_bit;;

type 'a ring_bit_operations =
  {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
    ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a};;
let nota _A = _A.nota;;

let semiring_bit_operations_int =
  ({semiring_bits_semiring_bit_operations = semiring_bits_int; anda = and_int;
     ora = or_int; xor = xor_int; mask = mask_int; set_bit = set_bit_int;
     unset_bit = unset_bit_int; flip_bit = flip_bit_int;
     push_bit = push_bit_int; drop_bit = drop_bit_int; take_bit = take_bit_int}
    : myint semiring_bit_operations);;

let ring_bit_operations_int =
  ({semiring_bit_operations_ring_bit_operations = semiring_bit_operations_int;
     ring_parity_ring_bit_operations = ring_parity_int; nota = not_int}
    : myint ring_bit_operations);;

type 'a itself = Type;;

type 'a len0 = {len_of : 'a itself -> nat};;
let len_of _A = _A.len_of;;

type 'a len = {len0_len : 'a len0};;

type 'a word = Word of myint;;

let rec one_worda _A = Word one_inta;;

let rec one_word _A = ({one = one_worda _A} : 'a word one);;

let rec the_int _A (Word x) = x;;

let rec of_int _A k = Word (take_bit_int (len_of _A.len0_len Type) k);;

let rec times_worda _A
  a b = of_int _A (times_inta (the_int _A a) (the_int _A b));;

let rec times_word _A = ({times = times_worda _A} : 'a word times);;

let rec power_word _A =
  ({one_power = (one_word _A); times_power = (times_word _A)} : 'a word power);;

let rec plus_nat x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
                   | Zero_nat, n -> n;;

let rec times_nat x0 n = match x0, n with Zero_nat, n -> Zero_nat
                    | Suc m, n -> plus_nat n (times_nat m n);;

let one_nat : nat = Suc Zero_nat;;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nat m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nat m m)
    | One -> one_nat;;

type 'a finite = unit;;

type 'a bit0 = Abs_bit0 of myint;;

let rec len_of_bit0 _A uu = times_nat (nat_of_num (Bit0 One)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

let rec len_bit0 _A = ({len0_len = (len0_bit0 _A.len0_len)} : 'a bit0 len);;

type num1 = One_num1;;

let rec len_of_num1 uu = one_nat;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

let len_num1 = ({len0_len = len0_num1} : num1 len);;

type 'a signed = EMPTY__;;

let rec len_of_signed _A x = len_of _A Type;;

let rec len0_signed _A = ({len_of = len_of_signed _A} : 'a signed len0);;

let rec len_signed _A =
  ({len0_len = (len0_signed _A.len0_len)} : 'a signed len);;

type ireg = RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP | R8 | R9 | R10 | R11
  | R12 | R13 | R14 | R15;;

type memory_chunk = M8 | M16 | M32 | M64;;

type binop = BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND | BPF_LSH
  | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV | BPF_ARSH;;

type pqrop = BPF_LMUL | BPF_UDIV | BPF_UREM | BPF_SDIV | BPF_SREM;;

type pqrop2 = BPF_UHMUL | BPF_SHMUL;;

type bpf_ireg = BR0 | BR1 | BR2 | BR3 | BR4 | BR5 | BR6 | BR7 | BR8 | BR9 |
  BR10;;

type snd_op = SOImm of num1 bit0 bit0 bit0 bit0 bit0 signed word |
  SOReg of bpf_ireg;;

type addrmode =
  Addrmode of
    ireg option * (ireg * num1 bit0 bit0 bit0 word) option *
      num1 bit0 bit0 bit0 bit0 bit0 word;;

type testcond = Cond_e | Cond_ne | Cond_b | Cond_be | Cond_ae | Cond_a | Cond_l
  | Cond_le | Cond_ge | Cond_g | Cond_p | Cond_np;;

type condition = Eq | Gt | Ge | Lt | Le | SEt | Ne | SGt | SGe | SLt | SLe;;

type instruction = Paddq_rr of ireg * ireg | Pret | Ppushl_r of ireg |
  Ppopl of ireg | Pmovq_rr of ireg * ireg |
  Pmovq_ri of ireg * num1 bit0 bit0 bit0 bit0 bit0 bit0 word | Pmulq_r of ireg |
  Pjcc of testcond * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  Pcmpq_rr of ireg * ireg | Pmov_mr of addrmode * ireg * memory_chunk |
  Pxchgq_rr of ireg * ireg | Pshrq_r of ireg | Pshlq_r of ireg | Psarq_r of ireg
  | Pmov_rm of ireg * addrmode * memory_chunk |
  Pcall_i of num1 bit0 bit0 bit0 bit0 bit0 word;;

type bpf_instruction =
  BPF_LD_IMM of
    bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word *
      num1 bit0 bit0 bit0 bit0 bit0 signed word
  | BPF_LDX of
      memory_chunk * bpf_ireg * bpf_ireg * num1 bit0 bit0 bit0 bit0 signed word
  | BPF_ST of
      memory_chunk * bpf_ireg * snd_op * num1 bit0 bit0 bit0 bit0 signed word
  | BPF_ADD_STK of num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_ALU of binop * bpf_ireg * snd_op | BPF_NEG32_REG of bpf_ireg |
  BPF_LE of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_BE of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_ALU64 of binop * bpf_ireg * snd_op | BPF_NEG64_REG of bpf_ireg |
  BPF_HOR64_IMM of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_PQR of pqrop * bpf_ireg * snd_op | BPF_PQR64 of pqrop * bpf_ireg * snd_op
  | BPF_PQR2 of pqrop2 * bpf_ireg * snd_op |
  BPF_JA of num1 bit0 bit0 bit0 bit0 signed word |
  BPF_JUMP of
    condition * bpf_ireg * snd_op * num1 bit0 bit0 bit0 bit0 signed word
  | BPF_CALL_REG of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_CALL_IMM of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_EXIT;;

let rec nat = function Pos k -> nat_of_num k
              | Zero_int -> Zero_nat
              | Neg k -> Zero_nat;;

let rec nth x0 x1 = match x0, x1 with x :: xs, Suc n -> nth xs n
              | x :: xs, Zero_nat -> x;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_int _B w));;

let rec butlast = function [] -> []
                  | x :: xs -> (if null xs then [] else x :: butlast xs);;

let rec the_nat _A w = nat (the_int _A w);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec is_none = function Some x -> false
                  | None -> true;;

let iNSN_SIZE : nat = nat_of_num (Bit0 (Bit0 (Bit0 One)));;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (Suc n) xs
                     | n, [] -> n;;

let rec signed_take_bit _A
  n a = (let l =
           take_bit _A.semiring_bit_operations_ring_bit_operations (Suc n) a in
          (if bit _A.semiring_bit_operations_ring_bit_operations.semiring_bits_semiring_bit_operations
                l n
            then plus _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.semigroup_add_numeral.plus_semigroup_add
                   l (push_bit _A.semiring_bit_operations_ring_bit_operations
                       (Suc n)
                       (uminus
                         _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.uminus_group_add
                         (one _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.one_numeral)))
            else l));;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec the_signed_int _A
  w = signed_take_bit ring_bit_operations_int
        (minus_nat (len_of _A.len0_len Type) (Suc Zero_nat)) (the_int _A w);;

let rec signed_cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_signed_int _B w));;

let rec equal_ireg x0 x1 = match x0, x1 with R14, R15 -> false
                     | R15, R14 -> false
                     | R13, R15 -> false
                     | R15, R13 -> false
                     | R13, R14 -> false
                     | R14, R13 -> false
                     | R12, R15 -> false
                     | R15, R12 -> false
                     | R12, R14 -> false
                     | R14, R12 -> false
                     | R12, R13 -> false
                     | R13, R12 -> false
                     | R11, R15 -> false
                     | R15, R11 -> false
                     | R11, R14 -> false
                     | R14, R11 -> false
                     | R11, R13 -> false
                     | R13, R11 -> false
                     | R11, R12 -> false
                     | R12, R11 -> false
                     | R10, R15 -> false
                     | R15, R10 -> false
                     | R10, R14 -> false
                     | R14, R10 -> false
                     | R10, R13 -> false
                     | R13, R10 -> false
                     | R10, R12 -> false
                     | R12, R10 -> false
                     | R10, R11 -> false
                     | R11, R10 -> false
                     | R9, R15 -> false
                     | R15, R9 -> false
                     | R9, R14 -> false
                     | R14, R9 -> false
                     | R9, R13 -> false
                     | R13, R9 -> false
                     | R9, R12 -> false
                     | R12, R9 -> false
                     | R9, R11 -> false
                     | R11, R9 -> false
                     | R9, R10 -> false
                     | R10, R9 -> false
                     | R8, R15 -> false
                     | R15, R8 -> false
                     | R8, R14 -> false
                     | R14, R8 -> false
                     | R8, R13 -> false
                     | R13, R8 -> false
                     | R8, R12 -> false
                     | R12, R8 -> false
                     | R8, R11 -> false
                     | R11, R8 -> false
                     | R8, R10 -> false
                     | R10, R8 -> false
                     | R8, R9 -> false
                     | R9, R8 -> false
                     | RSP, R15 -> false
                     | R15, RSP -> false
                     | RSP, R14 -> false
                     | R14, RSP -> false
                     | RSP, R13 -> false
                     | R13, RSP -> false
                     | RSP, R12 -> false
                     | R12, RSP -> false
                     | RSP, R11 -> false
                     | R11, RSP -> false
                     | RSP, R10 -> false
                     | R10, RSP -> false
                     | RSP, R9 -> false
                     | R9, RSP -> false
                     | RSP, R8 -> false
                     | R8, RSP -> false
                     | RBP, R15 -> false
                     | R15, RBP -> false
                     | RBP, R14 -> false
                     | R14, RBP -> false
                     | RBP, R13 -> false
                     | R13, RBP -> false
                     | RBP, R12 -> false
                     | R12, RBP -> false
                     | RBP, R11 -> false
                     | R11, RBP -> false
                     | RBP, R10 -> false
                     | R10, RBP -> false
                     | RBP, R9 -> false
                     | R9, RBP -> false
                     | RBP, R8 -> false
                     | R8, RBP -> false
                     | RBP, RSP -> false
                     | RSP, RBP -> false
                     | RDI, R15 -> false
                     | R15, RDI -> false
                     | RDI, R14 -> false
                     | R14, RDI -> false
                     | RDI, R13 -> false
                     | R13, RDI -> false
                     | RDI, R12 -> false
                     | R12, RDI -> false
                     | RDI, R11 -> false
                     | R11, RDI -> false
                     | RDI, R10 -> false
                     | R10, RDI -> false
                     | RDI, R9 -> false
                     | R9, RDI -> false
                     | RDI, R8 -> false
                     | R8, RDI -> false
                     | RDI, RSP -> false
                     | RSP, RDI -> false
                     | RDI, RBP -> false
                     | RBP, RDI -> false
                     | RSI, R15 -> false
                     | R15, RSI -> false
                     | RSI, R14 -> false
                     | R14, RSI -> false
                     | RSI, R13 -> false
                     | R13, RSI -> false
                     | RSI, R12 -> false
                     | R12, RSI -> false
                     | RSI, R11 -> false
                     | R11, RSI -> false
                     | RSI, R10 -> false
                     | R10, RSI -> false
                     | RSI, R9 -> false
                     | R9, RSI -> false
                     | RSI, R8 -> false
                     | R8, RSI -> false
                     | RSI, RSP -> false
                     | RSP, RSI -> false
                     | RSI, RBP -> false
                     | RBP, RSI -> false
                     | RSI, RDI -> false
                     | RDI, RSI -> false
                     | RDX, R15 -> false
                     | R15, RDX -> false
                     | RDX, R14 -> false
                     | R14, RDX -> false
                     | RDX, R13 -> false
                     | R13, RDX -> false
                     | RDX, R12 -> false
                     | R12, RDX -> false
                     | RDX, R11 -> false
                     | R11, RDX -> false
                     | RDX, R10 -> false
                     | R10, RDX -> false
                     | RDX, R9 -> false
                     | R9, RDX -> false
                     | RDX, R8 -> false
                     | R8, RDX -> false
                     | RDX, RSP -> false
                     | RSP, RDX -> false
                     | RDX, RBP -> false
                     | RBP, RDX -> false
                     | RDX, RDI -> false
                     | RDI, RDX -> false
                     | RDX, RSI -> false
                     | RSI, RDX -> false
                     | RCX, R15 -> false
                     | R15, RCX -> false
                     | RCX, R14 -> false
                     | R14, RCX -> false
                     | RCX, R13 -> false
                     | R13, RCX -> false
                     | RCX, R12 -> false
                     | R12, RCX -> false
                     | RCX, R11 -> false
                     | R11, RCX -> false
                     | RCX, R10 -> false
                     | R10, RCX -> false
                     | RCX, R9 -> false
                     | R9, RCX -> false
                     | RCX, R8 -> false
                     | R8, RCX -> false
                     | RCX, RSP -> false
                     | RSP, RCX -> false
                     | RCX, RBP -> false
                     | RBP, RCX -> false
                     | RCX, RDI -> false
                     | RDI, RCX -> false
                     | RCX, RSI -> false
                     | RSI, RCX -> false
                     | RCX, RDX -> false
                     | RDX, RCX -> false
                     | RBX, R15 -> false
                     | R15, RBX -> false
                     | RBX, R14 -> false
                     | R14, RBX -> false
                     | RBX, R13 -> false
                     | R13, RBX -> false
                     | RBX, R12 -> false
                     | R12, RBX -> false
                     | RBX, R11 -> false
                     | R11, RBX -> false
                     | RBX, R10 -> false
                     | R10, RBX -> false
                     | RBX, R9 -> false
                     | R9, RBX -> false
                     | RBX, R8 -> false
                     | R8, RBX -> false
                     | RBX, RSP -> false
                     | RSP, RBX -> false
                     | RBX, RBP -> false
                     | RBP, RBX -> false
                     | RBX, RDI -> false
                     | RDI, RBX -> false
                     | RBX, RSI -> false
                     | RSI, RBX -> false
                     | RBX, RDX -> false
                     | RDX, RBX -> false
                     | RBX, RCX -> false
                     | RCX, RBX -> false
                     | RAX, R15 -> false
                     | R15, RAX -> false
                     | RAX, R14 -> false
                     | R14, RAX -> false
                     | RAX, R13 -> false
                     | R13, RAX -> false
                     | RAX, R12 -> false
                     | R12, RAX -> false
                     | RAX, R11 -> false
                     | R11, RAX -> false
                     | RAX, R10 -> false
                     | R10, RAX -> false
                     | RAX, R9 -> false
                     | R9, RAX -> false
                     | RAX, R8 -> false
                     | R8, RAX -> false
                     | RAX, RSP -> false
                     | RSP, RAX -> false
                     | RAX, RBP -> false
                     | RBP, RAX -> false
                     | RAX, RDI -> false
                     | RDI, RAX -> false
                     | RAX, RSI -> false
                     | RSI, RAX -> false
                     | RAX, RDX -> false
                     | RDX, RAX -> false
                     | RAX, RCX -> false
                     | RCX, RAX -> false
                     | RAX, RBX -> false
                     | RBX, RAX -> false
                     | R15, R15 -> true
                     | R14, R14 -> true
                     | R13, R13 -> true
                     | R12, R12 -> true
                     | R11, R11 -> true
                     | R10, R10 -> true
                     | R9, R9 -> true
                     | R8, R8 -> true
                     | RSP, RSP -> true
                     | RBP, RBP -> true
                     | RDI, RDI -> true
                     | RSI, RSI -> true
                     | RDX, RDX -> true
                     | RCX, RCX -> true
                     | RBX, RBX -> true
                     | RAX, RAX -> true;;

let rec zero_word _A = Word Zero_int;;

let rec bpf_to_x64_reg
  br = (match br with BR0 -> RAX | BR1 -> RSI | BR2 -> RDX | BR3 -> RCX
         | BR4 -> R8 | BR5 -> R9 | BR6 -> R12 | BR7 -> R13 | BR8 -> R14
         | BR9 -> R15 | BR10 -> RBP);;

let rec and_word _A v w = Word (and_int (the_int _A v) (the_int _A w));;

let rec equal_memory_chunk x0 x1 = match x0, x1 with M32, M64 -> false
                             | M64, M32 -> false
                             | M16, M64 -> false
                             | M64, M16 -> false
                             | M16, M32 -> false
                             | M32, M16 -> false
                             | M8, M64 -> false
                             | M64, M8 -> false
                             | M8, M32 -> false
                             | M32, M8 -> false
                             | M8, M16 -> false
                             | M16, M8 -> false
                             | M64, M64 -> true
                             | M32, M32 -> true
                             | M16, M16 -> true
                             | M8, M8 -> true;;

let rec push_bit_word _A
  n w = times_worda _A w
          (power (power_word _A) (of_int _A (Pos (Bit0 One))) n);;

let rec or_word _A v w = Word (or_int (the_int _A v) (the_int _A w));;

let rec not_word _A w = of_int _A (not_int (the_int _A w));;

let rec minus_word _A
  a b = of_int _A (minus_inta (the_int _A a) (the_int _A b));;

let rec bitfield_insert_u8
  pos width n p =
    (let mask =
       push_bit_word (len_bit0 (len_bit0 (len_bit0 len_num1))) pos
         (minus_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (power (power_word (len_bit0 (len_bit0 (len_bit0 len_num1))))
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 One)))
             width)
           (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))))
       in
      or_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (push_bit_word (len_bit0 (len_bit0 (len_bit0 len_num1))) pos
          (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (minus_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (power (power_word (len_bit0 (len_bit0 (len_bit0 len_num1))))
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit0 One)))
                width)
              (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            p))
        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1))) n
          (not_word (len_bit0 (len_bit0 (len_bit0 len_num1))) mask)));;

let rec construct_modsib_to_u8
  op1 op2 op3 =
    bitfield_insert_u8 (nat_of_num (Bit0 (Bit1 One))) (nat_of_num (Bit0 One))
      (bitfield_insert_u8 (nat_of_num (Bit1 One)) (nat_of_num (Bit1 One))
        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit1 One))))
          op3)
        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit1 One))))
          op2))
      op1;;

let rec uminus_word _A a = of_int _A (uminus_inta (the_int _A a));;

let rec u8_of_bool
  b = (match b with true -> one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))
        | false -> zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))));;

let rec construct_rex_to_u8
  w r x b =
    bitfield_insert_u8 (nat_of_num (Bit0 (Bit0 One)))
      (nat_of_num (Bit0 (Bit0 One)))
      (bitfield_insert_u8 (nat_of_num (Bit1 One)) one_nat
        (bitfield_insert_u8 (nat_of_num (Bit0 One)) one_nat
          (bitfield_insert_u8 one_nat one_nat (u8_of_bool b) (u8_of_bool x))
          (u8_of_bool r))
        (u8_of_bool w))
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit0 (Bit0 One))));;

let rec less_eq_word _A a b = less_eq_int (the_int _A a) (the_int _A b);;

let rec equal_word _A v w = equal_int (the_int _A v) (the_int _A w);;

let rec drop_bit_word _A n w = Word (drop_bit_int n (the_int _A w));;

let rec u8_list_of_u64
  i = [cast (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (and_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           i (of_int
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 One)))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))))];;

let rec u8_list_of_u32
  i = [cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (and_word
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) i
           (of_int
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
             (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (drop_bit_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (nat_of_num (Bit0 (Bit0 (Bit0 One)))) i)
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (drop_bit_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))) i)
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (drop_bit_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))))) i)
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))))];;

let rec u8_of_ireg
  = function RAX -> zero_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
    | RCX -> one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))
    | RDX -> of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 One))
    | RBX -> of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 One))
    | RSP ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 (Bit0 One)))
    | RBP ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 (Bit0 One)))
    | RSI ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 (Bit1 One)))
    | RDI ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 (Bit1 One)))
    | R8 -> of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit0 (Bit0 (Bit0 One))))
    | R9 -> of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit1 (Bit0 (Bit0 One))))
    | R10 ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit0 (Bit1 (Bit0 One))))
    | R11 ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit0 One))))
    | R12 ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit0 (Bit0 (Bit1 One))))
    | R13 ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit0 (Bit1 One))))
    | R14 ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit0 (Bit1 (Bit1 One))))
    | R15 ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit1 One))));;

let rec u8_of_cond
  = function
    Cond_b -> of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 One))
    | Cond_ae ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 One))
    | Cond_e ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 (Bit0 One)))
    | Cond_ne ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 (Bit0 One)))
    | Cond_be ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 (Bit1 One)))
    | Cond_a ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 (Bit1 One)))
    | Cond_p ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit0 (Bit1 (Bit0 One))))
    | Cond_np ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit0 One))))
    | Cond_l ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit0 (Bit0 (Bit1 One))))
    | Cond_ge ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit0 (Bit1 One))))
    | Cond_le ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit0 (Bit1 (Bit1 One))))
    | Cond_g ->
        of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit1 One))));;

let rec x64_encode
  ins = (match ins
          with Paddq_rr (rd, r1) ->
            (let rex =
               construct_rex_to_u8 true
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op = one_worda (len_bit0 (len_bit0 (len_bit0 len_num1))) in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (u8_of_ireg r1) (u8_of_ireg rd)
               in
              [rex; op; rop])
          | Pret ->
            [of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))]
          | Ppushl_r r1 ->
            (let rex =
               construct_rex_to_u8 false false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               bitfield_insert_u8 Zero_nat (nat_of_num (Bit1 One))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))
                 (u8_of_ireg r1)
               in
              (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) rex
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                then [op] else [rex; op]))
          | Ppopl rd ->
            (let rex =
               construct_rex_to_u8 false false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               bitfield_insert_u8 Zero_nat (nat_of_num (Bit1 One))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One))))))))
                 (u8_of_ireg rd)
               in
              (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) rex
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                then [op] else [rex; op]))
          | Pmovq_rr (rd, r1) ->
            (let rex =
               construct_rex_to_u8 true
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (u8_of_ireg r1) (u8_of_ireg rd)
               in
              [rex; op; rop])
          | Pmovq_ri (rd, n) ->
            (let rex =
               construct_rex_to_u8 true false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               bitfield_insert_u8 Zero_nat (nat_of_num (Bit1 One))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                 (u8_of_ireg rd)
               in
              [rex; op] @ u8_list_of_u64 n)
          | Pmulq_r r1 ->
            (let rex =
               construct_rex_to_u8 true false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 One))))
                 (u8_of_ireg r1)
               in
              [rex; op; rop])
          | Pjcc (t, d) ->
            (let ex =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit1 One))))
               in
             let op =
               bitfield_insert_u8 Zero_nat (nat_of_num (Bit0 (Bit0 One)))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                 (u8_of_cond t)
               in
              [ex; op] @
                u8_list_of_u32
                  (cast (len_signed
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    d))
          | Pcmpq_rr (r1, r2) ->
            (let rex =
               construct_rex_to_u8 true
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r2)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (u8_of_ireg r1) (u8_of_ireg r2)
               in
              [rex; op; rop])
          | Pmov_mr (Addrmode (Some rb, None, dis), r1, c) ->
            (let rex =
               construct_rex_to_u8 (equal_memory_chunk c M64)
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rb)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
              (if less_eq_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    dis (of_int
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (Pos (Bit1 (Bit1 (Bit1
     (Bit1 (Bit1 (Bit1 One)))))))) ||
                    less_eq_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (uminus_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (of_int
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (Pos (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
                      dis
                then (let disa =
                        signed_cast
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (len_bit0 (len_bit0 (len_bit0 len_num1))) dis
                        in
                      let rop =
                        construct_modsib_to_u8
                          (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1))))
                          (u8_of_ireg r1) (u8_of_ireg rb)
                        in
                       (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             rex (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                         then (match c
                                with M8 ->
                                  [of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa]
                                | M16 ->
                                  [of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
                                    of_int
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      (Pos
(Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa]
                                | M32 ->
                                  [of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit1
    (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa])
                         else (match c
                                with M8 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa]
                                | M16 ->
                                  [of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
                                    rex;
                                    of_int
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      (Pos
(Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa]
                                | M32 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa]
                                | M64 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa])))
                else (let rop =
                        construct_modsib_to_u8
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 One)))
                          (u8_of_ireg r1) (u8_of_ireg rb)
                        in
                       (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             rex (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                         then (let M32 = c in
                                [of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                  rop] @
                                  u8_list_of_u32 dis)
                         else (match c
                                with M32 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop] @
                                    u8_list_of_u32 dis
                                | M64 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop] @
                                    u8_list_of_u32 dis)))))
          | Pmov_mr (Addrmode (Some rb, Some (ri, scale), dis), r1, _) ->
            (let rex =
               construct_rex_to_u8 true
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg ri)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rb)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 One)))
                 (u8_of_ireg r1)
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 One))))
               in
             let sib =
               construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
              [rex; op; rop; sib] @ u8_list_of_u32 dis)
          | Pxchgq_rr (rd, r1) ->
            (let rex =
               construct_rex_to_u8 true
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg r1)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (u8_of_ireg r1) (u8_of_ireg rd)
               in
              [rex; op; rop])
          | Pshrq_r rd ->
            (let rex =
               construct_rex_to_u8 true false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 (Bit0 One))))
                 (u8_of_ireg rd)
               in
              [rex; op; rop])
          | Pshlq_r rd ->
            (let rex =
               construct_rex_to_u8 true false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 One))))
                 (u8_of_ireg rd)
               in
              [rex; op; rop])
          | Psarq_r rd ->
            (let rex =
               construct_rex_to_u8 true false false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 One)))
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 (Bit1 One))))
                 (u8_of_ireg rd)
               in
              [rex; op; rop])
          | Pmov_rm (rd, Addrmode (Some rb, None, dis), c) ->
            (let rex =
               construct_rex_to_u8 (equal_memory_chunk c M64)
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 false
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rb)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
              (if less_eq_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    dis (of_int
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (Pos (Bit1 (Bit1 (Bit1
     (Bit1 (Bit1 (Bit1 One)))))))) ||
                    less_eq_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (uminus_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (of_int
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (Pos (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
                      dis
                then (let disa =
                        signed_cast
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (len_bit0 (len_bit0 (len_bit0 len_num1))) dis
                        in
                      let rop =
                        construct_modsib_to_u8
                          (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1))))
                          (u8_of_ireg rd) (u8_of_ireg rb)
                        in
                       (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             rex (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                         then (let M32 = c in
                                [of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                  rop; disa])
                         else (match c
                                with M32 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa]
                                | M64 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop; disa])))
                else (let rop =
                        construct_modsib_to_u8
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 One)))
                          (u8_of_ireg rd) (u8_of_ireg rb)
                        in
                       (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             rex (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                         then (let M32 = c in
                                [of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                  rop] @
                                  u8_list_of_u32 dis)
                         else (match c
                                with M32 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop] @
                                    u8_list_of_u32 dis
                                | M64 ->
                                  [rex; of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))));
                                    rop] @
                                    u8_list_of_u32 dis)))))
          | Pmov_rm (rd, Addrmode (Some rb, Some (ri, scale), dis), _) ->
            (let rex =
               construct_rex_to_u8 true
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rd)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg ri)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (not (equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (u8_of_ireg rb)
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit0 One))))))
                        (zero_word (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               in
             let op =
               of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
               in
             let rop =
               construct_modsib_to_u8
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 One)))
                 (u8_of_ireg rd)
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 One))))
               in
             let sib =
               construct_modsib_to_u8 scale (u8_of_ireg ri) (u8_of_ireg rb) in
              [rex; op; rop; sib] @ u8_list_of_u32 dis)
          | Pcall_i d ->
            [of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))] @
              u8_list_of_u32 d);;

let rec per_jit_shift_arsh_reg64
  dst src =
    (let _ = equal_ireg (bpf_to_x64_reg dst) RCX in
     let len =
       (match bpf_to_x64_reg dst with RAX -> nat_of_num (Bit0 (Bit0 One))
         | RBX -> nat_of_num (Bit0 (Bit0 One))
         | RCX -> nat_of_num (Bit1 (Bit0 One))
         | RDX -> nat_of_num (Bit0 (Bit0 One))
         | RSI -> nat_of_num (Bit0 (Bit0 One))
         | RDI -> nat_of_num (Bit0 (Bit0 One))
         | RBP -> nat_of_num (Bit0 (Bit0 One))
         | RSP -> nat_of_num (Bit0 (Bit0 One))
         | R8 -> nat_of_num (Bit0 (Bit0 One))
         | R9 -> nat_of_num (Bit0 (Bit0 One))
         | R10 -> nat_of_num (Bit0 (Bit0 One))
         | R11 -> nat_of_num (Bit0 (Bit0 One))
         | R12 -> nat_of_num (Bit0 (Bit0 One))
         | R13 -> nat_of_num (Bit0 (Bit0 One))
         | R14 -> nat_of_num (Bit0 (Bit0 One))
         | R15 -> nat_of_num (Bit0 (Bit0 One)))
       in
     let l_bin =
       (match bpf_to_x64_reg dst
         with RAX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RBX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RCX ->
           x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr (bpf_to_x64_reg dst, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg src)) @
                 x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
                   x64_encode (Ppopl (bpf_to_x64_reg src))
         | RDX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RSI ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RDI ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RBP ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RSP ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R8 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R9 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R10 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R11 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R12 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R13 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R14 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R15 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Psarq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX))
       in
      Some (len, (zero_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
                   l_bin)));;

let rec per_jit_shift_rsh_reg64
  dst src =
    (let _ = equal_ireg (bpf_to_x64_reg dst) RCX in
     let len =
       (match bpf_to_x64_reg dst with RAX -> nat_of_num (Bit0 (Bit0 One))
         | RBX -> nat_of_num (Bit0 (Bit0 One))
         | RCX -> nat_of_num (Bit1 (Bit0 One))
         | RDX -> nat_of_num (Bit0 (Bit0 One))
         | RSI -> nat_of_num (Bit0 (Bit0 One))
         | RDI -> nat_of_num (Bit0 (Bit0 One))
         | RBP -> nat_of_num (Bit0 (Bit0 One))
         | RSP -> nat_of_num (Bit0 (Bit0 One))
         | R8 -> nat_of_num (Bit0 (Bit0 One))
         | R9 -> nat_of_num (Bit0 (Bit0 One))
         | R10 -> nat_of_num (Bit0 (Bit0 One))
         | R11 -> nat_of_num (Bit0 (Bit0 One))
         | R12 -> nat_of_num (Bit0 (Bit0 One))
         | R13 -> nat_of_num (Bit0 (Bit0 One))
         | R14 -> nat_of_num (Bit0 (Bit0 One))
         | R15 -> nat_of_num (Bit0 (Bit0 One)))
       in
     let l_bin =
       (match bpf_to_x64_reg dst
         with RAX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RBX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RCX ->
           x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr (bpf_to_x64_reg dst, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg src)) @
                 x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
                   x64_encode (Ppopl (bpf_to_x64_reg src))
         | RDX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RSI ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RDI ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RBP ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RSP ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R8 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R9 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R10 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R11 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R12 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R13 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R14 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R15 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshrq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX))
       in
      Some (len, (zero_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
                   l_bin)));;

let rec per_jit_shift_lsh_reg64
  dst src =
    (let _ = equal_ireg (bpf_to_x64_reg dst) RCX in
     let len =
       (match bpf_to_x64_reg dst with RAX -> nat_of_num (Bit0 (Bit0 One))
         | RBX -> nat_of_num (Bit0 (Bit0 One))
         | RCX -> nat_of_num (Bit1 (Bit0 One))
         | RDX -> nat_of_num (Bit0 (Bit0 One))
         | RSI -> nat_of_num (Bit0 (Bit0 One))
         | RDI -> nat_of_num (Bit0 (Bit0 One))
         | RBP -> nat_of_num (Bit0 (Bit0 One))
         | RSP -> nat_of_num (Bit0 (Bit0 One))
         | R8 -> nat_of_num (Bit0 (Bit0 One))
         | R9 -> nat_of_num (Bit0 (Bit0 One))
         | R10 -> nat_of_num (Bit0 (Bit0 One))
         | R11 -> nat_of_num (Bit0 (Bit0 One))
         | R12 -> nat_of_num (Bit0 (Bit0 One))
         | R13 -> nat_of_num (Bit0 (Bit0 One))
         | R14 -> nat_of_num (Bit0 (Bit0 One))
         | R15 -> nat_of_num (Bit0 (Bit0 One)))
       in
     let l_bin =
       (match bpf_to_x64_reg dst
         with RAX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RBX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RCX ->
           x64_encode (Ppushl_r (bpf_to_x64_reg src)) @
             x64_encode (Pxchgq_rr (bpf_to_x64_reg dst, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg src)) @
                 x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
                   x64_encode (Ppopl (bpf_to_x64_reg src))
         | RDX ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RSI ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RDI ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RBP ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | RSP ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R8 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R9 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R10 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R11 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R12 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R13 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R14 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX)
         | R15 ->
           x64_encode (Ppushl_r RCX) @
             x64_encode (Pmovq_rr (RCX, bpf_to_x64_reg src)) @
               x64_encode (Pshlq_r (bpf_to_x64_reg dst)) @
                 x64_encode (Ppopl RCX))
       in
      Some (len, (zero_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
                   l_bin)));;

let rec per_jit_store_reg64
  dst src chk off =
    (let l_bin =
       x64_encode
         (Pmovq_ri
           (R11, signed_cast
                   (len_signed
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   off)) @
         x64_encode (Paddq_rr (R11, bpf_to_x64_reg dst)) @
           x64_encode (Pmovq_rr (R10, bpf_to_x64_reg src)) @
             x64_encode
               (Pmov_rm
                 (R10, Addrmode
                         (Some R11, None,
                           zero_word
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
                   chk))
       in
      Some (nat_of_num (Bit0 (Bit0 One)),
             (zero_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
               l_bin)));;

let rec per_jit_add_reg64_1
  dst src =
    (let ins = Paddq_rr (bpf_to_x64_reg dst, bpf_to_x64_reg src) in
      Some (one_nat,
             (zero_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
               x64_encode ins)));;

let rec per_jit_load_reg64
  dst src chk off =
    (let l_bin =
       x64_encode
         (Pmovq_ri
           (R11, signed_cast
                   (len_signed
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   off)) @
         x64_encode (Paddq_rr (R11, bpf_to_x64_reg src)) @
           x64_encode
             (Pmov_mr
               (Addrmode
                  (Some R11, None,
                    zero_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
                 bpf_to_x64_reg dst, chk))
       in
      Some (nat_of_num (Bit1 One),
             (zero_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
               l_bin)));;

let rec per_jit_mul_reg64
  dst src =
    (let ins_list =
       (match bpf_to_x64_reg dst
         with RAX ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RDX) @
               x64_encode (Pmulq_r R11) @ x64_encode (Ppopl RDX)
         | RBX ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | RCX ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | RDX ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, RDX)) @
                 x64_encode (Pmulq_r R11) @
                   x64_encode (Pmovq_rr (RDX, RAX)) @ x64_encode (Ppopl RAX)
         | RSI ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | RDI ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | RBP ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | RSP ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R8 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R9 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R10 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R11 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R12 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R13 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R14 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX)
         | R15 ->
           x64_encode (Pmovq_rr (R11, bpf_to_x64_reg src)) @
             x64_encode (Ppushl_r RAX) @
               x64_encode (Pmovq_rr (RAX, bpf_to_x64_reg dst)) @
                 x64_encode (Ppushl_r RDX) @
                   x64_encode (Pmulq_r R11) @
                     x64_encode (Ppopl RDX) @
                       x64_encode (Pmovq_rr (bpf_to_x64_reg dst, RAX)) @
                         x64_encode (Ppopl RAX))
       in
     let len =
       (match bpf_to_x64_reg dst with RAX -> nat_of_num (Bit0 (Bit0 One))
         | RBX -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | RCX -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | RDX -> nat_of_num (Bit0 (Bit1 One))
         | RSI -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | RDI -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | RBP -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | RSP -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R8 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R9 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R10 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R11 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R12 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R13 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R14 -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
         | R15 -> nat_of_num (Bit0 (Bit0 (Bit0 One))))
       in
      Some (len, (zero_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
                   ins_list)));;

let rec per_jit_call_reg
  src imm =
    Some (one_nat,
           (zero_word
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
             x64_encode
               (Pcall_i
                 (cast (len_signed
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                   imm))));;

let per_jit_exit :
  (nat *
    (num1 bit0 bit0 bit0 bit0 bit0 bit0 word *
      num1 bit0 bit0 bit0 word list)) option
  = (let ins = Pret in
      Some (one_nat,
             (zero_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
               x64_encode ins)));;

let rec plus_word _A a b = of_int _A (plus_inta (the_int _A a) (the_int _A b));;

let rec the (Some x2) = x2;;

let rec per_jit_jcc
  cond dst src off =
    (let tcond =
       (match cond with Eq -> Some Cond_e | Gt -> Some Cond_a
         | Ge -> Some Cond_ae | Lt -> Some Cond_b | Le -> Some Cond_be
         | SEt -> None | Ne -> Some Cond_ne | SGt -> Some Cond_g
         | SGe -> Some Cond_ge | SLt -> Some Cond_l | SLe -> Some Cond_le)
       in
      (if is_none tcond then None
        else (let ins1 = Pcmpq_rr (bpf_to_x64_reg dst, bpf_to_x64_reg src) in
              let ins2 =
                Pjcc (the tcond,
                       zero_word
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                in
               Some (one_nat,
                      (plus_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         off (one_worda
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))),
                        x64_encode ins1 @ x64_encode ins2)))));;

let rec per_jit_ins
  bins =
    (match bins with BPF_LD_IMM (_, _, _) -> None
      | BPF_LDX (chk, dst, src, a) -> per_jit_load_reg64 dst src chk a
      | BPF_ST (_, _, SOImm _, _) -> None
      | BPF_ST (chk, dst, SOReg src, off) -> per_jit_store_reg64 dst src chk off
      | BPF_ADD_STK _ -> None | BPF_ALU (_, _, _) -> None
      | BPF_NEG32_REG _ -> None | BPF_LE (_, _) -> None | BPF_BE (_, _) -> None
      | BPF_ALU64 (BPF_ADD, _, SOImm _) -> None
      | BPF_ALU64 (BPF_ADD, dst, SOReg a) -> per_jit_add_reg64_1 dst a
      | BPF_ALU64 (BPF_SUB, _, _) -> None
      | BPF_ALU64 (BPF_MUL, _, SOImm _) -> None
      | BPF_ALU64 (BPF_MUL, dst, SOReg a) -> per_jit_mul_reg64 dst a
      | BPF_ALU64 (BPF_DIV, _, _) -> None | BPF_ALU64 (BPF_OR, _, _) -> None
      | BPF_ALU64 (BPF_AND, _, _) -> None
      | BPF_ALU64 (BPF_LSH, _, SOImm _) -> None
      | BPF_ALU64 (BPF_LSH, dst, SOReg a) -> per_jit_shift_lsh_reg64 dst a
      | BPF_ALU64 (BPF_RSH, _, SOImm _) -> None
      | BPF_ALU64 (BPF_RSH, dst, SOReg a) -> per_jit_shift_rsh_reg64 dst a
      | BPF_ALU64 (BPF_MOD, _, _) -> None | BPF_ALU64 (BPF_XOR, _, _) -> None
      | BPF_ALU64 (BPF_MOV, _, _) -> None
      | BPF_ALU64 (BPF_ARSH, _, SOImm _) -> None
      | BPF_ALU64 (BPF_ARSH, dst, SOReg a) -> per_jit_shift_arsh_reg64 dst a
      | BPF_NEG64_REG _ -> None | BPF_HOR64_IMM (_, _) -> None
      | BPF_PQR (_, _, _) -> None | BPF_PQR64 (_, _, _) -> None
      | BPF_PQR2 (_, _, _) -> None | BPF_JA _ -> None
      | BPF_JUMP (_, _, SOImm _, _) -> None
      | BPF_JUMP (cond, dst, SOReg src, off) ->
        per_jit_jcc cond dst src
          (signed_cast
            (len_signed (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            off)
      | BPF_CALL_REG (_, _) -> None
      | BPF_CALL_IMM (a, b) -> per_jit_call_reg a b
      | BPF_EXIT -> per_jit_exit);;

let rec jitper
  = function [] -> Some []
    | h :: xs ->
        (match per_jit_ins h with None -> None
          | Some (n, (off, x)) ->
            (match jitper xs with None -> None
              | Some res -> Some ((n, (off, x)) :: res)));;

let rec equal_nat x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                    | Suc x2, Zero_nat -> false
                    | Suc x2, Suc y2 -> equal_nat x2 y2
                    | Zero_nat, Zero_nat -> true;;

let rec size_list x = gen_length Zero_nat x;;

let rec u16_of_u8_list
  l = (if not (equal_nat (size_list l) (nat_of_num (Bit0 One))) then None
        else Some (or_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                    (push_bit_word
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                      (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                      (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                        (nth l one_nat)))
                    (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                      (nth l Zero_nat))));;

let rec getNextPC
  pc l =
    (let npc = times_nat pc iNSN_SIZE in
     let off_v =
       u16_of_u8_list
         [nth l (plus_nat npc (nat_of_num (Bit0 One)));
           nth l (plus_nat npc (nat_of_num (Bit1 One)))]
       in
      (if equal_nat
            (the_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
              (the off_v))
            Zero_nat
        then plus_nat one_nat pc
        else plus_nat
               (the_nat (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                 (the off_v))
               pc));;

let rec u4_to_bpf_ireg
  dst = (if equal_word (len_bit0 (len_bit0 len_num1)) dst
              (zero_word (len_bit0 (len_bit0 len_num1)))
          then Some BR0
          else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                     (one_worda (len_bit0 (len_bit0 len_num1)))
                 then Some BR1
                 else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                            (of_int (len_bit0 (len_bit0 len_num1))
                              (Pos (Bit0 One)))
                        then Some BR2
                        else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                                   (of_int (len_bit0 (len_bit0 len_num1))
                                     (Pos (Bit1 One)))
                               then Some BR3
                               else (if equal_word
  (len_bit0 (len_bit0 len_num1)) dst
  (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit0 (Bit0 One))))
                                      then Some BR4
                                      else (if equal_word
         (len_bit0 (len_bit0 len_num1)) dst
         (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit1 (Bit0 One))))
     then Some BR5
     else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit0 (Bit1 One))))
            then Some BR6
            else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                       (of_int (len_bit0 (len_bit0 len_num1))
                         (Pos (Bit1 (Bit1 One))))
                   then Some BR7
                   else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                              (of_int (len_bit0 (len_bit0 len_num1))
                                (Pos (Bit0 (Bit0 (Bit0 One)))))
                          then Some BR8
                          else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                                     (of_int (len_bit0 (len_bit0 len_num1))
                                       (Pos (Bit1 (Bit0 (Bit0 One)))))
                                 then Some BR9
                                 else (if equal_word
    (len_bit0 (len_bit0 len_num1)) dst
    (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit0 (Bit1 (Bit0 One)))))
then Some BR10 else None)))))))))));;

let rec rbpf_decoder
  opc dv sv off imm =
    (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit1 One))))
      then (if equal_word (len_bit0 (len_bit0 len_num1)) dv
                 (of_int (len_bit0 (len_bit0 len_num1))
                   (Pos (Bit1 (Bit1 (Bit0 One)))))
             then Some (BPF_ADD_STK imm)
             else (match u4_to_bpf_ireg dv with None -> None
                    | Some dst -> Some (BPF_ALU64 (BPF_ADD, dst, SOImm imm))))
      else (match u4_to_bpf_ireg dv with None -> None
             | Some dst ->
               (match u4_to_bpf_ireg sv with None -> None
                 | Some src ->
                   (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))))
                     then Some (BPF_LDX (M8, dst, src, off))
                     else (if equal_word
                                (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit1
 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
                            then Some (BPF_LDX (M16, dst, src, off))
                            else (if equal_word
                                       (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                       opc (of_int
     (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))
                                   then Some (BPF_LDX (M32, dst, src, off))
                                   else (if equal_word
      (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
  then Some (BPF_LDX (M64, dst, src, off))
  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))))
         then Some (BPF_ST (M8, dst, SOImm imm, off))
         else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
                then Some (BPF_ST (M16, dst, SOImm imm, off))
                else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           opc (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit0
(Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))
                       then Some (BPF_ST (M32, dst, SOImm imm, off))
                       else (if equal_word
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                  (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
                              then Some (BPF_ST (M64, dst, SOImm imm, off))
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))))
                                     then Some (BPF_ST
         (M8, dst, SOReg src, off))
                                     else (if equal_word
        (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
    then Some (BPF_ST (M16, dst, SOReg src, off))
    else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))
           then Some (BPF_ST (M32, dst, SOReg src, off))
           else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
                  then Some (BPF_ST (M64, dst, SOReg src, off))
                  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             opc (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0 (Bit0 One))))
                         then Some (BPF_ALU (BPF_ADD, dst, SOImm imm))
                         else (if equal_word
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    opc (of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 (Bit0 (Bit1 One)))))
                                then Some (BPF_ALU (BPF_ADD, dst, SOReg src))
                                else (if equal_word
   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit0 (Bit0 (Bit1 (Bit0 One))))))
                                       then Some (BPF_ALU
           (BPF_SUB, dst, SOImm imm))
                                       else (if equal_word
          (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit0 (Bit0 (Bit1 (Bit1 One))))))
      then Some (BPF_ALU (BPF_SUB, dst, SOReg src))
      else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
             then Some (BPF_ALU (BPF_MUL, dst, SOImm imm))
             else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
                    then Some (BPF_ALU (BPF_MUL, dst, SOReg src))
                    else (if equal_word
                               (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
                           then Some (BPF_ALU (BPF_DIV, dst, SOImm imm))
                           else (if equal_word
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      opc (of_int
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
                                  then Some (BPF_ALU (BPF_DIV, dst, SOReg src))
                                  else (if equal_word
     (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
 then Some (BPF_ALU (BPF_OR, dst, SOImm imm))
 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
            (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
        then Some (BPF_ALU (BPF_OR, dst, SOReg src))
        else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
               then Some (BPF_ALU (BPF_AND, dst, SOImm imm))
               else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
                      then Some (BPF_ALU (BPF_AND, dst, SOReg src))
                      else (if equal_word
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                 (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
                             then Some (BPF_ALU (BPF_LSH, dst, SOImm imm))
                             else (if equal_word
(len_bit0 (len_bit0 (len_bit0 len_num1))) opc
(of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
                                    then Some (BPF_ALU
        (BPF_LSH, dst, SOReg src))
                                    else (if equal_word
       (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
   then Some (BPF_ALU (BPF_RSH, dst, SOImm imm))
   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
              (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
          then Some (BPF_ALU (BPF_RSH, dst, SOReg src))
          else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (Pos (Bit0 (Bit0 (Bit1
  (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                 then Some (BPF_NEG32_REG dst)
                 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            opc (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0
 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
                        then Some (BPF_ALU (BPF_MOD, dst, SOImm imm))
                        else (if equal_word
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                   (of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))))
                               then Some (BPF_ALU (BPF_MOD, dst, SOReg src))
                               else (if equal_word
  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))))
                                      then Some (BPF_ALU
          (BPF_XOR, dst, SOImm imm))
                                      else (if equal_word
         (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))))
     then Some (BPF_ALU (BPF_XOR, dst, SOReg src))
     else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
            then Some (BPF_ALU (BPF_MOV, dst, SOImm imm))
            else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                         (Pos (Bit0 (Bit0 (Bit1
    (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                   then Some (BPF_ALU (BPF_MOV, dst, SOReg src))
                   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                              opc (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
                          then Some (BPF_ALU (BPF_ARSH, dst, SOImm imm))
                          else (if equal_word
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     opc (of_int
   (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
                                 then Some (BPF_ALU (BPF_ARSH, dst, SOReg src))
                                 else (if equal_word
    (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))))
then Some (BPF_LE (dst, imm))
else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
           (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))))
       then Some (BPF_BE (dst, imm))
       else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                    (Pos (Bit1 (Bit1 (Bit1 One)))))
              then Some (BPF_ALU64 (BPF_ADD, dst, SOReg src))
              else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (Pos (Bit1 (Bit1 (Bit1 (Bit0 One))))))
                     then Some (BPF_ALU64 (BPF_SUB, dst, SOImm imm))
                     else (if equal_word
                                (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit1 (Bit1 (Bit1 (Bit1 One))))))
                            then Some (BPF_ALU64 (BPF_SUB, dst, SOReg src))
                            else (if equal_word
                                       (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                       opc (of_int
     (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
                                   then Some (BPF_ALU64
       (BPF_MUL, dst, SOImm imm))
                                   else (if equal_word
      (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
  then Some (BPF_ALU64 (BPF_MUL, dst, SOReg src))
  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
         then Some (BPF_ALU64 (BPF_DIV, dst, SOImm imm))
         else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
                then Some (BPF_ALU64 (BPF_DIV, dst, SOReg src))
                else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           opc (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit1
(Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
                       then Some (BPF_ALU64 (BPF_OR, dst, SOImm imm))
                       else (if equal_word
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                  (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit1
   (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
                              then Some (BPF_ALU64 (BPF_OR, dst, SOReg src))
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
                                     then Some (BPF_ALU64
         (BPF_AND, dst, SOImm imm))
                                     else (if equal_word
        (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
    then Some (BPF_ALU64 (BPF_AND, dst, SOReg src))
    else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
           then Some (BPF_ALU64 (BPF_LSH, dst, SOImm imm))
           else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
                  then Some (BPF_ALU64 (BPF_LSH, dst, SOReg src))
                  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             opc (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
                         then Some (BPF_ALU64 (BPF_RSH, dst, SOImm imm))
                         else (if equal_word
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    opc (of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
                                then Some (BPF_ALU64 (BPF_RSH, dst, SOReg src))
                                else (if equal_word
   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                                       then Some (BPF_NEG64_REG dst)
                                       else (if equal_word
          (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
      then Some (BPF_ALU64 (BPF_MOD, dst, SOImm imm))
      else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))))
             then Some (BPF_ALU64 (BPF_MOD, dst, SOReg src))
             else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (Pos (Bit1 (Bit1 (Bit1
     (Bit0 (Bit0 (Bit1 (Bit0 One)))))))))
                    then Some (BPF_ALU64 (BPF_XOR, dst, SOImm imm))
                    else (if equal_word
                               (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit1
(Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))))
                           then Some (BPF_ALU64 (BPF_XOR, dst, SOReg src))
                           else (if equal_word
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      opc (of_int
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
                                  then Some (BPF_ALU64
      (BPF_MOV, dst, SOImm imm))
                                  else (if equal_word
     (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
 then Some (BPF_ALU64 (BPF_MOV, dst, SOReg src))
 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
            (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
        then Some (BPF_ALU64 (BPF_ARSH, dst, SOImm imm))
        else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
               then Some (BPF_ALU64 (BPF_ARSH, dst, SOReg src))
               else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit1 (Bit1
 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))))
                      then Some (BPF_HOR64_IMM (dst, imm))
                      else (if equal_word
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                 (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                             then Some (BPF_PQR (BPF_LMUL, dst, SOImm imm))
                             else (if equal_word
(len_bit0 (len_bit0 (len_bit0 len_num1))) opc
(of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))))
                                    then Some (BPF_PQR
        (BPF_LMUL, dst, SOReg src))
                                    else (if equal_word
       (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
   then Some (BPF_PQR64 (BPF_LMUL, dst, SOImm imm))
   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
              (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))))
          then Some (BPF_PQR64 (BPF_LMUL, dst, SOReg src))
          else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
                 then Some (BPF_PQR2 (BPF_UHMUL, dst, SOImm imm))
                 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            opc (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
                        then Some (BPF_PQR2 (BPF_UHMUL, dst, SOReg src))
                        else (if equal_word
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                   (of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
                               then Some (BPF_PQR2 (BPF_SHMUL, dst, SOImm imm))
                               else (if equal_word
  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                                      then Some (BPF_PQR2
          (BPF_SHMUL, dst, SOReg src))
                                      else (if equal_word
         (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
     then Some (BPF_PQR (BPF_UDIV, dst, SOImm imm))
     else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
            then Some (BPF_PQR (BPF_UDIV, dst, SOReg src))
            else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                         (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
                   then Some (BPF_PQR64 (BPF_UDIV, dst, SOImm imm))
                   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                              opc (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
                          then Some (BPF_PQR64 (BPF_UDIV, dst, SOReg src))
                          else (if equal_word
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     opc (of_int
   (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
                                 then Some (BPF_PQR (BPF_UREM, dst, SOImm imm))
                                 else (if equal_word
    (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
then Some (BPF_PQR (BPF_UREM, dst, SOReg src))
else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
           (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
       then Some (BPF_PQR64 (BPF_UREM, dst, SOImm imm))
       else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                    (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
              then Some (BPF_PQR64 (BPF_UREM, dst, SOReg src))
              else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (Pos (Bit0 (Bit1
(Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
                     then Some (BPF_PQR (BPF_SDIV, dst, SOImm imm))
                     else (if equal_word
                                (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0
 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
                            then Some (BPF_PQR (BPF_SDIV, dst, SOReg src))
                            else (if equal_word
                                       (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                       opc (of_int
     (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))))
                                   then Some (BPF_PQR64
       (BPF_SDIV, dst, SOImm imm))
                                   else (if equal_word
      (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))))
  then Some (BPF_PQR64 (BPF_SDIV, dst, SOReg src))
  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))))
         then Some (BPF_PQR (BPF_SREM, dst, SOImm imm))
         else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit0 (Bit1 (Bit1
 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))))
                then Some (BPF_PQR (BPF_SREM, dst, SOReg src))
                else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           opc (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit0
(Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))))
                       then Some (BPF_PQR64 (BPF_SREM, dst, SOImm imm))
                       else (if equal_word
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                  (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))))
                              then Some (BPF_PQR64 (BPF_SREM, dst, SOReg src))
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 (Bit0 One))))
                                     then Some (BPF_JA off)
                                     else (if equal_word
        (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit0 (Bit1 (Bit0 One))))))
    then Some (BPF_JUMP (Eq, dst, SOImm imm, off))
    else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit0 (Bit1 (Bit1 One))))))
           then Some (BPF_JUMP (Eq, dst, SOReg src, off))
           else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
                  then Some (BPF_JUMP (Gt, dst, SOImm imm, off))
                  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             opc (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
                         then Some (BPF_JUMP (Gt, dst, SOReg src, off))
                         else (if equal_word
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    opc (of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
                                then Some (BPF_JUMP (Ge, dst, SOImm imm, off))
                                else (if equal_word
   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
                                       then Some (BPF_JUMP
           (Ge, dst, SOReg src, off))
                                       else (if equal_word
          (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))))
      then Some (BPF_JUMP (Lt, dst, SOImm imm, off))
      else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))))
             then Some (BPF_JUMP (Lt, dst, SOReg src, off))
             else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (Pos (Bit1 (Bit0 (Bit1
     (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
                    then Some (BPF_JUMP (Le, dst, SOImm imm, off))
                    else (if equal_word
                               (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit1
(Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                           then Some (BPF_JUMP (Le, dst, SOReg src, off))
                           else (if equal_word
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      opc (of_int
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
                                  then Some (BPF_JUMP
      (SEt, dst, SOImm imm, off))
                                  else (if equal_word
     (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
 then Some (BPF_JUMP (SEt, dst, SOReg src, off))
 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
            (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
        then Some (BPF_JUMP (Ne, dst, SOImm imm, off))
        else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
               then Some (BPF_JUMP (Ne, dst, SOReg src, off))
               else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
                      then Some (BPF_JUMP (SGt, dst, SOImm imm, off))
                      else (if equal_word
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                 (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
                             then Some (BPF_JUMP (SGt, dst, SOReg src, off))
                             else (if equal_word
(len_bit0 (len_bit0 (len_bit0 len_num1))) opc
(of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
                                    then Some (BPF_JUMP
        (SGe, dst, SOImm imm, off))
                                    else (if equal_word
       (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
   then Some (BPF_JUMP (SGe, dst, SOReg src, off))
   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
              (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
          then Some (BPF_JUMP (SLt, dst, SOImm imm, off))
          else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (Pos (Bit1 (Bit0 (Bit1
  (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
                 then Some (BPF_JUMP (SLt, dst, SOReg src, off))
                 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            opc (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit1
 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))))
                        then Some (BPF_JUMP (SLe, dst, SOImm imm, off))
                        else (if equal_word
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                   (of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit1
    (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))))
                               then Some (BPF_JUMP (SLe, dst, SOReg src, off))
                               else (if equal_word
  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))))
                                      then Some (BPF_CALL_REG (src, imm))
                                      else (if equal_word
         (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
     then Some (BPF_CALL_IMM (src, imm))
     else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
            then Some BPF_EXIT
            else None)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));;

let rec less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
                   | n, Zero_nat -> false
and less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                  | Zero_nat, n -> true;;

let rec unsigned_bitfield_extract_u8
  pos width n =
    and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (minus_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (power (power_word (len_bit0 (len_bit0 (len_bit0 len_num1))))
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 One)))
          width)
        (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      (drop_bit_word (len_bit0 (len_bit0 (len_bit0 len_num1))) pos n);;

let rec u32_of_u8_list
  l = (if not (equal_nat (size_list l) (nat_of_num (Bit0 (Bit0 One)))) then None
        else Some (or_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    (push_bit_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One)))))
                      (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (nth l (nat_of_num (Bit1 One)))))
                    (or_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (push_bit_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
                        (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (nth l (nat_of_num (Bit0 One)))))
                      (or_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (push_bit_word
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                          (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                            (nth l one_nat)))
                        (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (nth l Zero_nat))))));;

let rec bpf_find_instr
  pc l =
    (let npc = times_nat pc iNSN_SIZE in
     let op = nth l npc in
     let reg = nth l (plus_nat npc one_nat) in
     let dst =
       unsigned_bitfield_extract_u8 Zero_nat (nat_of_num (Bit0 (Bit0 One))) reg
       in
     let src =
       unsigned_bitfield_extract_u8 (nat_of_num (Bit0 (Bit0 One)))
         (nat_of_num (Bit0 (Bit0 One))) reg
       in
      (if less_nat (size_list l) (plus_nat npc (nat_of_num (Bit1 (Bit1 One))))
        then None
        else (match
               u16_of_u8_list
                 [nth l (plus_nat npc (nat_of_num (Bit0 One)));
                   nth l (plus_nat npc (nat_of_num (Bit1 One)))]
               with None -> None
               | Some off_v ->
                 (match
                   u32_of_u8_list
                     [nth l (plus_nat npc (nat_of_num (Bit0 (Bit0 One))));
                       nth l (plus_nat npc (nat_of_num (Bit1 (Bit0 One))));
                       nth l (plus_nat npc (nat_of_num (Bit0 (Bit1 One))));
                       nth l (plus_nat npc (nat_of_num (Bit1 (Bit1 One))))]
                   with None -> None
                   | Some i1 ->
                     (let off =
                        signed_cast
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                          (len_signed
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          off_v
                        in
                      let imm =
                        signed_cast
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (len_signed
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          i1
                        in
                       (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             op (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0 (Bit0 (Bit0 (Bit1 One))))))
                         then (if less_nat (size_list l)
                                    (plus_nat npc
                                      (nat_of_num (Bit1 (Bit1 (Bit1 One)))))
                                then None
                                else (match
                                       u32_of_u8_list
 [nth l (plus_nat npc (nat_of_num (Bit0 (Bit0 (Bit1 One)))));
   nth l (plus_nat npc (nat_of_num (Bit1 (Bit0 (Bit1 One)))));
   nth l (plus_nat npc (nat_of_num (Bit0 (Bit1 (Bit1 One)))));
   nth l (plus_nat npc (nat_of_num (Bit1 (Bit1 (Bit1 One)))))]
                                       with None -> None
                                       | Some i2 ->
 (let imm2 =
    signed_cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      (len_signed
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
      i2
    in
   (match
     u4_to_bpf_ireg
       (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (len_bit0 (len_bit0 len_num1)) dst)
     with None -> None | Some dst_r -> Some (BPF_LD_IMM (dst_r, imm, imm2))))))
                         else rbpf_decoder op
                                (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (len_bit0 (len_bit0 len_num1)) dst)
                                (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (len_bit0 (len_bit0 len_num1)) src)
                                off imm))))));;

let rec bpf_find_prog_aux
  x0 uu uv = match x0, uu, uv with Zero_nat, uu, uv -> [None]
    | Suc fuel, pc, l ->
        (if less_eq_nat (times_nat (plus_nat pc one_nat) iNSN_SIZE)
              (size_list l)
          then (match bpf_find_instr pc l with None -> [None]
                 | Some v ->
                   (let pca = getNextPC pc l in
                     [Some v] @ bpf_find_prog_aux fuel pca l))
          else [None]);;

let rec bpf_find_prog
  fuel pc l =
    (let la = bpf_find_prog_aux fuel pc l in
      (if equal_nat (size_list la) one_nat then None
        else Some (map the (butlast la))));;

let rec divmod_nat
  m n = (if equal_nat n Zero_nat || less_nat m n then (Zero_nat, m)
          else (let (q, a) = divmod_nat (minus_nat m n) n in (Suc q, a)));;

let rec int_to_u8_list
  lp = map (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))) lp;;

let rec divide_nat m n = fst (divmod_nat m n);;

let rec list_embedd_in_list
  x0 l = match x0, l with [], l -> Some l
    | x :: xs, [] -> None
    | x :: xs, y :: ys ->
        (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) x y
          then list_embedd_in_list xs ys
          else list_embedd_in_list (x :: xs) ys);;

let rec dlist_embedd_in_list
  x0 uu = match x0, uu with [], uu -> true
    | x :: xs, l ->
        (match list_embedd_in_list x l with None -> false
          | Some a -> dlist_embedd_in_list xs a);;    

let i64_MIN
  = (Neg (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));;

let rec num_to_int (n: num) : int64 =
  match n with
  | One -> 1L
  | Bit0 m -> Int64.mul 2L (num_to_int m)
  | Bit1 m -> Int64.add (Int64.mul 2L (num_to_int m)) 1L     

let myint_to_int (mi: myint) : int64 =
  match mi with
  | Zero_int -> 0L
  | Pos n -> num_to_int n
  | Neg n -> Int64.neg (num_to_int n)

let rec num_of_int (n: int64) =
  if n = 1L then One
  else if Int64.rem n 2L = 0L then Bit0 (num_of_int (Int64.div n 2L))
  else Bit1 (num_of_int (Int64.div n 2L))


let int_of_standard_int (n: int64) =
  if n = 0L then Zero_int
  else if n > 0L then  Pos (num_of_int (n))
  else if n = 0x8000000000000000L then i64_MIN
  else Neg (num_of_int (Int64.sub 0L n))


let int_list_of_standard_int_list lst =
  List.map int_of_standard_int lst


let rec jit_evaluation
  ebpf_prog compiled_progam =
    (let ebpf_binary = int_to_u8_list ebpf_prog in
     let jit_prog = int_to_u8_list compiled_progam in
      (match
        bpf_find_prog
          (divide_nat (size_list ebpf_binary)
            (nat_of_num (Bit0 (Bit0 (Bit0 One)))))
          Zero_nat ebpf_binary
        with None -> false
        | Some l_ebpf_asm ->
          (match jitper l_ebpf_asm with None -> false
            | Some l_bin3 ->
              (let l_bin = map (fun x -> snd (snd x)) l_bin3 in
                dlist_embedd_in_list l_bin jit_prog))));;

end;; (*struct Jit_eval*)
