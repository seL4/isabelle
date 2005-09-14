(* $Id$ *)

    (* Caution: This file should not be modified. *)
    (* It is autmatically generated from HOL/ex/Reflected_Presburger.thy *)
fun nat i = if i < 0 then 0 else i;
structure Generated =
struct

datatype intterm = Cst of int | Var of int | Neg of intterm
  | Add of intterm * intterm | Sub of intterm * intterm
  | Mult of intterm * intterm;

datatype QF = Lt of intterm * intterm | Gt of intterm * intterm
  | Le of intterm * intterm | Ge of intterm * intterm | Eq of intterm * intterm
  | Divides of intterm * intterm | T | F | NOT of QF | And of QF * QF
  | Or of QF * QF | Imp of QF * QF | Equ of QF * QF | QAll of QF | QEx of QF;

datatype 'a option = None | Some of 'a;

fun lift_un c None = None
  | lift_un c (Some p) = Some (c p);

fun lift_bin (c, (Some a, Some b)) = Some (c a b)
  | lift_bin (c, (None, y)) = None
  | lift_bin (c, (Some y, None)) = None;

fun lift_qe qe None = None
  | lift_qe qe (Some p) = qe p;

fun qelim (qe, QAll p) = lift_un NOT (lift_qe qe (lift_un NOT (qelim (qe, p))))
  | qelim (qe, QEx p) = lift_qe qe (qelim (qe, p))
  | qelim (qe, And (p, q)) =
    lift_bin ((fn x => fn xa => And (x, xa)), (qelim (qe, p), qelim (qe, q)))
  | qelim (qe, Or (p, q)) =
    lift_bin ((fn x => fn xa => Or (x, xa)), (qelim (qe, p), qelim (qe, q)))
  | qelim (qe, Imp (p, q)) =
    lift_bin ((fn x => fn xa => Imp (x, xa)), (qelim (qe, p), qelim (qe, q)))
  | qelim (qe, Equ (p, q)) =
    lift_bin ((fn x => fn xa => Equ (x, xa)), (qelim (qe, p), qelim (qe, q)))
  | qelim (qe, NOT p) = lift_un NOT (qelim (qe, p))
  | qelim (qe, Lt (w, x)) = Some (Lt (w, x))
  | qelim (qe, Gt (y, z)) = Some (Gt (y, z))
  | qelim (qe, Le (aa, ab)) = Some (Le (aa, ab))
  | qelim (qe, Ge (ac, ad)) = Some (Ge (ac, ad))
  | qelim (qe, Eq (ae, af)) = Some (Eq (ae, af))
  | qelim (qe, Divides (ag, ah)) = Some (Divides (ag, ah))
  | qelim (qe, T) = Some T
  | qelim (qe, F) = Some F;

fun lin_mul (c, Cst i) = Cst (c * i)
  | lin_mul (c, Add (Mult (Cst c', Var n), r)) =
    (if (c = 0) then Cst 0
      else Add (Mult (Cst (c * c'), Var n), lin_mul (c, r)));

fun op_60_def0 m n = ((m) < (n));

fun op_60_61_def0 m n = not (op_60_def0 n m);

fun lin_add (Add (Mult (Cst c1, Var n1), r1), Add (Mult (Cst c2, Var n2), r2)) =
    (if (n1 = n2)
      then let val c = Cst (c1 + c2)
           in (if ((c1 + c2) = 0) then lin_add (r1, r2)
                else Add (Mult (c, Var n1), lin_add (r1, r2)))
           end
      else (if op_60_61_def0 n1 n2
             then Add (Mult (Cst c1, Var n1),
                        lin_add (r1, Add (Mult (Cst c2, Var n2), r2)))
             else Add (Mult (Cst c2, Var n2),
                        lin_add (Add (Mult (Cst c1, Var n1), r1), r2))))
  | lin_add (Add (Mult (Cst c1, Var n1), r1), Cst b) =
    Add (Mult (Cst c1, Var n1), lin_add (r1, Cst b))
  | lin_add (Cst x, Add (Mult (Cst c2, Var n2), r2)) =
    Add (Mult (Cst c2, Var n2), lin_add (Cst x, r2))
  | lin_add (Cst b1, Cst b2) = Cst (b1 + b2);

fun lin_neg i = lin_mul (~1, i);

fun linearize (Cst b) = Some (Cst b)
  | linearize (Var n) = Some (Add (Mult (Cst 1, Var n), Cst 0))
  | linearize (Neg i) = lift_un lin_neg (linearize i)
  | linearize (Add (i, j)) =
    lift_bin ((fn x => fn y => lin_add (x, y)), (linearize i, linearize j))
  | linearize (Sub (i, j)) =
    lift_bin
      ((fn x => fn y => lin_add (x, lin_neg y)), (linearize i, linearize j))
  | linearize (Mult (i, j)) =
    (case linearize i of None => None
      | Some x =>
          (case x of
            Cst xa =>
              (case linearize j of None => None
                | Some x => Some (lin_mul (xa, x)))
            | Var xa =>
                (case linearize j of None => None
                  | Some xa =>
                      (case xa of Cst xa => Some (lin_mul (xa, x))
                        | Var xa => None | Neg xa => None | Add (xa, xb) => None
                        | Sub (xa, xb) => None | Mult (xa, xb) => None))
            | Neg xa =>
                (case linearize j of None => None
                  | Some xa =>
                      (case xa of Cst xa => Some (lin_mul (xa, x))
                        | Var xa => None | Neg xa => None | Add (xa, xb) => None
                        | Sub (xa, xb) => None | Mult (xa, xb) => None))
            | Add (xa, xb) =>
                (case linearize j of None => None
                  | Some xa =>
                      (case xa of Cst xa => Some (lin_mul (xa, x))
                        | Var xa => None | Neg xa => None | Add (xa, xb) => None
                        | Sub (xa, xb) => None | Mult (xa, xb) => None))
            | Sub (xa, xb) =>
                (case linearize j of None => None
                  | Some xa =>
                      (case xa of Cst xa => Some (lin_mul (xa, x))
                        | Var xa => None | Neg xa => None | Add (xa, xb) => None
                        | Sub (xa, xb) => None | Mult (xa, xb) => None))
            | Mult (xa, xb) =>
                (case linearize j of None => None
                  | Some xa =>
                      (case xa of Cst xa => Some (lin_mul (xa, x))
                        | Var xa => None | Neg xa => None | Add (xa, xb) => None
                        | Sub (xa, xb) => None | Mult (xa, xb) => None))));

fun linform (Le (it1, it2)) =
    lift_bin
      ((fn x => fn y => Le (lin_add (x, lin_neg y), Cst 0)),
        (linearize it1, linearize it2))
  | linform (Eq (it1, it2)) =
    lift_bin
      ((fn x => fn y => Eq (lin_add (x, lin_neg y), Cst 0)),
        (linearize it1, linearize it2))
  | linform (Divides (d, t)) =
    (case linearize d of None => None
      | Some x =>
          (case x of
            Cst xa =>
              (if (xa = 0) then None
                else (case linearize t of None => None
                       | Some xa => Some (Divides (x, xa))))
            | Var xa => None | Neg xa => None | Add (xa, xb) => None
            | Sub (xa, xb) => None | Mult (xa, xb) => None))
  | linform T = Some T
  | linform F = Some F
  | linform (NOT p) = lift_un NOT (linform p)
  | linform (And (p, q)) =
    lift_bin ((fn f => fn g => And (f, g)), (linform p, linform q))
  | linform (Or (p, q)) =
    lift_bin ((fn f => fn g => Or (f, g)), (linform p, linform q));

fun nnf (Lt (it1, it2)) = Le (Sub (it1, it2), Cst (~ 1))
  | nnf (Gt (it1, it2)) = Le (Sub (it2, it1), Cst (~ 1))
  | nnf (Le (it1, it2)) = Le (it1, it2)
  | nnf (Ge (it1, it2)) = Le (it2, it1)
  | nnf (Eq (it1, it2)) = Eq (it2, it1)
  | nnf (Divides (d, t)) = Divides (d, t)
  | nnf T = T
  | nnf F = F
  | nnf (And (p, q)) = And (nnf p, nnf q)
  | nnf (Or (p, q)) = Or (nnf p, nnf q)
  | nnf (Imp (p, q)) = Or (nnf (NOT p), nnf q)
  | nnf (Equ (p, q)) = Or (And (nnf p, nnf q), And (nnf (NOT p), nnf (NOT q)))
  | nnf (NOT (Lt (it1, it2))) = Le (it2, it1)
  | nnf (NOT (Gt (it1, it2))) = Le (it1, it2)
  | nnf (NOT (Le (it1, it2))) = Le (Sub (it2, it1), Cst (~ 1))
  | nnf (NOT (Ge (it1, it2))) = Le (Sub (it1, it2), Cst (~ 1))
  | nnf (NOT (Eq (it1, it2))) = NOT (Eq (it1, it2))
  | nnf (NOT (Divides (d, t))) = NOT (Divides (d, t))
  | nnf (NOT T) = F
  | nnf (NOT F) = T
  | nnf (NOT (NOT p)) = nnf p
  | nnf (NOT (And (p, q))) = Or (nnf (NOT p), nnf (NOT q))
  | nnf (NOT (Or (p, q))) = And (nnf (NOT p), nnf (NOT q))
  | nnf (NOT (Imp (p, q))) = And (nnf p, nnf (NOT q))
  | nnf (NOT (Equ (p, q))) =
    Or (And (nnf p, nnf (NOT q)), And (nnf (NOT p), nnf q));

fun op_45_def2 z w = (z + ~ w);

fun op_45_def0 m n = nat (op_45_def2 (m) (n));

val id_1_def0 : int = (0 + 1);

fun decrvarsI (Cst i) = Cst i
  | decrvarsI (Var n) = Var (op_45_def0 n id_1_def0)
  | decrvarsI (Neg a) = Neg (decrvarsI a)
  | decrvarsI (Add (a, b)) = Add (decrvarsI a, decrvarsI b)
  | decrvarsI (Sub (a, b)) = Sub (decrvarsI a, decrvarsI b)
  | decrvarsI (Mult (a, b)) = Mult (decrvarsI a, decrvarsI b);

fun decrvars (Lt (a, b)) = Lt (decrvarsI a, decrvarsI b)
  | decrvars (Gt (a, b)) = Gt (decrvarsI a, decrvarsI b)
  | decrvars (Le (a, b)) = Le (decrvarsI a, decrvarsI b)
  | decrvars (Ge (a, b)) = Ge (decrvarsI a, decrvarsI b)
  | decrvars (Eq (a, b)) = Eq (decrvarsI a, decrvarsI b)
  | decrvars (Divides (a, b)) = Divides (decrvarsI a, decrvarsI b)
  | decrvars T = T
  | decrvars F = F
  | decrvars (NOT p) = NOT (decrvars p)
  | decrvars (And (p, q)) = And (decrvars p, decrvars q)
  | decrvars (Or (p, q)) = Or (decrvars p, decrvars q)
  | decrvars (Imp (p, q)) = Imp (decrvars p, decrvars q)
  | decrvars (Equ (p, q)) = Equ (decrvars p, decrvars q);

fun op_64 [] ys = ys
  | op_64 (x :: xs) ys = (x :: op_64 xs ys);

fun map f [] = []
  | map f (x :: xs) = (f x :: map f xs);

fun iupto (i, j) = (if (j < i) then [] else (i :: iupto ((i + 1), j)));

fun all_sums (j, []) = []
  | all_sums (j, (i :: is)) =
    op_64 (map (fn x => lin_add (i, Cst x)) (iupto (1, j))) (all_sums (j, is));

fun split x = (fn p => x (fst p) (snd p));

fun negateSnd x = split (fn q => fn r => (q, ~ r)) x;

fun adjust b =
  (fn (q, r) =>
    (if (0 <= op_45_def2 r b) then (((2 * q) + 1), op_45_def2 r b)
      else ((2 * q), r)));

fun negDivAlg (a, b) =
    (if ((0 <= (a + b)) orelse (b <= 0)) then (~1, (a + b))
      else adjust b (negDivAlg (a, (2 * b))));

fun posDivAlg (a, b) =
    (if ((a < b) orelse (b <= 0)) then (0, a)
      else adjust b (posDivAlg (a, (2 * b))));

fun divAlg x =
  split (fn a => fn b =>
          (if (0 <= a)
            then (if (0 <= b) then posDivAlg (a, b)
                   else (if (a = 0) then (0, 0)
                          else negateSnd (negDivAlg (~ a, ~ b))))
            else (if (0 < b) then negDivAlg (a, b)
                   else negateSnd (posDivAlg (~ a, ~ b)))))
    x;

fun op_mod_def1 a b = snd (divAlg (a, b));

fun op_dvd m n = (op_mod_def1 n m = 0);

fun psimpl (Le (l, r)) =
    (case lift_bin
            ((fn x => fn y => lin_add (x, lin_neg y)),
              (linearize l, linearize r)) of
      None => Le (l, r)
      | Some x =>
          (case x of Cst xa => (if (xa <= 0) then T else F)
            | Var xa => Le (x, Cst 0) | Neg xa => Le (x, Cst 0)
            | Add (xa, xb) => Le (x, Cst 0) | Sub (xa, xb) => Le (x, Cst 0)
            | Mult (xa, xb) => Le (x, Cst 0)))
  | psimpl (Eq (l, r)) =
    (case lift_bin
            ((fn x => fn y => lin_add (x, lin_neg y)),
              (linearize l, linearize r)) of
      None => Eq (l, r)
      | Some x =>
          (case x of Cst xa => (if (xa = 0) then T else F)
            | Var xa => Eq (x, Cst 0) | Neg xa => Eq (x, Cst 0)
            | Add (xa, xb) => Eq (x, Cst 0) | Sub (xa, xb) => Eq (x, Cst 0)
            | Mult (xa, xb) => Eq (x, Cst 0)))
  | psimpl (Divides (Cst d, t)) =
    (case linearize t of None => Divides (Cst d, t)
      | Some x =>
          (case x of Cst xa => (if op_dvd d xa then T else F)
            | Var xa => Divides (Cst d, x) | Neg xa => Divides (Cst d, x)
            | Add (xa, xb) => Divides (Cst d, x)
            | Sub (xa, xb) => Divides (Cst d, x)
            | Mult (xa, xb) => Divides (Cst d, x)))
  | psimpl (Equ (p, q)) =
    let val p' = psimpl p; val q' = psimpl q
    in (case p' of
         Lt (x, xa) =>
           (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
             | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
             | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
             | T => p' | F => NOT p' | NOT x => Equ (p', q')
             | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
             | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
             | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Gt (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Le (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Ge (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Eq (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Divides (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | T => q'
         | F => (case q' of Lt (x, xa) => NOT q' | Gt (x, xa) => NOT q'
                  | Le (x, xa) => NOT q' | Ge (x, xa) => NOT q'
                  | Eq (x, xa) => NOT q' | Divides (x, xa) => NOT q' | T => F
                  | F => T | NOT x => x | And (x, xa) => NOT q'
                  | Or (x, xa) => NOT q' | Imp (x, xa) => NOT q'
                  | Equ (x, xa) => NOT q' | QAll x => NOT q' | QEx x => NOT q')
         | NOT x =>
             (case q' of Lt (xa, xb) => Equ (p', q')
               | Gt (xa, xb) => Equ (p', q') | Le (xa, xb) => Equ (p', q')
               | Ge (xa, xb) => Equ (p', q') | Eq (xa, xb) => Equ (p', q')
               | Divides (xa, xb) => Equ (p', q') | T => p' | F => x
               | NOT xa => Equ (x, xa) | And (xa, xb) => Equ (p', q')
               | Or (xa, xb) => Equ (p', q') | Imp (xa, xb) => Equ (p', q')
               | Equ (xa, xb) => Equ (p', q') | QAll xa => Equ (p', q')
               | QEx xa => Equ (p', q'))
         | And (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Or (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Imp (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | Equ (x, xa) =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | QAll x =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q'))
         | QEx x =>
             (case q' of Lt (x, xa) => Equ (p', q') | Gt (x, xa) => Equ (p', q')
               | Le (x, xa) => Equ (p', q') | Ge (x, xa) => Equ (p', q')
               | Eq (x, xa) => Equ (p', q') | Divides (x, xa) => Equ (p', q')
               | T => p' | F => NOT p' | NOT x => Equ (p', q')
               | And (x, xa) => Equ (p', q') | Or (x, xa) => Equ (p', q')
               | Imp (x, xa) => Equ (p', q') | Equ (x, xa) => Equ (p', q')
               | QAll x => Equ (p', q') | QEx x => Equ (p', q')))
    end
  | psimpl (NOT p) =
    let val p' = psimpl p
    in (case p' of Lt (x, xa) => NOT p' | Gt (x, xa) => NOT p'
         | Le (x, xa) => NOT p' | Ge (x, xa) => NOT p' | Eq (x, xa) => NOT p'
         | Divides (x, xa) => NOT p' | T => F | F => T | NOT x => x
         | And (x, xa) => NOT p' | Or (x, xa) => NOT p' | Imp (x, xa) => NOT p'
         | Equ (x, xa) => NOT p' | QAll x => NOT p' | QEx x => NOT p')
    end
  | psimpl (Lt (u, v)) = Lt (u, v)
  | psimpl (Gt (w, x)) = Gt (w, x)
  | psimpl (Ge (aa, ab)) = Ge (aa, ab)
  | psimpl (Divides (Var bp, af)) = Divides (Var bp, af)
  | psimpl (Divides (Neg bq, af)) = Divides (Neg bq, af)
  | psimpl (Divides (Add (br, bs), af)) = Divides (Add (br, bs), af)
  | psimpl (Divides (Sub (bt, bu), af)) = Divides (Sub (bt, bu), af)
  | psimpl (Divides (Mult (bv, bw), af)) = Divides (Mult (bv, bw), af)
  | psimpl T = T
  | psimpl F = F
  | psimpl (QAll ap) = QAll ap
  | psimpl (QEx aq) = QEx aq
  | psimpl (And (p, q)) =
    let val p' = psimpl p
    in (case p' of
         Lt (x, xa) =>
           let val q' = psimpl q
           in (case q' of Lt (x, xa) => And (p', q')
                | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                | Divides (x, xa) => And (p', q') | T => p' | F => F
                | NOT x => And (p', q') | And (x, xa) => And (p', q')
                | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                | QEx x => And (p', q'))
           end
         | Gt (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Le (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Ge (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Eq (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Divides (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | T => psimpl q | F => F
         | NOT x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | And (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Or (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Imp (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | Equ (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | QAll x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end
         | QEx x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => And (p', q')
                  | Gt (x, xa) => And (p', q') | Le (x, xa) => And (p', q')
                  | Ge (x, xa) => And (p', q') | Eq (x, xa) => And (p', q')
                  | Divides (x, xa) => And (p', q') | T => p' | F => F
                  | NOT x => And (p', q') | And (x, xa) => And (p', q')
                  | Or (x, xa) => And (p', q') | Imp (x, xa) => And (p', q')
                  | Equ (x, xa) => And (p', q') | QAll x => And (p', q')
                  | QEx x => And (p', q'))
             end)
    end
  | psimpl (Or (p, q)) =
    let val p' = psimpl p
    in (case p' of
         Lt (x, xa) =>
           let val q' = psimpl q
           in (case q' of Lt (x, xa) => Or (p', q') | Gt (x, xa) => Or (p', q')
                | Le (x, xa) => Or (p', q') | Ge (x, xa) => Or (p', q')
                | Eq (x, xa) => Or (p', q') | Divides (x, xa) => Or (p', q')
                | T => T | F => p' | NOT x => Or (p', q')
                | And (x, xa) => Or (p', q') | Or (x, xa) => Or (p', q')
                | Imp (x, xa) => Or (p', q') | Equ (x, xa) => Or (p', q')
                | QAll x => Or (p', q') | QEx x => Or (p', q'))
           end
         | Gt (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Le (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Ge (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Eq (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Divides (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | T => T | F => psimpl q
         | NOT x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | And (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Or (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Imp (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | Equ (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | QAll x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end
         | QEx x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Or (p', q')
                  | Gt (x, xa) => Or (p', q') | Le (x, xa) => Or (p', q')
                  | Ge (x, xa) => Or (p', q') | Eq (x, xa) => Or (p', q')
                  | Divides (x, xa) => Or (p', q') | T => T | F => p'
                  | NOT x => Or (p', q') | And (x, xa) => Or (p', q')
                  | Or (x, xa) => Or (p', q') | Imp (x, xa) => Or (p', q')
                  | Equ (x, xa) => Or (p', q') | QAll x => Or (p', q')
                  | QEx x => Or (p', q'))
             end)
    end
  | psimpl (Imp (p, q)) =
    let val p' = psimpl p
    in (case p' of
         Lt (x, xa) =>
           let val q' = psimpl q
           in (case q' of Lt (x, xa) => Imp (p', q')
                | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                | QEx x => Imp (p', q'))
           end
         | Gt (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Le (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Ge (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Eq (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Divides (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | T => psimpl q | F => T
         | NOT x =>
             let val q' = psimpl q
             in (case q' of Lt (xa, xb) => Or (x, q')
                  | Gt (xa, xb) => Or (x, q') | Le (xa, xb) => Or (x, q')
                  | Ge (xa, xb) => Or (x, q') | Eq (xa, xb) => Or (x, q')
                  | Divides (xa, xb) => Or (x, q') | T => T | F => x
                  | NOT xa => Or (x, q') | And (xa, xb) => Or (x, q')
                  | Or (xa, xb) => Or (x, q') | Imp (xa, xb) => Or (x, q')
                  | Equ (xa, xb) => Or (x, q') | QAll xa => Or (x, q')
                  | QEx xa => Or (x, q'))
             end
         | And (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Or (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Imp (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | Equ (x, xa) =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | QAll x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end
         | QEx x =>
             let val q' = psimpl q
             in (case q' of Lt (x, xa) => Imp (p', q')
                  | Gt (x, xa) => Imp (p', q') | Le (x, xa) => Imp (p', q')
                  | Ge (x, xa) => Imp (p', q') | Eq (x, xa) => Imp (p', q')
                  | Divides (x, xa) => Imp (p', q') | T => T | F => NOT p'
                  | NOT x => Imp (p', q') | And (x, xa) => Imp (p', q')
                  | Or (x, xa) => Imp (p', q') | Imp (x, xa) => Imp (p', q')
                  | Equ (x, xa) => Imp (p', q') | QAll x => Imp (p', q')
                  | QEx x => Imp (p', q'))
             end)
    end;

fun subst_it i (Cst b) = Cst b
  | subst_it i (Var n) = (if (n = 0) then i else Var n)
  | subst_it i (Neg it) = Neg (subst_it i it)
  | subst_it i (Add (it1, it2)) = Add (subst_it i it1, subst_it i it2)
  | subst_it i (Sub (it1, it2)) = Sub (subst_it i it1, subst_it i it2)
  | subst_it i (Mult (it1, it2)) = Mult (subst_it i it1, subst_it i it2);

fun subst_p i (Le (it1, it2)) = Le (subst_it i it1, subst_it i it2)
  | subst_p i (Lt (it1, it2)) = Lt (subst_it i it1, subst_it i it2)
  | subst_p i (Ge (it1, it2)) = Ge (subst_it i it1, subst_it i it2)
  | subst_p i (Gt (it1, it2)) = Gt (subst_it i it1, subst_it i it2)
  | subst_p i (Eq (it1, it2)) = Eq (subst_it i it1, subst_it i it2)
  | subst_p i (Divides (d, t)) = Divides (subst_it i d, subst_it i t)
  | subst_p i T = T
  | subst_p i F = F
  | subst_p i (And (p, q)) = And (subst_p i p, subst_p i q)
  | subst_p i (Or (p, q)) = Or (subst_p i p, subst_p i q)
  | subst_p i (Imp (p, q)) = Imp (subst_p i p, subst_p i q)
  | subst_p i (Equ (p, q)) = Equ (subst_p i p, subst_p i q)
  | subst_p i (NOT p) = NOT (subst_p i p);

fun explode_disj ([], p) = F
  | explode_disj ((i :: is), p) =
    let val pi = psimpl (subst_p i p)
    in (case pi of
         Lt (x, xa) =>
           let val r = explode_disj (is, p)
           in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                | T => T | F => pi | NOT x => Or (pi, r)
                | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                | QAll x => Or (pi, r) | QEx x => Or (pi, r))
           end
         | Gt (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Le (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Ge (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Eq (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Divides (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | T => T | F => explode_disj (is, p)
         | NOT x =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | And (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Or (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Imp (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | Equ (x, xa) =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | QAll x =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end
         | QEx x =>
             let val r = explode_disj (is, p)
             in (case r of Lt (x, xa) => Or (pi, r) | Gt (x, xa) => Or (pi, r)
                  | Le (x, xa) => Or (pi, r) | Ge (x, xa) => Or (pi, r)
                  | Eq (x, xa) => Or (pi, r) | Divides (x, xa) => Or (pi, r)
                  | T => T | F => pi | NOT x => Or (pi, r)
                  | And (x, xa) => Or (pi, r) | Or (x, xa) => Or (pi, r)
                  | Imp (x, xa) => Or (pi, r) | Equ (x, xa) => Or (pi, r)
                  | QAll x => Or (pi, r) | QEx x => Or (pi, r))
             end)
    end;

fun minusinf (And (p, q)) = And (minusinf p, minusinf q)
  | minusinf (Or (p, q)) = Or (minusinf p, minusinf q)
  | minusinf (Lt (u, v)) = Lt (u, v)
  | minusinf (Gt (w, x)) = Gt (w, x)
  | minusinf (Le (Cst bo, z)) = Le (Cst bo, z)
  | minusinf (Le (Var bp, z)) = Le (Var bp, z)
  | minusinf (Le (Neg bq, z)) = Le (Neg bq, z)
  | minusinf (Le (Add (Cst cg, bs), z)) = Le (Add (Cst cg, bs), z)
  | minusinf (Le (Add (Var ch, bs), z)) = Le (Add (Var ch, bs), z)
  | minusinf (Le (Add (Neg ci, bs), z)) = Le (Add (Neg ci, bs), z)
  | minusinf (Le (Add (Add (cj, ck), bs), z)) = Le (Add (Add (cj, ck), bs), z)
  | minusinf (Le (Add (Sub (cl, cm), bs), z)) = Le (Add (Sub (cl, cm), bs), z)
  | minusinf (Le (Add (Mult (Cst cy, Cst dq), bs), z)) =
    Le (Add (Mult (Cst cy, Cst dq), bs), z)
  | minusinf (Le (Add (Mult (Cst cy, Var ei), bs), z)) =
    (if (ei = 0) then (if (cy < 0) then F else T)
      else Le (Add (Mult (Cst cy, Var (op_45_def0 ei id_1_def0 + 1)), bs), z))
  | minusinf (Le (Add (Mult (Cst cy, Neg ds), bs), z)) =
    Le (Add (Mult (Cst cy, Neg ds), bs), z)
  | minusinf (Le (Add (Mult (Cst cy, Add (dt, du)), bs), z)) =
    Le (Add (Mult (Cst cy, Add (dt, du)), bs), z)
  | minusinf (Le (Add (Mult (Cst cy, Sub (dv, dw)), bs), z)) =
    Le (Add (Mult (Cst cy, Sub (dv, dw)), bs), z)
  | minusinf (Le (Add (Mult (Cst cy, Mult (dx, dy)), bs), z)) =
    Le (Add (Mult (Cst cy, Mult (dx, dy)), bs), z)
  | minusinf (Le (Add (Mult (Var cz, co), bs), z)) =
    Le (Add (Mult (Var cz, co), bs), z)
  | minusinf (Le (Add (Mult (Neg da, co), bs), z)) =
    Le (Add (Mult (Neg da, co), bs), z)
  | minusinf (Le (Add (Mult (Add (db, dc), co), bs), z)) =
    Le (Add (Mult (Add (db, dc), co), bs), z)
  | minusinf (Le (Add (Mult (Sub (dd, de), co), bs), z)) =
    Le (Add (Mult (Sub (dd, de), co), bs), z)
  | minusinf (Le (Add (Mult (Mult (df, dg), co), bs), z)) =
    Le (Add (Mult (Mult (df, dg), co), bs), z)
  | minusinf (Le (Sub (bt, bu), z)) = Le (Sub (bt, bu), z)
  | minusinf (Le (Mult (bv, bw), z)) = Le (Mult (bv, bw), z)
  | minusinf (Ge (aa, ab)) = Ge (aa, ab)
  | minusinf (Eq (Cst ek, ad)) = Eq (Cst ek, ad)
  | minusinf (Eq (Var el, ad)) = Eq (Var el, ad)
  | minusinf (Eq (Neg em, ad)) = Eq (Neg em, ad)
  | minusinf (Eq (Add (Cst fc, eo), ad)) = Eq (Add (Cst fc, eo), ad)
  | minusinf (Eq (Add (Var fd, eo), ad)) = Eq (Add (Var fd, eo), ad)
  | minusinf (Eq (Add (Neg fe, eo), ad)) = Eq (Add (Neg fe, eo), ad)
  | minusinf (Eq (Add (Add (ff, fg), eo), ad)) = Eq (Add (Add (ff, fg), eo), ad)
  | minusinf (Eq (Add (Sub (fh, fi), eo), ad)) = Eq (Add (Sub (fh, fi), eo), ad)
  | minusinf (Eq (Add (Mult (Cst fu, Cst gm), eo), ad)) =
    Eq (Add (Mult (Cst fu, Cst gm), eo), ad)
  | minusinf (Eq (Add (Mult (Cst fu, Var he), eo), ad)) =
    (if (he = 0) then F
      else Eq (Add (Mult (Cst fu, Var (op_45_def0 he id_1_def0 + 1)), eo), ad))
  | minusinf (Eq (Add (Mult (Cst fu, Neg go), eo), ad)) =
    Eq (Add (Mult (Cst fu, Neg go), eo), ad)
  | minusinf (Eq (Add (Mult (Cst fu, Add (gp, gq)), eo), ad)) =
    Eq (Add (Mult (Cst fu, Add (gp, gq)), eo), ad)
  | minusinf (Eq (Add (Mult (Cst fu, Sub (gr, gs)), eo), ad)) =
    Eq (Add (Mult (Cst fu, Sub (gr, gs)), eo), ad)
  | minusinf (Eq (Add (Mult (Cst fu, Mult (gt, gu)), eo), ad)) =
    Eq (Add (Mult (Cst fu, Mult (gt, gu)), eo), ad)
  | minusinf (Eq (Add (Mult (Var fv, fk), eo), ad)) =
    Eq (Add (Mult (Var fv, fk), eo), ad)
  | minusinf (Eq (Add (Mult (Neg fw, fk), eo), ad)) =
    Eq (Add (Mult (Neg fw, fk), eo), ad)
  | minusinf (Eq (Add (Mult (Add (fx, fy), fk), eo), ad)) =
    Eq (Add (Mult (Add (fx, fy), fk), eo), ad)
  | minusinf (Eq (Add (Mult (Sub (fz, ga), fk), eo), ad)) =
    Eq (Add (Mult (Sub (fz, ga), fk), eo), ad)
  | minusinf (Eq (Add (Mult (Mult (gb, gc), fk), eo), ad)) =
    Eq (Add (Mult (Mult (gb, gc), fk), eo), ad)
  | minusinf (Eq (Sub (ep, eq), ad)) = Eq (Sub (ep, eq), ad)
  | minusinf (Eq (Mult (er, es), ad)) = Eq (Mult (er, es), ad)
  | minusinf (Divides (ae, af)) = Divides (ae, af)
  | minusinf T = T
  | minusinf F = F
  | minusinf (NOT (Lt (hg, hh))) = NOT (Lt (hg, hh))
  | minusinf (NOT (Gt (hi, hj))) = NOT (Gt (hi, hj))
  | minusinf (NOT (Le (hk, hl))) = NOT (Le (hk, hl))
  | minusinf (NOT (Ge (hm, hn))) = NOT (Ge (hm, hn))
  | minusinf (NOT (Eq (Cst ja, hp))) = NOT (Eq (Cst ja, hp))
  | minusinf (NOT (Eq (Var jb, hp))) = NOT (Eq (Var jb, hp))
  | minusinf (NOT (Eq (Neg jc, hp))) = NOT (Eq (Neg jc, hp))
  | minusinf (NOT (Eq (Add (Cst js, je), hp))) = NOT (Eq (Add (Cst js, je), hp))
  | minusinf (NOT (Eq (Add (Var jt, je), hp))) = NOT (Eq (Add (Var jt, je), hp))
  | minusinf (NOT (Eq (Add (Neg ju, je), hp))) = NOT (Eq (Add (Neg ju, je), hp))
  | minusinf (NOT (Eq (Add (Add (jv, jw), je), hp))) =
    NOT (Eq (Add (Add (jv, jw), je), hp))
  | minusinf (NOT (Eq (Add (Sub (jx, jy), je), hp))) =
    NOT (Eq (Add (Sub (jx, jy), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Cst kk, Cst lc), je), hp))) =
    NOT (Eq (Add (Mult (Cst kk, Cst lc), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Cst kk, Var lu), je), hp))) =
    (if (lu = 0) then T
      else NOT (Eq (Add (Mult (Cst kk, Var (op_45_def0 lu id_1_def0 + 1)), je),
                     hp)))
  | minusinf (NOT (Eq (Add (Mult (Cst kk, Neg le), je), hp))) =
    NOT (Eq (Add (Mult (Cst kk, Neg le), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Cst kk, Add (lf, lg)), je), hp))) =
    NOT (Eq (Add (Mult (Cst kk, Add (lf, lg)), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Cst kk, Sub (lh, li)), je), hp))) =
    NOT (Eq (Add (Mult (Cst kk, Sub (lh, li)), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Cst kk, Mult (lj, lk)), je), hp))) =
    NOT (Eq (Add (Mult (Cst kk, Mult (lj, lk)), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Var kl, ka), je), hp))) =
    NOT (Eq (Add (Mult (Var kl, ka), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Neg km, ka), je), hp))) =
    NOT (Eq (Add (Mult (Neg km, ka), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Add (kn, ko), ka), je), hp))) =
    NOT (Eq (Add (Mult (Add (kn, ko), ka), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Sub (kp, kq), ka), je), hp))) =
    NOT (Eq (Add (Mult (Sub (kp, kq), ka), je), hp))
  | minusinf (NOT (Eq (Add (Mult (Mult (kr, ks), ka), je), hp))) =
    NOT (Eq (Add (Mult (Mult (kr, ks), ka), je), hp))
  | minusinf (NOT (Eq (Sub (jf, jg), hp))) = NOT (Eq (Sub (jf, jg), hp))
  | minusinf (NOT (Eq (Mult (jh, ji), hp))) = NOT (Eq (Mult (jh, ji), hp))
  | minusinf (NOT (Divides (hq, hr))) = NOT (Divides (hq, hr))
  | minusinf (NOT T) = NOT T
  | minusinf (NOT F) = NOT F
  | minusinf (NOT (NOT hs)) = NOT (NOT hs)
  | minusinf (NOT (And (ht, hu))) = NOT (And (ht, hu))
  | minusinf (NOT (Or (hv, hw))) = NOT (Or (hv, hw))
  | minusinf (NOT (Imp (hx, hy))) = NOT (Imp (hx, hy))
  | minusinf (NOT (Equ (hz, ia))) = NOT (Equ (hz, ia))
  | minusinf (NOT (QAll ib)) = NOT (QAll ib)
  | minusinf (NOT (QEx ic)) = NOT (QEx ic)
  | minusinf (Imp (al, am)) = Imp (al, am)
  | minusinf (Equ (an, ao)) = Equ (an, ao)
  | minusinf (QAll ap) = QAll ap
  | minusinf (QEx aq) = QEx aq;

fun abs i = (if (i < 0) then ~ i else i);

fun op_div_def1 a b = fst (divAlg (a, b));

fun op_mod_def0 m n = nat (op_mod_def1 (m) (n));

fun ngcd (m, n) = (if (n = 0) then m else ngcd (n, op_mod_def0 m n));

fun igcd x = split (fn a => fn b => (ngcd (nat (abs a), nat (abs b)))) x;

fun ilcm a b = op_div_def1 (a * b) (igcd (a, b));

fun divlcm (NOT p) = divlcm p
  | divlcm (And (p, q)) = ilcm (divlcm p) (divlcm q)
  | divlcm (Or (p, q)) = ilcm (divlcm p) (divlcm q)
  | divlcm (Lt (u, v)) = 1
  | divlcm (Gt (w, x)) = 1
  | divlcm (Le (y, z)) = 1
  | divlcm (Ge (aa, ab)) = 1
  | divlcm (Eq (ac, ad)) = 1
  | divlcm (Divides (Cst bo, Cst cg)) = 1
  | divlcm (Divides (Cst bo, Var ch)) = 1
  | divlcm (Divides (Cst bo, Neg ci)) = 1
  | divlcm (Divides (Cst bo, Add (Cst cy, ck))) = 1
  | divlcm (Divides (Cst bo, Add (Var cz, ck))) = 1
  | divlcm (Divides (Cst bo, Add (Neg da, ck))) = 1
  | divlcm (Divides (Cst bo, Add (Add (db, dc), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Sub (dd, de), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Cst dq, Cst ei), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Cst dq, Var fa), ck))) =
    (if (fa = 0) then abs bo else 1)
  | divlcm (Divides (Cst bo, Add (Mult (Cst dq, Neg ek), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Cst dq, Add (el, em)), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Cst dq, Sub (en, eo)), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Cst dq, Mult (ep, eq)), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Var dr, dg), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Neg ds, dg), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Add (dt, du), dg), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Sub (dv, dw), dg), ck))) = 1
  | divlcm (Divides (Cst bo, Add (Mult (Mult (dx, dy), dg), ck))) = 1
  | divlcm (Divides (Cst bo, Sub (cl, cm))) = 1
  | divlcm (Divides (Cst bo, Mult (cn, co))) = 1
  | divlcm (Divides (Var bp, af)) = 1
  | divlcm (Divides (Neg bq, af)) = 1
  | divlcm (Divides (Add (br, bs), af)) = 1
  | divlcm (Divides (Sub (bt, bu), af)) = 1
  | divlcm (Divides (Mult (bv, bw), af)) = 1
  | divlcm T = 1
  | divlcm F = 1
  | divlcm (Imp (al, am)) = 1
  | divlcm (Equ (an, ao)) = 1
  | divlcm (QAll ap) = 1
  | divlcm (QEx aq) = 1;

fun explode_minf (q, B) =
    let val d = divlcm q; val pm = minusinf q;
        val dj1 = explode_disj (map (fn x => Cst x) (iupto (1, d)), pm)
    in (case dj1 of
         Lt (x, xa) =>
           let val dj2 = explode_disj (all_sums (d, B), q)
           in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                | QEx x => Or (dj1, dj2))
           end
         | Gt (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Le (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Ge (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Eq (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Divides (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | T => T | F => explode_disj (all_sums (d, B), q)
         | NOT x =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | And (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Or (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Imp (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | Equ (x, xa) =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | QAll x =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end
         | QEx x =>
             let val dj2 = explode_disj (all_sums (d, B), q)
             in (case dj2 of Lt (x, xa) => Or (dj1, dj2)
                  | Gt (x, xa) => Or (dj1, dj2) | Le (x, xa) => Or (dj1, dj2)
                  | Ge (x, xa) => Or (dj1, dj2) | Eq (x, xa) => Or (dj1, dj2)
                  | Divides (x, xa) => Or (dj1, dj2) | T => T | F => dj1
                  | NOT x => Or (dj1, dj2) | And (x, xa) => Or (dj1, dj2)
                  | Or (x, xa) => Or (dj1, dj2) | Imp (x, xa) => Or (dj1, dj2)
                  | Equ (x, xa) => Or (dj1, dj2) | QAll x => Or (dj1, dj2)
                  | QEx x => Or (dj1, dj2))
             end)
    end;

fun mirror (And (p, q)) = And (mirror p, mirror q)
  | mirror (Or (p, q)) = Or (mirror p, mirror q)
  | mirror (Lt (u, v)) = Lt (u, v)
  | mirror (Gt (w, x)) = Gt (w, x)
  | mirror (Le (Cst bp, aa)) = Le (Cst bp, aa)
  | mirror (Le (Var bq, aa)) = Le (Var bq, aa)
  | mirror (Le (Neg br, aa)) = Le (Neg br, aa)
  | mirror (Le (Add (Cst ch, bt), aa)) = Le (Add (Cst ch, bt), aa)
  | mirror (Le (Add (Var ci, bt), aa)) = Le (Add (Var ci, bt), aa)
  | mirror (Le (Add (Neg cj, bt), aa)) = Le (Add (Neg cj, bt), aa)
  | mirror (Le (Add (Add (ck, cl), bt), aa)) = Le (Add (Add (ck, cl), bt), aa)
  | mirror (Le (Add (Sub (cm, cn), bt), aa)) = Le (Add (Sub (cm, cn), bt), aa)
  | mirror (Le (Add (Mult (Cst cz, Cst dr), bt), aa)) =
    Le (Add (Mult (Cst cz, Cst dr), bt), aa)
  | mirror (Le (Add (Mult (Cst cz, Var ej), bt), aa)) =
    (if (ej = 0) then Le (Add (Mult (Cst (~ cz), Var 0), bt), aa)
      else Le (Add (Mult (Cst cz, Var (op_45_def0 ej id_1_def0 + 1)), bt), aa))
  | mirror (Le (Add (Mult (Cst cz, Neg dt), bt), aa)) =
    Le (Add (Mult (Cst cz, Neg dt), bt), aa)
  | mirror (Le (Add (Mult (Cst cz, Add (du, dv)), bt), aa)) =
    Le (Add (Mult (Cst cz, Add (du, dv)), bt), aa)
  | mirror (Le (Add (Mult (Cst cz, Sub (dw, dx)), bt), aa)) =
    Le (Add (Mult (Cst cz, Sub (dw, dx)), bt), aa)
  | mirror (Le (Add (Mult (Cst cz, Mult (dy, dz)), bt), aa)) =
    Le (Add (Mult (Cst cz, Mult (dy, dz)), bt), aa)
  | mirror (Le (Add (Mult (Var da, cp), bt), aa)) =
    Le (Add (Mult (Var da, cp), bt), aa)
  | mirror (Le (Add (Mult (Neg db, cp), bt), aa)) =
    Le (Add (Mult (Neg db, cp), bt), aa)
  | mirror (Le (Add (Mult (Add (dc, dd), cp), bt), aa)) =
    Le (Add (Mult (Add (dc, dd), cp), bt), aa)
  | mirror (Le (Add (Mult (Sub (de, df), cp), bt), aa)) =
    Le (Add (Mult (Sub (de, df), cp), bt), aa)
  | mirror (Le (Add (Mult (Mult (dg, dh), cp), bt), aa)) =
    Le (Add (Mult (Mult (dg, dh), cp), bt), aa)
  | mirror (Le (Sub (bu, bv), aa)) = Le (Sub (bu, bv), aa)
  | mirror (Le (Mult (bw, bx), aa)) = Le (Mult (bw, bx), aa)
  | mirror (Ge (ab, ac)) = Ge (ab, ac)
  | mirror (Eq (Cst el, ae)) = Eq (Cst el, ae)
  | mirror (Eq (Var em, ae)) = Eq (Var em, ae)
  | mirror (Eq (Neg en, ae)) = Eq (Neg en, ae)
  | mirror (Eq (Add (Cst fd, ep), ae)) = Eq (Add (Cst fd, ep), ae)
  | mirror (Eq (Add (Var fe, ep), ae)) = Eq (Add (Var fe, ep), ae)
  | mirror (Eq (Add (Neg ff, ep), ae)) = Eq (Add (Neg ff, ep), ae)
  | mirror (Eq (Add (Add (fg, fh), ep), ae)) = Eq (Add (Add (fg, fh), ep), ae)
  | mirror (Eq (Add (Sub (fi, fj), ep), ae)) = Eq (Add (Sub (fi, fj), ep), ae)
  | mirror (Eq (Add (Mult (Cst fv, Cst gn), ep), ae)) =
    Eq (Add (Mult (Cst fv, Cst gn), ep), ae)
  | mirror (Eq (Add (Mult (Cst fv, Var hf), ep), ae)) =
    (if (hf = 0) then Eq (Add (Mult (Cst (~ fv), Var 0), ep), ae)
      else Eq (Add (Mult (Cst fv, Var (op_45_def0 hf id_1_def0 + 1)), ep), ae))
  | mirror (Eq (Add (Mult (Cst fv, Neg gp), ep), ae)) =
    Eq (Add (Mult (Cst fv, Neg gp), ep), ae)
  | mirror (Eq (Add (Mult (Cst fv, Add (gq, gr)), ep), ae)) =
    Eq (Add (Mult (Cst fv, Add (gq, gr)), ep), ae)
  | mirror (Eq (Add (Mult (Cst fv, Sub (gs, gt)), ep), ae)) =
    Eq (Add (Mult (Cst fv, Sub (gs, gt)), ep), ae)
  | mirror (Eq (Add (Mult (Cst fv, Mult (gu, gv)), ep), ae)) =
    Eq (Add (Mult (Cst fv, Mult (gu, gv)), ep), ae)
  | mirror (Eq (Add (Mult (Var fw, fl), ep), ae)) =
    Eq (Add (Mult (Var fw, fl), ep), ae)
  | mirror (Eq (Add (Mult (Neg fx, fl), ep), ae)) =
    Eq (Add (Mult (Neg fx, fl), ep), ae)
  | mirror (Eq (Add (Mult (Add (fy, fz), fl), ep), ae)) =
    Eq (Add (Mult (Add (fy, fz), fl), ep), ae)
  | mirror (Eq (Add (Mult (Sub (ga, gb), fl), ep), ae)) =
    Eq (Add (Mult (Sub (ga, gb), fl), ep), ae)
  | mirror (Eq (Add (Mult (Mult (gc, gd), fl), ep), ae)) =
    Eq (Add (Mult (Mult (gc, gd), fl), ep), ae)
  | mirror (Eq (Sub (eq, er), ae)) = Eq (Sub (eq, er), ae)
  | mirror (Eq (Mult (es, et), ae)) = Eq (Mult (es, et), ae)
  | mirror (Divides (Cst hh, Cst hz)) = Divides (Cst hh, Cst hz)
  | mirror (Divides (Cst hh, Var ia)) = Divides (Cst hh, Var ia)
  | mirror (Divides (Cst hh, Neg ib)) = Divides (Cst hh, Neg ib)
  | mirror (Divides (Cst hh, Add (Cst ir, id))) =
    Divides (Cst hh, Add (Cst ir, id))
  | mirror (Divides (Cst hh, Add (Var is, id))) =
    Divides (Cst hh, Add (Var is, id))
  | mirror (Divides (Cst hh, Add (Neg it, id))) =
    Divides (Cst hh, Add (Neg it, id))
  | mirror (Divides (Cst hh, Add (Add (iu, iv), id))) =
    Divides (Cst hh, Add (Add (iu, iv), id))
  | mirror (Divides (Cst hh, Add (Sub (iw, ix), id))) =
    Divides (Cst hh, Add (Sub (iw, ix), id))
  | mirror (Divides (Cst hh, Add (Mult (Cst jj, Cst kb), id))) =
    Divides (Cst hh, Add (Mult (Cst jj, Cst kb), id))
  | mirror (Divides (Cst hh, Add (Mult (Cst jj, Var kt), id))) =
    (if (kt = 0) then Divides (Cst hh, Add (Mult (Cst (~ jj), Var 0), id))
      else Divides
             (Cst hh,
               Add (Mult (Cst jj, Var (op_45_def0 kt id_1_def0 + 1)), id)))
  | mirror (Divides (Cst hh, Add (Mult (Cst jj, Neg kd), id))) =
    Divides (Cst hh, Add (Mult (Cst jj, Neg kd), id))
  | mirror (Divides (Cst hh, Add (Mult (Cst jj, Add (ke, kf)), id))) =
    Divides (Cst hh, Add (Mult (Cst jj, Add (ke, kf)), id))
  | mirror (Divides (Cst hh, Add (Mult (Cst jj, Sub (kg, kh)), id))) =
    Divides (Cst hh, Add (Mult (Cst jj, Sub (kg, kh)), id))
  | mirror (Divides (Cst hh, Add (Mult (Cst jj, Mult (ki, kj)), id))) =
    Divides (Cst hh, Add (Mult (Cst jj, Mult (ki, kj)), id))
  | mirror (Divides (Cst hh, Add (Mult (Var jk, iz), id))) =
    Divides (Cst hh, Add (Mult (Var jk, iz), id))
  | mirror (Divides (Cst hh, Add (Mult (Neg jl, iz), id))) =
    Divides (Cst hh, Add (Mult (Neg jl, iz), id))
  | mirror (Divides (Cst hh, Add (Mult (Add (jm, jn), iz), id))) =
    Divides (Cst hh, Add (Mult (Add (jm, jn), iz), id))
  | mirror (Divides (Cst hh, Add (Mult (Sub (jo, jp), iz), id))) =
    Divides (Cst hh, Add (Mult (Sub (jo, jp), iz), id))
  | mirror (Divides (Cst hh, Add (Mult (Mult (jq, jr), iz), id))) =
    Divides (Cst hh, Add (Mult (Mult (jq, jr), iz), id))
  | mirror (Divides (Cst hh, Sub (ie, if'))) = Divides (Cst hh, Sub (ie, if'))
  | mirror (Divides (Cst hh, Mult (ig, ih))) = Divides (Cst hh, Mult (ig, ih))
  | mirror (Divides (Var hi, ag)) = Divides (Var hi, ag)
  | mirror (Divides (Neg hj, ag)) = Divides (Neg hj, ag)
  | mirror (Divides (Add (hk, hl), ag)) = Divides (Add (hk, hl), ag)
  | mirror (Divides (Sub (hm, hn), ag)) = Divides (Sub (hm, hn), ag)
  | mirror (Divides (Mult (ho, hp), ag)) = Divides (Mult (ho, hp), ag)
  | mirror T = T
  | mirror F = F
  | mirror (NOT (Lt (kv, kw))) = NOT (Lt (kv, kw))
  | mirror (NOT (Gt (kx, ky))) = NOT (Gt (kx, ky))
  | mirror (NOT (Le (kz, la))) = NOT (Le (kz, la))
  | mirror (NOT (Ge (lb, lc))) = NOT (Ge (lb, lc))
  | mirror (NOT (Eq (Cst mp, le))) = NOT (Eq (Cst mp, le))
  | mirror (NOT (Eq (Var mq, le))) = NOT (Eq (Var mq, le))
  | mirror (NOT (Eq (Neg mr, le))) = NOT (Eq (Neg mr, le))
  | mirror (NOT (Eq (Add (Cst nh, mt), le))) = NOT (Eq (Add (Cst nh, mt), le))
  | mirror (NOT (Eq (Add (Var ni, mt), le))) = NOT (Eq (Add (Var ni, mt), le))
  | mirror (NOT (Eq (Add (Neg nj, mt), le))) = NOT (Eq (Add (Neg nj, mt), le))
  | mirror (NOT (Eq (Add (Add (nk, nl), mt), le))) =
    NOT (Eq (Add (Add (nk, nl), mt), le))
  | mirror (NOT (Eq (Add (Sub (nm, nn), mt), le))) =
    NOT (Eq (Add (Sub (nm, nn), mt), le))
  | mirror (NOT (Eq (Add (Mult (Cst nz, Cst or), mt), le))) =
    NOT (Eq (Add (Mult (Cst nz, Cst or), mt), le))
  | mirror (NOT (Eq (Add (Mult (Cst nz, Var pj), mt), le))) =
    (if (pj = 0) then NOT (Eq (Add (Mult (Cst (~ nz), Var 0), mt), le))
      else NOT (Eq (Add (Mult (Cst nz, Var (op_45_def0 pj id_1_def0 + 1)), mt),
                     le)))
  | mirror (NOT (Eq (Add (Mult (Cst nz, Neg ot), mt), le))) =
    NOT (Eq (Add (Mult (Cst nz, Neg ot), mt), le))
  | mirror (NOT (Eq (Add (Mult (Cst nz, Add (ou, ov)), mt), le))) =
    NOT (Eq (Add (Mult (Cst nz, Add (ou, ov)), mt), le))
  | mirror (NOT (Eq (Add (Mult (Cst nz, Sub (ow, ox)), mt), le))) =
    NOT (Eq (Add (Mult (Cst nz, Sub (ow, ox)), mt), le))
  | mirror (NOT (Eq (Add (Mult (Cst nz, Mult (oy, oz)), mt), le))) =
    NOT (Eq (Add (Mult (Cst nz, Mult (oy, oz)), mt), le))
  | mirror (NOT (Eq (Add (Mult (Var oa, np), mt), le))) =
    NOT (Eq (Add (Mult (Var oa, np), mt), le))
  | mirror (NOT (Eq (Add (Mult (Neg ob, np), mt), le))) =
    NOT (Eq (Add (Mult (Neg ob, np), mt), le))
  | mirror (NOT (Eq (Add (Mult (Add (oc, od), np), mt), le))) =
    NOT (Eq (Add (Mult (Add (oc, od), np), mt), le))
  | mirror (NOT (Eq (Add (Mult (Sub (oe, of'), np), mt), le))) =
    NOT (Eq (Add (Mult (Sub (oe, of'), np), mt), le))
  | mirror (NOT (Eq (Add (Mult (Mult (og, oh), np), mt), le))) =
    NOT (Eq (Add (Mult (Mult (og, oh), np), mt), le))
  | mirror (NOT (Eq (Sub (mu, mv), le))) = NOT (Eq (Sub (mu, mv), le))
  | mirror (NOT (Eq (Mult (mw, mx), le))) = NOT (Eq (Mult (mw, mx), le))
  | mirror (NOT (Divides (Cst pl, Cst qd))) = NOT (Divides (Cst pl, Cst qd))
  | mirror (NOT (Divides (Cst pl, Var qe))) = NOT (Divides (Cst pl, Var qe))
  | mirror (NOT (Divides (Cst pl, Neg qf))) = NOT (Divides (Cst pl, Neg qf))
  | mirror (NOT (Divides (Cst pl, Add (Cst qv, qh)))) =
    NOT (Divides (Cst pl, Add (Cst qv, qh)))
  | mirror (NOT (Divides (Cst pl, Add (Var qw, qh)))) =
    NOT (Divides (Cst pl, Add (Var qw, qh)))
  | mirror (NOT (Divides (Cst pl, Add (Neg qx, qh)))) =
    NOT (Divides (Cst pl, Add (Neg qx, qh)))
  | mirror (NOT (Divides (Cst pl, Add (Add (qy, qz), qh)))) =
    NOT (Divides (Cst pl, Add (Add (qy, qz), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Sub (ra, rb), qh)))) =
    NOT (Divides (Cst pl, Add (Sub (ra, rb), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Cst rn, Cst sf), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Cst rn, Cst sf), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Cst rn, Var sx), qh)))) =
    (if (sx = 0)
      then NOT (Divides (Cst pl, Add (Mult (Cst (~ rn), Var 0), qh)))
      else NOT (Divides
                  (Cst pl,
                    Add (Mult (Cst rn, Var (op_45_def0 sx id_1_def0 + 1)),
                          qh))))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Cst rn, Neg sh), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Cst rn, Neg sh), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Cst rn, Add (si, sj)), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Cst rn, Add (si, sj)), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Cst rn, Sub (sk, sl)), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Cst rn, Sub (sk, sl)), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Cst rn, Mult (sm, sn)), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Cst rn, Mult (sm, sn)), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Var ro, rd), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Var ro, rd), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Neg rp, rd), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Neg rp, rd), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Add (rq, rr), rd), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Add (rq, rr), rd), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Sub (rs, rt), rd), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Sub (rs, rt), rd), qh)))
  | mirror (NOT (Divides (Cst pl, Add (Mult (Mult (ru, rv), rd), qh)))) =
    NOT (Divides (Cst pl, Add (Mult (Mult (ru, rv), rd), qh)))
  | mirror (NOT (Divides (Cst pl, Sub (qi, qj)))) =
    NOT (Divides (Cst pl, Sub (qi, qj)))
  | mirror (NOT (Divides (Cst pl, Mult (qk, ql)))) =
    NOT (Divides (Cst pl, Mult (qk, ql)))
  | mirror (NOT (Divides (Var pm, lg))) = NOT (Divides (Var pm, lg))
  | mirror (NOT (Divides (Neg pn, lg))) = NOT (Divides (Neg pn, lg))
  | mirror (NOT (Divides (Add (po, pp), lg))) = NOT (Divides (Add (po, pp), lg))
  | mirror (NOT (Divides (Sub (pq, pr), lg))) = NOT (Divides (Sub (pq, pr), lg))
  | mirror (NOT (Divides (Mult (ps, pt), lg))) =
    NOT (Divides (Mult (ps, pt), lg))
  | mirror (NOT T) = NOT T
  | mirror (NOT F) = NOT F
  | mirror (NOT (NOT lh)) = NOT (NOT lh)
  | mirror (NOT (And (li, lj))) = NOT (And (li, lj))
  | mirror (NOT (Or (lk, ll))) = NOT (Or (lk, ll))
  | mirror (NOT (Imp (lm, ln))) = NOT (Imp (lm, ln))
  | mirror (NOT (Equ (lo, lp))) = NOT (Equ (lo, lp))
  | mirror (NOT (QAll lq)) = NOT (QAll lq)
  | mirror (NOT (QEx lr)) = NOT (QEx lr)
  | mirror (Imp (am, an)) = Imp (am, an)
  | mirror (Equ (ao, ap)) = Equ (ao, ap)
  | mirror (QAll aq) = QAll aq
  | mirror (QEx ar) = QEx ar;

fun op_43_def0 m n = nat ((m) + (n));

fun size_def1 [] = 0
  | size_def1 (a :: list) = op_43_def0 (size_def1 list) (0 + 1);

fun aset (And (p, q)) = op_64 (aset p) (aset q)
  | aset (Or (p, q)) = op_64 (aset p) (aset q)
  | aset (Lt (u, v)) = []
  | aset (Gt (w, x)) = []
  | aset (Le (Cst bo, z)) = []
  | aset (Le (Var bp, z)) = []
  | aset (Le (Neg bq, z)) = []
  | aset (Le (Add (Cst cg, bs), z)) = []
  | aset (Le (Add (Var ch, bs), z)) = []
  | aset (Le (Add (Neg ci, bs), z)) = []
  | aset (Le (Add (Add (cj, ck), bs), z)) = []
  | aset (Le (Add (Sub (cl, cm), bs), z)) = []
  | aset (Le (Add (Mult (Cst cy, Cst dq), bs), z)) = []
  | aset (Le (Add (Mult (Cst cy, Var ei), bs), z)) =
    (if (ei = 0)
      then (if (cy < 0) then [lin_add (bs, Cst 1)]
             else [lin_neg bs, lin_add (lin_neg bs, Cst 1)])
      else [])
  | aset (Le (Add (Mult (Cst cy, Neg ds), bs), z)) = []
  | aset (Le (Add (Mult (Cst cy, Add (dt, du)), bs), z)) = []
  | aset (Le (Add (Mult (Cst cy, Sub (dv, dw)), bs), z)) = []
  | aset (Le (Add (Mult (Cst cy, Mult (dx, dy)), bs), z)) = []
  | aset (Le (Add (Mult (Var cz, co), bs), z)) = []
  | aset (Le (Add (Mult (Neg da, co), bs), z)) = []
  | aset (Le (Add (Mult (Add (db, dc), co), bs), z)) = []
  | aset (Le (Add (Mult (Sub (dd, de), co), bs), z)) = []
  | aset (Le (Add (Mult (Mult (df, dg), co), bs), z)) = []
  | aset (Le (Sub (bt, bu), z)) = []
  | aset (Le (Mult (bv, bw), z)) = []
  | aset (Ge (aa, ab)) = []
  | aset (Eq (Cst ek, ad)) = []
  | aset (Eq (Var el, ad)) = []
  | aset (Eq (Neg em, ad)) = []
  | aset (Eq (Add (Cst fc, eo), ad)) = []
  | aset (Eq (Add (Var fd, eo), ad)) = []
  | aset (Eq (Add (Neg fe, eo), ad)) = []
  | aset (Eq (Add (Add (ff, fg), eo), ad)) = []
  | aset (Eq (Add (Sub (fh, fi), eo), ad)) = []
  | aset (Eq (Add (Mult (Cst fu, Cst gm), eo), ad)) = []
  | aset (Eq (Add (Mult (Cst fu, Var he), eo), ad)) =
    (if (he = 0)
      then (if (fu < 0) then [lin_add (eo, Cst 1)]
             else [lin_add (lin_neg eo, Cst 1)])
      else [])
  | aset (Eq (Add (Mult (Cst fu, Neg go), eo), ad)) = []
  | aset (Eq (Add (Mult (Cst fu, Add (gp, gq)), eo), ad)) = []
  | aset (Eq (Add (Mult (Cst fu, Sub (gr, gs)), eo), ad)) = []
  | aset (Eq (Add (Mult (Cst fu, Mult (gt, gu)), eo), ad)) = []
  | aset (Eq (Add (Mult (Var fv, fk), eo), ad)) = []
  | aset (Eq (Add (Mult (Neg fw, fk), eo), ad)) = []
  | aset (Eq (Add (Mult (Add (fx, fy), fk), eo), ad)) = []
  | aset (Eq (Add (Mult (Sub (fz, ga), fk), eo), ad)) = []
  | aset (Eq (Add (Mult (Mult (gb, gc), fk), eo), ad)) = []
  | aset (Eq (Sub (ep, eq), ad)) = []
  | aset (Eq (Mult (er, es), ad)) = []
  | aset (Divides (ae, af)) = []
  | aset T = []
  | aset F = []
  | aset (NOT (Lt (hg, hh))) = []
  | aset (NOT (Gt (hi, hj))) = []
  | aset (NOT (Le (hk, hl))) = []
  | aset (NOT (Ge (hm, hn))) = []
  | aset (NOT (Eq (Cst ja, hp))) = []
  | aset (NOT (Eq (Var jb, hp))) = []
  | aset (NOT (Eq (Neg jc, hp))) = []
  | aset (NOT (Eq (Add (Cst js, je), hp))) = []
  | aset (NOT (Eq (Add (Var jt, je), hp))) = []
  | aset (NOT (Eq (Add (Neg ju, je), hp))) = []
  | aset (NOT (Eq (Add (Add (jv, jw), je), hp))) = []
  | aset (NOT (Eq (Add (Sub (jx, jy), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Cst kk, Cst lc), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Cst kk, Var lu), je), hp))) =
    (if (lu = 0) then (if (kk < 0) then [je] else [lin_neg je]) else [])
  | aset (NOT (Eq (Add (Mult (Cst kk, Neg le), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Cst kk, Add (lf, lg)), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Cst kk, Sub (lh, li)), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Cst kk, Mult (lj, lk)), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Var kl, ka), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Neg km, ka), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Add (kn, ko), ka), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Sub (kp, kq), ka), je), hp))) = []
  | aset (NOT (Eq (Add (Mult (Mult (kr, ks), ka), je), hp))) = []
  | aset (NOT (Eq (Sub (jf, jg), hp))) = []
  | aset (NOT (Eq (Mult (jh, ji), hp))) = []
  | aset (NOT (Divides (hq, hr))) = []
  | aset (NOT T) = []
  | aset (NOT F) = []
  | aset (NOT (NOT hs)) = []
  | aset (NOT (And (ht, hu))) = []
  | aset (NOT (Or (hv, hw))) = []
  | aset (NOT (Imp (hx, hy))) = []
  | aset (NOT (Equ (hz, ia))) = []
  | aset (NOT (QAll ib)) = []
  | aset (NOT (QEx ic)) = []
  | aset (Imp (al, am)) = []
  | aset (Equ (an, ao)) = []
  | aset (QAll ap) = []
  | aset (QEx aq) = [];

fun op_mem x [] = false
  | op_mem x (y :: ys) = (if (y = x) then true else op_mem x ys);

fun list_insert x xs = (if op_mem x xs then xs else (x :: xs));

fun list_set [] = []
  | list_set (x :: xs) = list_insert x (list_set xs);

fun bset (And (p, q)) = op_64 (bset p) (bset q)
  | bset (Or (p, q)) = op_64 (bset p) (bset q)
  | bset (Lt (u, v)) = []
  | bset (Gt (w, x)) = []
  | bset (Le (Cst bo, z)) = []
  | bset (Le (Var bp, z)) = []
  | bset (Le (Neg bq, z)) = []
  | bset (Le (Add (Cst cg, bs), z)) = []
  | bset (Le (Add (Var ch, bs), z)) = []
  | bset (Le (Add (Neg ci, bs), z)) = []
  | bset (Le (Add (Add (cj, ck), bs), z)) = []
  | bset (Le (Add (Sub (cl, cm), bs), z)) = []
  | bset (Le (Add (Mult (Cst cy, Cst dq), bs), z)) = []
  | bset (Le (Add (Mult (Cst cy, Var ei), bs), z)) =
    (if (ei = 0)
      then (if (cy < 0) then [lin_add (bs, Cst ~1), bs]
             else [lin_add (lin_neg bs, Cst ~1)])
      else [])
  | bset (Le (Add (Mult (Cst cy, Neg ds), bs), z)) = []
  | bset (Le (Add (Mult (Cst cy, Add (dt, du)), bs), z)) = []
  | bset (Le (Add (Mult (Cst cy, Sub (dv, dw)), bs), z)) = []
  | bset (Le (Add (Mult (Cst cy, Mult (dx, dy)), bs), z)) = []
  | bset (Le (Add (Mult (Var cz, co), bs), z)) = []
  | bset (Le (Add (Mult (Neg da, co), bs), z)) = []
  | bset (Le (Add (Mult (Add (db, dc), co), bs), z)) = []
  | bset (Le (Add (Mult (Sub (dd, de), co), bs), z)) = []
  | bset (Le (Add (Mult (Mult (df, dg), co), bs), z)) = []
  | bset (Le (Sub (bt, bu), z)) = []
  | bset (Le (Mult (bv, bw), z)) = []
  | bset (Ge (aa, ab)) = []
  | bset (Eq (Cst ek, ad)) = []
  | bset (Eq (Var el, ad)) = []
  | bset (Eq (Neg em, ad)) = []
  | bset (Eq (Add (Cst fc, eo), ad)) = []
  | bset (Eq (Add (Var fd, eo), ad)) = []
  | bset (Eq (Add (Neg fe, eo), ad)) = []
  | bset (Eq (Add (Add (ff, fg), eo), ad)) = []
  | bset (Eq (Add (Sub (fh, fi), eo), ad)) = []
  | bset (Eq (Add (Mult (Cst fu, Cst gm), eo), ad)) = []
  | bset (Eq (Add (Mult (Cst fu, Var he), eo), ad)) =
    (if (he = 0)
      then (if (fu < 0) then [lin_add (eo, Cst ~1)]
             else [lin_add (lin_neg eo, Cst ~1)])
      else [])
  | bset (Eq (Add (Mult (Cst fu, Neg go), eo), ad)) = []
  | bset (Eq (Add (Mult (Cst fu, Add (gp, gq)), eo), ad)) = []
  | bset (Eq (Add (Mult (Cst fu, Sub (gr, gs)), eo), ad)) = []
  | bset (Eq (Add (Mult (Cst fu, Mult (gt, gu)), eo), ad)) = []
  | bset (Eq (Add (Mult (Var fv, fk), eo), ad)) = []
  | bset (Eq (Add (Mult (Neg fw, fk), eo), ad)) = []
  | bset (Eq (Add (Mult (Add (fx, fy), fk), eo), ad)) = []
  | bset (Eq (Add (Mult (Sub (fz, ga), fk), eo), ad)) = []
  | bset (Eq (Add (Mult (Mult (gb, gc), fk), eo), ad)) = []
  | bset (Eq (Sub (ep, eq), ad)) = []
  | bset (Eq (Mult (er, es), ad)) = []
  | bset (Divides (ae, af)) = []
  | bset T = []
  | bset F = []
  | bset (NOT (Lt (hg, hh))) = []
  | bset (NOT (Gt (hi, hj))) = []
  | bset (NOT (Le (hk, hl))) = []
  | bset (NOT (Ge (hm, hn))) = []
  | bset (NOT (Eq (Cst ja, hp))) = []
  | bset (NOT (Eq (Var jb, hp))) = []
  | bset (NOT (Eq (Neg jc, hp))) = []
  | bset (NOT (Eq (Add (Cst js, je), hp))) = []
  | bset (NOT (Eq (Add (Var jt, je), hp))) = []
  | bset (NOT (Eq (Add (Neg ju, je), hp))) = []
  | bset (NOT (Eq (Add (Add (jv, jw), je), hp))) = []
  | bset (NOT (Eq (Add (Sub (jx, jy), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Cst kk, Cst lc), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Cst kk, Var lu), je), hp))) =
    (if (lu = 0) then (if (kk < 0) then [je] else [lin_neg je]) else [])
  | bset (NOT (Eq (Add (Mult (Cst kk, Neg le), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Cst kk, Add (lf, lg)), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Cst kk, Sub (lh, li)), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Cst kk, Mult (lj, lk)), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Var kl, ka), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Neg km, ka), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Add (kn, ko), ka), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Sub (kp, kq), ka), je), hp))) = []
  | bset (NOT (Eq (Add (Mult (Mult (kr, ks), ka), je), hp))) = []
  | bset (NOT (Eq (Sub (jf, jg), hp))) = []
  | bset (NOT (Eq (Mult (jh, ji), hp))) = []
  | bset (NOT (Divides (hq, hr))) = []
  | bset (NOT T) = []
  | bset (NOT F) = []
  | bset (NOT (NOT hs)) = []
  | bset (NOT (And (ht, hu))) = []
  | bset (NOT (Or (hv, hw))) = []
  | bset (NOT (Imp (hx, hy))) = []
  | bset (NOT (Equ (hz, ia))) = []
  | bset (NOT (QAll ib)) = []
  | bset (NOT (QEx ic)) = []
  | bset (Imp (al, am)) = []
  | bset (Equ (an, ao)) = []
  | bset (QAll ap) = []
  | bset (QEx aq) = [];

fun adjustcoeff (l, Le (Add (Mult (Cst c, Var 0), r), Cst i)) =
    (if (c <= 0)
      then Le (Add (Mult (Cst ~1, Var 0), lin_mul (~ (op_div_def1 l c), r)),
                Cst 0)
      else Le (Add (Mult (Cst 1, Var 0), lin_mul (op_div_def1 l c, r)), Cst 0))
  | adjustcoeff (l, Eq (Add (Mult (Cst c, Var 0), r), Cst i)) =
    Eq (Add (Mult (Cst 1, Var 0), lin_mul (op_div_def1 l c, r)), Cst 0)
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst c, Var 0), r), Cst i))) =
    NOT (Eq (Add (Mult (Cst 1, Var 0), lin_mul (op_div_def1 l c, r)), Cst 0))
  | adjustcoeff (l, And (p, q)) = And (adjustcoeff (l, p), adjustcoeff (l, q))
  | adjustcoeff (l, Or (p, q)) = Or (adjustcoeff (l, p), adjustcoeff (l, q))
  | adjustcoeff (l, Lt (w, x)) = Lt (w, x)
  | adjustcoeff (l, Gt (y, z)) = Gt (y, z)
  | adjustcoeff (l, Le (Cst bq, ab)) = Le (Cst bq, ab)
  | adjustcoeff (l, Le (Var br, ab)) = Le (Var br, ab)
  | adjustcoeff (l, Le (Neg bs, ab)) = Le (Neg bs, ab)
  | adjustcoeff (l, Le (Add (Cst ci, bu), ab)) = Le (Add (Cst ci, bu), ab)
  | adjustcoeff (l, Le (Add (Var cj, bu), ab)) = Le (Add (Var cj, bu), ab)
  | adjustcoeff (l, Le (Add (Neg ck, bu), ab)) = Le (Add (Neg ck, bu), ab)
  | adjustcoeff (l, Le (Add (Add (cl, cm), bu), ab)) =
    Le (Add (Add (cl, cm), bu), ab)
  | adjustcoeff (l, Le (Add (Sub (cn, co), bu), ab)) =
    Le (Add (Sub (cn, co), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Cst ds), bu), ab)) =
    Le (Add (Mult (Cst da, Cst ds), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Var 0), bu), Var en)) =
    Le (Add (Mult (Cst da, Var 0), bu), Var en)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Var 0), bu), Neg eo)) =
    Le (Add (Mult (Cst da, Var 0), bu), Neg eo)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Var 0), bu), Add (ep, eq))) =
    Le (Add (Mult (Cst da, Var 0), bu), Add (ep, eq))
  | adjustcoeff (l, Le (Add (Mult (Cst da, Var 0), bu), Sub (er, es))) =
    Le (Add (Mult (Cst da, Var 0), bu), Sub (er, es))
  | adjustcoeff (l, Le (Add (Mult (Cst da, Var 0), bu), Mult (et, eu))) =
    Le (Add (Mult (Cst da, Var 0), bu), Mult (et, eu))
  | adjustcoeff (l, Le (Add (Mult (Cst da, Var ek), bu), ab)) =
    Le (Add (Mult (Cst da, Var ek), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Neg du), bu), ab)) =
    Le (Add (Mult (Cst da, Neg du), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Add (dv, dw)), bu), ab)) =
    Le (Add (Mult (Cst da, Add (dv, dw)), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Sub (dx, dy)), bu), ab)) =
    Le (Add (Mult (Cst da, Sub (dx, dy)), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Cst da, Mult (dz, ea)), bu), ab)) =
    Le (Add (Mult (Cst da, Mult (dz, ea)), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Var db, cq), bu), ab)) =
    Le (Add (Mult (Var db, cq), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Neg dc, cq), bu), ab)) =
    Le (Add (Mult (Neg dc, cq), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Add (dd, de), cq), bu), ab)) =
    Le (Add (Mult (Add (dd, de), cq), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Sub (df, dg), cq), bu), ab)) =
    Le (Add (Mult (Sub (df, dg), cq), bu), ab)
  | adjustcoeff (l, Le (Add (Mult (Mult (dh, di), cq), bu), ab)) =
    Le (Add (Mult (Mult (dh, di), cq), bu), ab)
  | adjustcoeff (l, Le (Sub (bv, bw), ab)) = Le (Sub (bv, bw), ab)
  | adjustcoeff (l, Le (Mult (bx, by), ab)) = Le (Mult (bx, by), ab)
  | adjustcoeff (l, Ge (ac, ad)) = Ge (ac, ad)
  | adjustcoeff (l, Eq (Cst fe, af)) = Eq (Cst fe, af)
  | adjustcoeff (l, Eq (Var ff, af)) = Eq (Var ff, af)
  | adjustcoeff (l, Eq (Neg fg, af)) = Eq (Neg fg, af)
  | adjustcoeff (l, Eq (Add (Cst fw, fi), af)) = Eq (Add (Cst fw, fi), af)
  | adjustcoeff (l, Eq (Add (Var fx, fi), af)) = Eq (Add (Var fx, fi), af)
  | adjustcoeff (l, Eq (Add (Neg fy, fi), af)) = Eq (Add (Neg fy, fi), af)
  | adjustcoeff (l, Eq (Add (Add (fz, ga), fi), af)) =
    Eq (Add (Add (fz, ga), fi), af)
  | adjustcoeff (l, Eq (Add (Sub (gb, gc), fi), af)) =
    Eq (Add (Sub (gb, gc), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Cst hg), fi), af)) =
    Eq (Add (Mult (Cst go, Cst hg), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Var 0), fi), Var ib)) =
    Eq (Add (Mult (Cst go, Var 0), fi), Var ib)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Var 0), fi), Neg ic)) =
    Eq (Add (Mult (Cst go, Var 0), fi), Neg ic)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Var 0), fi), Add (id, ie))) =
    Eq (Add (Mult (Cst go, Var 0), fi), Add (id, ie))
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Var 0), fi), Sub (if', ig))) =
    Eq (Add (Mult (Cst go, Var 0), fi), Sub (if', ig))
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Var 0), fi), Mult (ih, ii))) =
    Eq (Add (Mult (Cst go, Var 0), fi), Mult (ih, ii))
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Var hy), fi), af)) =
    Eq (Add (Mult (Cst go, Var hy), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Neg hi), fi), af)) =
    Eq (Add (Mult (Cst go, Neg hi), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Add (hj, hk)), fi), af)) =
    Eq (Add (Mult (Cst go, Add (hj, hk)), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Sub (hl, hm)), fi), af)) =
    Eq (Add (Mult (Cst go, Sub (hl, hm)), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Cst go, Mult (hn, ho)), fi), af)) =
    Eq (Add (Mult (Cst go, Mult (hn, ho)), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Var gp, ge), fi), af)) =
    Eq (Add (Mult (Var gp, ge), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Neg gq, ge), fi), af)) =
    Eq (Add (Mult (Neg gq, ge), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Add (gr, gs), ge), fi), af)) =
    Eq (Add (Mult (Add (gr, gs), ge), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Sub (gt, gu), ge), fi), af)) =
    Eq (Add (Mult (Sub (gt, gu), ge), fi), af)
  | adjustcoeff (l, Eq (Add (Mult (Mult (gv, gw), ge), fi), af)) =
    Eq (Add (Mult (Mult (gv, gw), ge), fi), af)
  | adjustcoeff (l, Eq (Sub (fj, fk), af)) = Eq (Sub (fj, fk), af)
  | adjustcoeff (l, Eq (Mult (fl, fm), af)) = Eq (Mult (fl, fm), af)
  | adjustcoeff (l, Divides (Cst is, Cst jk)) = Divides (Cst is, Cst jk)
  | adjustcoeff (l, Divides (Cst is, Var jl)) = Divides (Cst is, Var jl)
  | adjustcoeff (l, Divides (Cst is, Neg jm)) = Divides (Cst is, Neg jm)
  | adjustcoeff (l, Divides (Cst is, Add (Cst kc, jo))) =
    Divides (Cst is, Add (Cst kc, jo))
  | adjustcoeff (l, Divides (Cst is, Add (Var kd, jo))) =
    Divides (Cst is, Add (Var kd, jo))
  | adjustcoeff (l, Divides (Cst is, Add (Neg ke, jo))) =
    Divides (Cst is, Add (Neg ke, jo))
  | adjustcoeff (l, Divides (Cst is, Add (Add (kf, kg), jo))) =
    Divides (Cst is, Add (Add (kf, kg), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Sub (kh, ki), jo))) =
    Divides (Cst is, Add (Sub (kh, ki), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Cst ku, Cst lm), jo))) =
    Divides (Cst is, Add (Mult (Cst ku, Cst lm), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Cst ku, Var me), jo))) =
    (if (me = 0)
      then Divides
             (Cst (op_div_def1 l ku * is),
               Add (Mult (Cst 1, Var 0), lin_mul (op_div_def1 l ku, jo)))
      else Divides
             (Cst is,
               Add (Mult (Cst ku, Var (op_45_def0 me id_1_def0 + 1)), jo)))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Cst ku, Neg lo), jo))) =
    Divides (Cst is, Add (Mult (Cst ku, Neg lo), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Cst ku, Add (lp, lq)), jo))) =
    Divides (Cst is, Add (Mult (Cst ku, Add (lp, lq)), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Cst ku, Sub (lr, ls)), jo))) =
    Divides (Cst is, Add (Mult (Cst ku, Sub (lr, ls)), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Cst ku, Mult (lt, lu)), jo))) =
    Divides (Cst is, Add (Mult (Cst ku, Mult (lt, lu)), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Var kv, kk), jo))) =
    Divides (Cst is, Add (Mult (Var kv, kk), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Neg kw, kk), jo))) =
    Divides (Cst is, Add (Mult (Neg kw, kk), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Add (kx, ky), kk), jo))) =
    Divides (Cst is, Add (Mult (Add (kx, ky), kk), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Sub (kz, la), kk), jo))) =
    Divides (Cst is, Add (Mult (Sub (kz, la), kk), jo))
  | adjustcoeff (l, Divides (Cst is, Add (Mult (Mult (lb, lc), kk), jo))) =
    Divides (Cst is, Add (Mult (Mult (lb, lc), kk), jo))
  | adjustcoeff (l, Divides (Cst is, Sub (jp, jq))) =
    Divides (Cst is, Sub (jp, jq))
  | adjustcoeff (l, Divides (Cst is, Mult (jr, js))) =
    Divides (Cst is, Mult (jr, js))
  | adjustcoeff (l, Divides (Var it, ah)) = Divides (Var it, ah)
  | adjustcoeff (l, Divides (Neg iu, ah)) = Divides (Neg iu, ah)
  | adjustcoeff (l, Divides (Add (iv, iw), ah)) = Divides (Add (iv, iw), ah)
  | adjustcoeff (l, Divides (Sub (ix, iy), ah)) = Divides (Sub (ix, iy), ah)
  | adjustcoeff (l, Divides (Mult (iz, ja), ah)) = Divides (Mult (iz, ja), ah)
  | adjustcoeff (l, T) = T
  | adjustcoeff (l, F) = F
  | adjustcoeff (l, NOT (Lt (mg, mh))) = NOT (Lt (mg, mh))
  | adjustcoeff (l, NOT (Gt (mi, mj))) = NOT (Gt (mi, mj))
  | adjustcoeff (l, NOT (Le (mk, ml))) = NOT (Le (mk, ml))
  | adjustcoeff (l, NOT (Ge (mm, mn))) = NOT (Ge (mm, mn))
  | adjustcoeff (l, NOT (Eq (Cst oa, mp))) = NOT (Eq (Cst oa, mp))
  | adjustcoeff (l, NOT (Eq (Var ob, mp))) = NOT (Eq (Var ob, mp))
  | adjustcoeff (l, NOT (Eq (Neg oc, mp))) = NOT (Eq (Neg oc, mp))
  | adjustcoeff (l, NOT (Eq (Add (Cst os, oe), mp))) =
    NOT (Eq (Add (Cst os, oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Var ot, oe), mp))) =
    NOT (Eq (Add (Var ot, oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Neg ou, oe), mp))) =
    NOT (Eq (Add (Neg ou, oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Add (ov, ow), oe), mp))) =
    NOT (Eq (Add (Add (ov, ow), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Sub (ox, oy), oe), mp))) =
    NOT (Eq (Add (Sub (ox, oy), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Cst qc), oe), mp))) =
    NOT (Eq (Add (Mult (Cst pk, Cst qc), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Var qx))) =
    NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Var qx))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Neg qy))) =
    NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Neg qy))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Add (qz, ra)))) =
    NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Add (qz, ra)))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Sub (rb, rc)))) =
    NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Sub (rb, rc)))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Mult (rd, re)))) =
    NOT (Eq (Add (Mult (Cst pk, Var 0), oe), Mult (rd, re)))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Var qu), oe), mp))) =
    NOT (Eq (Add (Mult (Cst pk, Var qu), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Neg qe), oe), mp))) =
    NOT (Eq (Add (Mult (Cst pk, Neg qe), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Add (qf, qg)), oe), mp))) =
    NOT (Eq (Add (Mult (Cst pk, Add (qf, qg)), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Sub (qh, qi)), oe), mp))) =
    NOT (Eq (Add (Mult (Cst pk, Sub (qh, qi)), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Cst pk, Mult (qj, qk)), oe), mp))) =
    NOT (Eq (Add (Mult (Cst pk, Mult (qj, qk)), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Var pl, pa), oe), mp))) =
    NOT (Eq (Add (Mult (Var pl, pa), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Neg pm, pa), oe), mp))) =
    NOT (Eq (Add (Mult (Neg pm, pa), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Add (pn, po), pa), oe), mp))) =
    NOT (Eq (Add (Mult (Add (pn, po), pa), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Sub (pp, pq), pa), oe), mp))) =
    NOT (Eq (Add (Mult (Sub (pp, pq), pa), oe), mp))
  | adjustcoeff (l, NOT (Eq (Add (Mult (Mult (pr, ps), pa), oe), mp))) =
    NOT (Eq (Add (Mult (Mult (pr, ps), pa), oe), mp))
  | adjustcoeff (l, NOT (Eq (Sub (of', og), mp))) = NOT (Eq (Sub (of', og), mp))
  | adjustcoeff (l, NOT (Eq (Mult (oh, oi), mp))) = NOT (Eq (Mult (oh, oi), mp))
  | adjustcoeff (l, NOT (Divides (Cst ro, Cst sg))) =
    NOT (Divides (Cst ro, Cst sg))
  | adjustcoeff (l, NOT (Divides (Cst ro, Var sh))) =
    NOT (Divides (Cst ro, Var sh))
  | adjustcoeff (l, NOT (Divides (Cst ro, Neg si))) =
    NOT (Divides (Cst ro, Neg si))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Cst sy, sk)))) =
    NOT (Divides (Cst ro, Add (Cst sy, sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Var sz, sk)))) =
    NOT (Divides (Cst ro, Add (Var sz, sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Neg ta, sk)))) =
    NOT (Divides (Cst ro, Add (Neg ta, sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Add (tb, tc), sk)))) =
    NOT (Divides (Cst ro, Add (Add (tb, tc), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Sub (td, te), sk)))) =
    NOT (Divides (Cst ro, Add (Sub (td, te), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Cst tq, Cst ui), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Cst tq, Cst ui), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Cst tq, Var va), sk)))) =
    (if (va = 0)
      then NOT (Divides
                  (Cst (op_div_def1 l tq * ro),
                    Add (Mult (Cst 1, Var 0), lin_mul (op_div_def1 l tq, sk))))
      else NOT (Divides
                  (Cst ro,
                    Add (Mult (Cst tq, Var (op_45_def0 va id_1_def0 + 1)),
                          sk))))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Cst tq, Neg uk), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Cst tq, Neg uk), sk)))
  | adjustcoeff
      (l, NOT (Divides (Cst ro, Add (Mult (Cst tq, Add (ul, um)), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Cst tq, Add (ul, um)), sk)))
  | adjustcoeff
      (l, NOT (Divides (Cst ro, Add (Mult (Cst tq, Sub (un, uo)), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Cst tq, Sub (un, uo)), sk)))
  | adjustcoeff
      (l, NOT (Divides (Cst ro, Add (Mult (Cst tq, Mult (up, uq)), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Cst tq, Mult (up, uq)), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Var tr, tg), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Var tr, tg), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Neg ts, tg), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Neg ts, tg), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Add (tt, tu), tg), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Add (tt, tu), tg), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Add (Mult (Sub (tv, tw), tg), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Sub (tv, tw), tg), sk)))
  | adjustcoeff
      (l, NOT (Divides (Cst ro, Add (Mult (Mult (tx, ty), tg), sk)))) =
    NOT (Divides (Cst ro, Add (Mult (Mult (tx, ty), tg), sk)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Sub (sl, sm)))) =
    NOT (Divides (Cst ro, Sub (sl, sm)))
  | adjustcoeff (l, NOT (Divides (Cst ro, Mult (sn, so)))) =
    NOT (Divides (Cst ro, Mult (sn, so)))
  | adjustcoeff (l, NOT (Divides (Var rp, mr))) = NOT (Divides (Var rp, mr))
  | adjustcoeff (l, NOT (Divides (Neg rq, mr))) = NOT (Divides (Neg rq, mr))
  | adjustcoeff (l, NOT (Divides (Add (rr, rs), mr))) =
    NOT (Divides (Add (rr, rs), mr))
  | adjustcoeff (l, NOT (Divides (Sub (rt, ru), mr))) =
    NOT (Divides (Sub (rt, ru), mr))
  | adjustcoeff (l, NOT (Divides (Mult (rv, rw), mr))) =
    NOT (Divides (Mult (rv, rw), mr))
  | adjustcoeff (l, NOT T) = NOT T
  | adjustcoeff (l, NOT F) = NOT F
  | adjustcoeff (l, NOT (NOT ms)) = NOT (NOT ms)
  | adjustcoeff (l, NOT (And (mt, mu))) = NOT (And (mt, mu))
  | adjustcoeff (l, NOT (Or (mv, mw))) = NOT (Or (mv, mw))
  | adjustcoeff (l, NOT (Imp (mx, my))) = NOT (Imp (mx, my))
  | adjustcoeff (l, NOT (Equ (mz, na))) = NOT (Equ (mz, na))
  | adjustcoeff (l, NOT (QAll nb)) = NOT (QAll nb)
  | adjustcoeff (l, NOT (QEx nc)) = NOT (QEx nc)
  | adjustcoeff (l, Imp (an, ao)) = Imp (an, ao)
  | adjustcoeff (l, Equ (ap, aq)) = Equ (ap, aq)
  | adjustcoeff (l, QAll ar) = QAll ar
  | adjustcoeff (l, QEx as') = QEx as';

fun formlcm (Le (Add (Mult (Cst c, Var 0), r), Cst i)) = abs c
  | formlcm (Eq (Add (Mult (Cst c, Var 0), r), Cst i)) = abs c
  | formlcm (NOT p) = formlcm p
  | formlcm (And (p, q)) = ilcm (formlcm p) (formlcm q)
  | formlcm (Or (p, q)) = ilcm (formlcm p) (formlcm q)
  | formlcm (Lt (u, v)) = 1
  | formlcm (Gt (w, x)) = 1
  | formlcm (Le (Cst bo, z)) = 1
  | formlcm (Le (Var bp, z)) = 1
  | formlcm (Le (Neg bq, z)) = 1
  | formlcm (Le (Add (Cst cg, bs), z)) = 1
  | formlcm (Le (Add (Var ch, bs), z)) = 1
  | formlcm (Le (Add (Neg ci, bs), z)) = 1
  | formlcm (Le (Add (Add (cj, ck), bs), z)) = 1
  | formlcm (Le (Add (Sub (cl, cm), bs), z)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Cst dq), bs), z)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Var 0), bs), Var el)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Var 0), bs), Neg em)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Var 0), bs), Add (en, eo))) = 1
  | formlcm (Le (Add (Mult (Cst cy, Var 0), bs), Sub (ep, eq))) = 1
  | formlcm (Le (Add (Mult (Cst cy, Var 0), bs), Mult (er, es))) = 1
  | formlcm (Le (Add (Mult (Cst cy, Var ei ), bs), z)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Neg ds), bs), z)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Add (dt, du)), bs), z)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Sub (dv, dw)), bs), z)) = 1
  | formlcm (Le (Add (Mult (Cst cy, Mult (dx, dy)), bs), z)) = 1
  | formlcm (Le (Add (Mult (Var cz, co), bs), z)) = 1
  | formlcm (Le (Add (Mult (Neg da, co), bs), z)) = 1
  | formlcm (Le (Add (Mult (Add (db, dc), co), bs), z)) = 1
  | formlcm (Le (Add (Mult (Sub (dd, de), co), bs), z)) = 1
  | formlcm (Le (Add (Mult (Mult (df, dg), co), bs), z)) = 1
  | formlcm (Le (Sub (bt, bu), z)) = 1
  | formlcm (Le (Mult (bv, bw), z)) = 1
  | formlcm (Ge (aa, ab)) = 1
  | formlcm (Eq (Cst fc, ad)) = 1
  | formlcm (Eq (Var fd, ad)) = 1
  | formlcm (Eq (Neg fe, ad)) = 1
  | formlcm (Eq (Add (Cst fu, fg), ad)) = 1
  | formlcm (Eq (Add (Var fv, fg), ad)) = 1
  | formlcm (Eq (Add (Neg fw, fg), ad)) = 1
  | formlcm (Eq (Add (Add (fx, fy), fg), ad)) = 1
  | formlcm (Eq (Add (Sub (fz, ga), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Cst he), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Var 0), fg), Var hz)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Var 0), fg), Neg ia)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Var 0), fg), Add (ib, ic))) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Var 0), fg), Sub (id, ie))) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Var 0), fg), Mult (if', ig))) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Var hw), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Neg hg), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Add (hh, hi)), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Sub (hj, hk)), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Cst gm, Mult (hl, hm)), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Var gn, gc), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Neg go, gc), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Add (gp, gq), gc), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Sub (gr, gs), gc), fg), ad)) = 1
  | formlcm (Eq (Add (Mult (Mult (gt, gu), gc), fg), ad)) = 1
  | formlcm (Eq (Sub (fh, fi), ad)) = 1
  | formlcm (Eq (Mult (fj, fk), ad)) = 1
  | formlcm (Divides (Cst iq, Cst ji)) = 1
  | formlcm (Divides (Cst iq, Var jj)) = 1
  | formlcm (Divides (Cst iq, Neg jk)) = 1
  | formlcm (Divides (Cst iq, Add (Cst ka, jm))) = 1
  | formlcm (Divides (Cst iq, Add (Var kb, jm))) = 1
  | formlcm (Divides (Cst iq, Add (Neg kc, jm))) = 1
  | formlcm (Divides (Cst iq, Add (Add (kd, ke), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Sub (kf, kg), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Cst ks, Cst lk), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Cst ks, Var mc), jm))) =
    (if (mc = 0) then abs ks else 1)
  | formlcm (Divides (Cst iq, Add (Mult (Cst ks, Neg lm), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Cst ks, Add (ln, lo)), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Cst ks, Sub (lp, lq)), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Cst ks, Mult (lr, ls)), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Var kt, ki), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Neg ku, ki), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Add (kv, kw), ki), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Sub (kx, ky), ki), jm))) = 1
  | formlcm (Divides (Cst iq, Add (Mult (Mult (kz, la), ki), jm))) = 1
  | formlcm (Divides (Cst iq, Sub (jn, jo))) = 1
  | formlcm (Divides (Cst iq, Mult (jp, jq))) = 1
  | formlcm (Divides (Var ir, af)) = 1
  | formlcm (Divides (Neg is, af)) = 1
  | formlcm (Divides (Add (it, iu), af)) = 1
  | formlcm (Divides (Sub (iv, iw), af)) = 1
  | formlcm (Divides (Mult (ix, iy), af)) = 1
  | formlcm T = 1
  | formlcm F = 1
  | formlcm (Imp (al, am)) = 1
  | formlcm (Equ (an, ao)) = 1
  | formlcm (QAll ap) = 1
  | formlcm (QEx aq) = 1;

fun unitycoeff p =
  let val l = formlcm p; val p' = adjustcoeff (l, p)
  in (if (l = 1) then p'
       else And (Divides (Cst l, Add (Mult (Cst 1, Var 0), Cst 0)), p'))
  end;

fun unify p =
  let val q = unitycoeff p; val B = list_set (bset q); val A = list_set (aset q)
  in (if op_60_61_def0 (size_def1 B) (size_def1 A) then (q, B)
       else (mirror q, map lin_neg A))
  end;

fun cooper p =
  lift_un (fn q => decrvars (explode_minf (unify q))) (linform (nnf p));

fun pa p = lift_un psimpl (qelim (cooper, p));

val test = pa;

end;
