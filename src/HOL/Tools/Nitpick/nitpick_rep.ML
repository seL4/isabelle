(*  Title:      HOL/Tools/Nitpick/nitpick_rep.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Kodkod representations of Nitpick terms.
*)

signature NITPICK_REP =
sig
  type polarity = Nitpick_Util.polarity
  type scope = Nitpick_Scope.scope

  datatype rep =
    Any |
    Formula of polarity |
    Unit |
    Atom of int * int |
    Struct of rep list |
    Vect of int * rep |
    Func of rep * rep |
    Opt of rep

  exception REP of string * rep list

  val string_for_polarity : polarity -> string
  val string_for_rep : rep -> string
  val is_Func : rep -> bool
  val is_Opt : rep -> bool
  val is_opt_rep : rep -> bool
  val flip_rep_polarity : rep -> rep
  val card_of_rep : rep -> int
  val arity_of_rep : rep -> int
  val min_univ_card_of_rep : rep -> int
  val is_one_rep : rep -> bool
  val is_lone_rep : rep -> bool
  val dest_Func : rep -> rep * rep
  val smart_range_rep : int Typtab.table -> typ -> (unit -> int) -> rep -> rep
  val binder_reps : rep -> rep list
  val body_rep : rep -> rep
  val one_rep : int Typtab.table -> typ -> rep -> rep
  val optable_rep : int Typtab.table -> typ -> rep -> rep
  val opt_rep : int Typtab.table -> typ -> rep -> rep
  val unopt_rep : rep -> rep
  val min_rep : rep -> rep -> rep
  val min_reps : rep list -> rep list -> rep list
  val card_of_domain_from_rep : int -> rep -> int
  val rep_to_binary_rel_rep : int Typtab.table -> typ -> rep -> rep
  val best_one_rep_for_type : scope -> typ -> rep
  val best_opt_set_rep_for_type : scope -> typ -> rep
  val best_non_opt_set_rep_for_type : scope -> typ -> rep
  val best_set_rep_for_type : scope -> typ -> rep
  val best_non_opt_symmetric_reps_for_fun_type : scope -> typ -> rep * rep
  val atom_schema_of_rep : rep -> (int * int) list
  val atom_schema_of_reps : rep list -> (int * int) list
  val type_schema_of_rep : typ -> rep -> typ list
  val type_schema_of_reps : typ list -> rep list -> typ list
  val all_combinations_for_rep : rep -> int list list
  val all_combinations_for_reps : rep list -> int list list
end;

structure Nitpick_Rep : NITPICK_REP =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Scope

datatype rep =
  Any |
  Formula of polarity |
  Unit |
  Atom of int * int |
  Struct of rep list |
  Vect of int * rep |
  Func of rep * rep |
  Opt of rep

exception REP of string * rep list

(* polarity -> string *)
fun string_for_polarity Pos = "+"
  | string_for_polarity Neg = "-"
  | string_for_polarity Neut = "="

(* rep -> string *)
fun atomic_string_for_rep rep =
  let val s = string_for_rep rep in
    if String.isPrefix "[" s orelse not (is_substring_of " " s) then s
    else "(" ^ s ^ ")"
  end
(* rep -> string *)
and string_for_rep Any = "X"
  | string_for_rep (Formula polar) = "F" ^ string_for_polarity polar
  | string_for_rep Unit = "U"
  | string_for_rep (Atom (k, j0)) =
    "A" ^ string_of_int k ^ (if j0 = 0 then "" else "@" ^ string_of_int j0)
  | string_for_rep (Struct rs) = "[" ^ commas (map string_for_rep rs) ^ "]"
  | string_for_rep (Vect (k, R)) =
    string_of_int k ^ " x " ^ atomic_string_for_rep R
  | string_for_rep (Func (R1, R2)) =
    atomic_string_for_rep R1 ^ " => " ^ string_for_rep R2
  | string_for_rep (Opt R) = atomic_string_for_rep R ^ "?"

(* rep -> bool *)
fun is_Func (Func _) = true
  | is_Func _ = false
fun is_Opt (Opt _) = true
  | is_Opt _ = false
fun is_opt_rep (Func (_, R2)) = is_opt_rep R2
  | is_opt_rep (Opt _) = true
  | is_opt_rep _ = false

(* rep -> int *)
fun card_of_rep Any = raise REP ("Nitpick_Rep.card_of_rep", [Any])
  | card_of_rep (Formula _) = 2
  | card_of_rep Unit = 1
  | card_of_rep (Atom (k, _)) = k
  | card_of_rep (Struct rs) = Integer.prod (map card_of_rep rs)
  | card_of_rep (Vect (k, R)) = reasonable_power (card_of_rep R) k
  | card_of_rep (Func (R1, R2)) =
    reasonable_power (card_of_rep R2) (card_of_rep R1)
  | card_of_rep (Opt R) = card_of_rep R
fun arity_of_rep Any = raise REP ("Nitpick_Rep.arity_of_rep", [Any])
  | arity_of_rep (Formula _) = 0
  | arity_of_rep Unit = 0
  | arity_of_rep (Atom _) = 1
  | arity_of_rep (Struct Rs) = Integer.sum (map arity_of_rep Rs)
  | arity_of_rep (Vect (k, R)) = k * arity_of_rep R
  | arity_of_rep (Func (R1, R2)) = arity_of_rep R1 + arity_of_rep R2
  | arity_of_rep (Opt R) = arity_of_rep R
fun min_univ_card_of_rep Any =
    raise REP ("Nitpick_Rep.min_univ_card_of_rep", [Any])
  | min_univ_card_of_rep (Formula _) = 0
  | min_univ_card_of_rep Unit = 0
  | min_univ_card_of_rep (Atom (k, j0)) = k + j0 + 1
  | min_univ_card_of_rep (Struct Rs) =
    fold Integer.max (map min_univ_card_of_rep Rs) 0
  | min_univ_card_of_rep (Vect (_, R)) = min_univ_card_of_rep R
  | min_univ_card_of_rep (Func (R1, R2)) =
    Int.max (min_univ_card_of_rep R1, min_univ_card_of_rep R2)
  | min_univ_card_of_rep (Opt R) = min_univ_card_of_rep R

(* rep -> bool *)
fun is_one_rep Unit = true
  | is_one_rep (Atom _) = true
  | is_one_rep (Struct _) = true
  | is_one_rep (Vect _) = true
  | is_one_rep _ = false
fun is_lone_rep (Opt R) = is_one_rep R
  | is_lone_rep R = is_one_rep R

(* rep -> rep * rep *)
fun dest_Func (Func z) = z
  | dest_Func R = raise REP ("Nitpick_Rep.dest_Func", [R])
(* int Typtab.table -> typ -> (unit -> int) -> rep -> rep *)
fun smart_range_rep _ _ _ Unit = Unit
  | smart_range_rep _ _ _ (Vect (_, R)) = R
  | smart_range_rep _ _ _ (Func (_, R2)) = R2
  | smart_range_rep ofs T ran_card (Opt R) =
    Opt (smart_range_rep ofs T ran_card R)
  | smart_range_rep ofs (Type ("fun", [_, T2])) _ (Atom (1, _)) =
    Atom (1, offset_of_type ofs T2)
  | smart_range_rep ofs (Type ("fun", [_, T2])) ran_card (Atom _) =
    Atom (ran_card (), offset_of_type ofs T2)
  | smart_range_rep _ _ _ R = raise REP ("Nitpick_Rep.smart_range_rep", [R])

(* rep -> rep list *)
fun binder_reps (Func (R1, R2)) = R1 :: binder_reps R2
  | binder_reps R = []
(* rep -> rep *)
fun body_rep (Func (_, R2)) = body_rep R2
  | body_rep R = R

(* rep -> rep *)
fun flip_rep_polarity (Formula polar) = Formula (flip_polarity polar)
  | flip_rep_polarity (Func (R1, R2)) = Func (R1, flip_rep_polarity R2)
  | flip_rep_polarity R = R

(* int Typtab.table -> rep -> rep *)
fun one_rep _ _ Any = raise REP ("Nitpick_Rep.one_rep", [Any])
  | one_rep _ _ (Atom x) = Atom x
  | one_rep _ _ (Struct Rs) = Struct Rs
  | one_rep _ _ (Vect z) = Vect z
  | one_rep ofs T (Opt R) = one_rep ofs T R
  | one_rep ofs T R = Atom (card_of_rep R, offset_of_type ofs T)
fun optable_rep ofs (Type ("fun", [_, T2])) (Func (R1, R2)) =
    Func (R1, optable_rep ofs T2 R2)
  | optable_rep ofs T R = one_rep ofs T R
fun opt_rep ofs (Type ("fun", [_, T2])) (Func (R1, R2)) =
    Func (R1, opt_rep ofs T2 R2)
  | opt_rep ofs T R = Opt (optable_rep ofs T R)
(* rep -> rep *)
fun unopt_rep (Func (R1, R2)) = Func (R1, unopt_rep R2)
  | unopt_rep (Opt R) = R
  | unopt_rep R = R

(* polarity -> polarity -> polarity *)
fun min_polarity polar1 polar2 =
  if polar1 = polar2 then
    polar1
  else if polar1 = Neut then
    polar2
  else if polar2 = Neut then
    polar1
  else
    raise ARG ("Nitpick_Rep.min_polarity",
               commas (map (quote o string_for_polarity) [polar1, polar2]))

(* It's important that Func is before Vect, because if the range is Opt we
   could lose information by converting a Func to a Vect. *)
(* rep -> rep -> rep *)
fun min_rep (Opt R1) (Opt R2) = Opt (min_rep R1 R2)
  | min_rep (Opt R) _ = Opt R
  | min_rep _ (Opt R) = Opt R
  | min_rep (Formula polar1) (Formula polar2) =
    Formula (min_polarity polar1 polar2)
  | min_rep (Formula polar) _ = Formula polar
  | min_rep _ (Formula polar) = Formula polar
  | min_rep Unit _ = Unit
  | min_rep _ Unit = Unit
  | min_rep (Atom x) _ = Atom x
  | min_rep _ (Atom x) = Atom x
  | min_rep (Struct Rs1) (Struct Rs2) = Struct (min_reps Rs1 Rs2)
  | min_rep (Struct Rs) _ = Struct Rs
  | min_rep _ (Struct Rs) = Struct Rs
  | min_rep (R1 as Func (R11, R12)) (R2 as Func (R21, R22)) =
    (case pairself is_opt_rep (R12, R22) of
       (true, false) => R1
     | (false, true) => R2
     | _ => if R11 = R21 then Func (R11, min_rep R12 R22)
            else if min_rep R11 R21 = R11 then R1
            else R2)
  | min_rep (Func z) _ = Func z
  | min_rep _ (Func z) = Func z
  | min_rep (Vect (k1, R1)) (Vect (k2, R2)) =
    if k1 < k2 then Vect (k1, R1)
    else if k1 > k2 then Vect (k2, R2)
    else Vect (k1, min_rep R1 R2)
  | min_rep R1 R2 = raise REP ("Nitpick_Rep.min_rep", [R1, R2])
(* rep list -> rep list -> rep list *)
and min_reps [] _ = []
  | min_reps _ [] = []
  | min_reps (R1 :: Rs1) (R2 :: Rs2) =
    if R1 = R2 then R1 :: min_reps Rs1 Rs2
    else if min_rep R1 R2 = R1 then R1 :: Rs1
    else R2 :: Rs2

(* int -> rep -> int *)
fun card_of_domain_from_rep ran_card R =
  case R of
    Unit => 1
  | Atom (k, _) => exact_log ran_card k
  | Vect (k, _) => k
  | Func (R1, _) => card_of_rep R1
  | Opt R => card_of_domain_from_rep ran_card R
  | _ => raise REP ("Nitpick_Rep.card_of_domain_from_rep", [R])

(* int Typtab.table -> typ -> rep -> rep *)
fun rep_to_binary_rel_rep ofs T R =
  let
    val k = exact_root 2 (card_of_domain_from_rep 2 R)
    val j0 = offset_of_type ofs (fst (HOLogic.dest_prodT (domain_type T)))
  in Func (Struct [Atom (k, j0), Atom (k, j0)], Formula Neut) end

(* scope -> typ -> rep *)
fun best_one_rep_for_type (scope as {card_assigns, ...} : scope)
                          (Type ("fun", [T1, T2])) =
    (case best_one_rep_for_type scope T2 of
       Unit => Unit
     | R2 => Vect (card_of_type card_assigns T1, R2))
  | best_one_rep_for_type scope (Type ("*", [T1, T2])) =
    (case (best_one_rep_for_type scope T1, best_one_rep_for_type scope T2) of
       (Unit, Unit) => Unit
     | (R1, R2) => Struct [R1, R2])
  | best_one_rep_for_type (scope as {card_assigns, datatypes, ofs, ...}) T =
    (case card_of_type card_assigns T of
       1 => if is_some (datatype_spec datatypes T)
               orelse is_fp_iterator_type T then
              Atom (1, offset_of_type ofs T)
            else
              Unit
     | k => Atom (k, offset_of_type ofs T))

(* Datatypes are never represented by Unit, because it would confuse
   "nfa_transitions_for_ctor". *)
(* scope -> typ -> rep *)
fun best_opt_set_rep_for_type scope (Type ("fun", [T1, T2])) =
    Func (best_one_rep_for_type scope T1, best_opt_set_rep_for_type scope T2)
  | best_opt_set_rep_for_type (scope as {ofs, ...}) T =
    opt_rep ofs T (best_one_rep_for_type scope T)
fun best_non_opt_set_rep_for_type (scope as {ofs, ...})
                                  (Type ("fun", [T1, T2])) =
    (case (best_one_rep_for_type scope T1,
           best_non_opt_set_rep_for_type scope T2) of
       (_, Unit) => Unit
     | (Unit, Atom (2, _)) =>
       Func (Atom (1, offset_of_type ofs T1), Formula Neut)
     | (R1, Atom (2, _)) => Func (R1, Formula Neut)
     | z => Func z)
  | best_non_opt_set_rep_for_type scope T = best_one_rep_for_type scope T
fun best_set_rep_for_type (scope as {datatypes, ...}) T =
  (if is_exact_type datatypes T then best_non_opt_set_rep_for_type
   else best_opt_set_rep_for_type) scope T
fun best_non_opt_symmetric_reps_for_fun_type (scope as {ofs, ...})
                                             (Type ("fun", [T1, T2])) =
    (optable_rep ofs T1 (best_one_rep_for_type scope T1),
     optable_rep ofs T2 (best_one_rep_for_type scope T2))
  | best_non_opt_symmetric_reps_for_fun_type _ T =
    raise TYPE ("Nitpick_Rep.best_non_opt_symmetric_reps_for_fun_type", [T], [])

(* rep -> (int * int) list *)
fun atom_schema_of_rep Any = raise REP ("Nitpick_Rep.atom_schema_of_rep", [Any])
  | atom_schema_of_rep (Formula _) = []
  | atom_schema_of_rep Unit = []
  | atom_schema_of_rep (Atom x) = [x]
  | atom_schema_of_rep (Struct Rs) = atom_schema_of_reps Rs
  | atom_schema_of_rep (Vect (k, R)) = replicate_list k (atom_schema_of_rep R)
  | atom_schema_of_rep (Func (R1, R2)) =
    atom_schema_of_rep R1 @ atom_schema_of_rep R2
  | atom_schema_of_rep (Opt R) = atom_schema_of_rep R
(* rep list -> (int * int) list *)
and atom_schema_of_reps Rs = maps atom_schema_of_rep Rs

(* typ -> rep -> typ list *)
fun type_schema_of_rep _ (Formula _) = []
  | type_schema_of_rep _ Unit = []
  | type_schema_of_rep T (Atom _) = [T]
  | type_schema_of_rep (Type ("*", [T1, T2])) (Struct [R1, R2]) =
    type_schema_of_reps [T1, T2] [R1, R2]
  | type_schema_of_rep (Type ("fun", [_, T2])) (Vect (k, R)) =
    replicate_list k (type_schema_of_rep T2 R)
  | type_schema_of_rep (Type ("fun", [T1, T2])) (Func (R1, R2)) =
    type_schema_of_rep T1 R1 @ type_schema_of_rep T2 R2
  | type_schema_of_rep T (Opt R) = type_schema_of_rep T R
  | type_schema_of_rep T R = raise REP ("Nitpick_Rep.type_schema_of_rep", [R])
(* typ list -> rep list -> typ list *)
and type_schema_of_reps Ts Rs = flat (map2 type_schema_of_rep Ts Rs)

(* rep -> int list list *)
val all_combinations_for_rep = all_combinations o atom_schema_of_rep
(* rep list -> int list list *)
val all_combinations_for_reps = all_combinations o atom_schema_of_reps

end;
