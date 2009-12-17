(*  Title:      HOL/Tools/Nitpick/nitpick_tests.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Unit tests for Nitpick.
*)

signature NITPICK_TESTS =
sig
  val run_all_tests : unit -> unit
end

structure Nitpick_Tests =
struct

open Nitpick_Util
open Nitpick_Peephole
open Nitpick_Rep
open Nitpick_Nut
open Nitpick_Kodkod

val settings =
  [("solver", "\"zChaff\""),
   ("skolem_depth", "-1")]

fun cast_to_rep R u = Op1 (Cast, type_of u, R, u)

val unit_T = @{typ unit}
val dummy_T = @{typ 'a}

val unity = Cst (Unity, unit_T, Unit)
val atom1_v1 = FreeName ("atom1_v1", dummy_T, Atom (1, 0))
val atom2_v1 = FreeName ("atom2_v1", dummy_T, Atom (2, 0))
val atom6_v1 = FreeName ("atom6_v1", dummy_T, Atom (6, 0))
val atom16_v1 = FreeName ("atom16_v1", dummy_T, Atom (16, 0))
val atom24_v1 = FreeName ("atom24_v1", dummy_T, Atom (24, 0))
val atom36_v1 = FreeName ("atom36_v1", dummy_T, Atom (36, 0))
val atom81_v1 = FreeName ("atom81_v1", dummy_T, Atom (81, 0))
val struct_atom1_atom1_v1 =
  FreeName ("struct_atom1_atom1_v1", dummy_T, Struct [Atom (1, 0), Atom (1, 0)])
val struct_atom1_unit_v1 =
  FreeName ("struct_atom1_atom1_v1", dummy_T, Struct [Atom (1, 0), Unit])
val struct_unit_atom1_v1 =
  FreeName ("struct_atom1_atom1_v1", dummy_T, Struct [Unit, Atom (1, 0)])

(*
              Formula    Unit   Atom    Struct    Vect    Func
    Formula      X       N/A     X        X       N/A     N/A
    Unit        N/A      N/A    N/A      N/A      N/A     N/A
    Atom         X       N/A     X        X        X       X
    Struct      N/A      N/A     X        X       N/A     N/A
    Vect        N/A      N/A     X       N/A       X       X
    Func        N/A      N/A     X       N/A       X       X
*)

val tests =
  [("rep_conversion_formula_formula",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Formula Neut)
                     (cast_to_rep (Formula Neut) atom2_v1), atom2_v1)),
   ("rep_conversion_atom_atom",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0)) (cast_to_rep (Atom (16, 0)) atom16_v1),
         atom16_v1)),
   ("rep_conversion_struct_struct_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (4, 0), Atom (6, 0)])
             (cast_to_rep (Struct [Atom (4, 0), Atom (6, 0)]) atom24_v1),
         atom24_v1)),
   ("rep_conversion_struct_struct_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (4, 0), Struct [Atom (2, 0), Atom (3, 0)]])
             (cast_to_rep (Struct [Atom (4, 0), Atom (6, 0)]) atom24_v1),
         atom24_v1)),
   ("rep_conversion_struct_struct_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (4, 0), Atom (6, 0)])
             (cast_to_rep (Struct [Atom (4, 0),
                                   Struct [Atom (2, 0), Atom (3, 0)]])
                          atom24_v1),
         atom24_v1)),
   ("rep_conversion_struct_struct_4",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (24, 0), Unit])
             (cast_to_rep (Struct [Atom (24, 0), Atom (1, 0)]) atom24_v1),
         atom24_v1)),
   ("rep_conversion_struct_struct_5",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (24, 0), Atom (1, 0)])
             (cast_to_rep (Struct [Atom (24, 0), Unit]) atom24_v1),
         atom24_v1)),
   ("rep_conversion_struct_struct_6",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (1, 0), Atom (1, 0)])
             (cast_to_rep (Struct [Atom (1, 0), Unit])
                 (cast_to_rep (Struct [Unit, Atom (1, 0)]) atom1_v1)),
         atom1_v1)),
   ("rep_conversion_vect_vect_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (2, Atom (4, 0)))
                  (cast_to_rep (Vect (2, Struct [Atom (2, 0), Atom (2, 0)]))
                               atom16_v1)),
         atom16_v1)),
   ("rep_conversion_vect_vect_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (2, Struct [Atom (2, 0), Atom (2, 0)]))
                  (cast_to_rep (Vect (2, Atom (4, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_vect_vect_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (2, Atom (4, 0)))
                  (cast_to_rep (Vect (2, Vect (2, Atom (2, 0)))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_vect_vect_4",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (2, Vect (2, Atom (2, 0))))
                  (cast_to_rep (Vect (2, Atom (4, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_func_func_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Atom (2, 0),
                                 Struct [Atom (2, 0), Atom (3, 0)]))
                  (cast_to_rep (Func (Atom (2, 0), Atom (6, 0))) atom36_v1)),
         atom36_v1)),
   ("rep_conversion_func_func_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Atom (2, 0), Atom (6, 0)))
                  (cast_to_rep (Func (Atom (2, 0),
                                Struct [Atom (2, 0), Atom (3, 0)]))
                       atom36_v1)),
         atom36_v1)),
   ("rep_conversion_func_func_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Unit, Struct [Atom (6, 0), Atom (6, 0)]))
                  (cast_to_rep (Func (Atom (1, 0), Atom (36, 0))) atom36_v1)),
         atom36_v1)),
   ("rep_conversion_func_func_4",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Atom (1, 0), Atom (36, 0)))
                  (cast_to_rep (Func (Unit, Struct [Atom (6, 0), Atom (6, 0)]))
                       atom36_v1)),
         atom36_v1)),
   ("rep_conversion_func_func_5",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Unit, Vect (2, Atom (6, 0))))
                  (cast_to_rep (Func (Atom (1, 0), Atom (36, 0))) atom36_v1)),
         atom36_v1)),
   ("rep_conversion_func_func_6",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Atom (1, 0), Atom (36, 0)))
                  (cast_to_rep (Func (Unit, Vect (2, Atom (6, 0))))
                       atom36_v1)),
         atom36_v1)),
   ("rep_conversion_func_func_7",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (2, 0))
             (cast_to_rep (Func (Unit, Atom (2, 0)))
                  (cast_to_rep (Func (Atom (1, 0), Formula Neut)) atom2_v1)),
         atom2_v1)),
   ("rep_conversion_func_func_8",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (2, 0))
             (cast_to_rep (Func (Atom (1, 0), Formula Neut))
                  (cast_to_rep (Func (Unit, Atom (2, 0))) atom2_v1)),
         atom2_v1)),
   ("rep_conversion_atom_formula_atom",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (2, 0)) (cast_to_rep (Formula Neut) atom2_v1),
         atom2_v1)),
   ("rep_conversion_unit_atom",
    Op2 (Eq, bool_T, Formula Neut, cast_to_rep (Atom (1, 0)) unity, unity)),
   ("rep_conversion_atom_struct_atom1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (6, 0))
                     (cast_to_rep (Struct [Atom (3, 0), Atom (2, 0)]) atom6_v1),
         atom6_v1)),
   ("rep_conversion_atom_struct_atom_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (24, 0))
             (cast_to_rep (Struct [Struct [Atom (3, 0), Atom (4, 0)],
                                   Atom (2, 0)]) atom24_v1),
         atom24_v1)),
   ("rep_conversion_atom_struct_atom_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (6, 0))
                     (cast_to_rep (Struct [Atom (6, 0), Unit]) atom6_v1),
         atom6_v1)),
   ("rep_conversion_atom_struct_atom_4",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (6, 0))
             (cast_to_rep (Struct [Struct [Atom (3, 0), Unit], Atom (2, 0)]) 
             atom6_v1),
         atom6_v1)),
   ("rep_conversion_atom_vect_func_atom_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (4, Atom (2, 0)))
                  (cast_to_rep (Func (Atom (4, 0), Atom (2, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_vect_func_atom_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (4, Atom (2, 0)))
                  (cast_to_rep (Func (Atom (4, 0), Atom (2, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_vect_func_atom_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (4, Atom (2, 0)))
                  (cast_to_rep (Func (Atom (4, 0), Formula Neut)) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_vect_func_atom_4",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (1, Atom (16, 0)))
                  (cast_to_rep (Func (Unit, Atom (16, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_vect_func_atom_5",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Vect (1, Atom (16, 0)))
                  (cast_to_rep (Func (Unit, Atom (16, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_func_vect_atom_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Func (Atom (4, 0), Atom (2, 0)))
                  (cast_to_rep (Vect (4, Atom (2, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_func_vect_atom_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Func (Atom (4, 0), Atom (2, 0)))
                  (cast_to_rep (Vect (4, Atom (2, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_func_vect_atom_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Func (Atom (4, 0), Formula Neut))
                  (cast_to_rep (Vect (4, Atom (2, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_func_vect_atom_4",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Func (Unit, Atom (16, 0)))
                  (cast_to_rep (Vect (1, Atom (16, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_func_vect_atom_5",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (16, 0))
             (cast_to_rep (Func (Atom (1, 0), Atom (16, 0)))
                  (cast_to_rep (Vect (1, Atom (16, 0))) atom16_v1)),
         atom16_v1)),
   ("rep_conversion_atom_vect_atom",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Vect (2, Struct [Atom (2, 0), Atom (3, 0)]))
                          atom36_v1),
         atom36_v1)),
   ("rep_conversion_atom_func_atom",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (36, 0))
             (cast_to_rep (Func (Atom (2, 0),
                           Struct [Atom (2, 0), Atom (3, 0)])) atom36_v1),
         atom36_v1)),
   ("rep_conversion_struct_atom1_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (1, 0), Atom (1, 0)]) atom1_v1,
                      struct_atom1_atom1_v1)),
   ("rep_conversion_struct_atom1_2",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (1, 0), Unit]) atom1_v1,
                      struct_atom1_unit_v1)),
   ("rep_conversion_struct_atom1_3",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Unit, Atom (1, 0)]) atom1_v1,
                      struct_unit_atom1_v1))
(*
   ("rep_conversion_struct_formula_struct_1",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Struct [Atom (2, 0), Unit])
             (cast_to_rep (Formula Neut) struct_atom_2_unit_v1),
         struct_atom_2_unit_v1))
*)
  ]

fun problem_for_nut ctxt name u =
  let
    val debug = false
    val peephole_optim = true
    val nat_card = 4
    val int_card = 9
    val bits = 8
    val j0 = 0
    val constrs = kodkod_constrs peephole_optim nat_card int_card j0
    val (free_rels, pool, table) =
      rename_free_vars (fst (add_free_and_const_names u ([], []))) initial_pool
                       NameTable.empty
    val u = Op1 (Not, type_of u, rep_of u, u)
            |> rename_vars_in_nut pool table
    val formula = kodkod_formula_from_nut bits Typtab.empty false constrs u
    val bounds = map (bound_for_plain_rel ctxt debug) free_rels
    val univ_card = univ_card nat_card int_card j0 bounds formula
    val declarative_axioms = map (declarative_axiom_for_plain_rel constrs)
                                 free_rels
    val formula = fold_rev s_and declarative_axioms formula
  in
    {comment = name, settings = settings, univ_card = univ_card,
     tuple_assigns = [], bounds = bounds, int_bounds = [], expr_assigns = [],
     formula = formula}
  end

(* string -> unit *)
fun run_test name =
  case Kodkod.solve_any_problem true NONE 0 1
           [problem_for_nut @{context} name
                            (the (AList.lookup (op =) tests name))] of
    Kodkod.Normal ([], _) => ()
  | _ => warning ("Test " ^ quote name ^ " failed")

(* unit -> unit *)
fun run_all_tests () = List.app run_test (map fst tests)

end;
