(*  Title:      HOL/Tools/Nitpick/nitpick_tests.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Unit tests for Nitpick.
*)

signature NITPICK_TESTS =
sig
  val run_all_tests : unit -> unit
end;

structure Nitpick_Tests : NITPICK_TESTS =
struct

open Nitpick_Util
open Nitpick_Peephole
open Nitpick_Rep
open Nitpick_Nut
open Nitpick_Kodkod

val settings = [("solver", "\"DefaultSAT4J\"")]

fun cast_to_rep R u = Op1 (Cast, type_of u, R, u)

val dummy_T = \<^typ>\<open>'a\<close>

val atom1_v1 = FreeName ("atom1_v1", dummy_T, Atom (1, 0))
val atom2_v1 = FreeName ("atom2_v1", dummy_T, Atom (2, 0))
val atom6_v1 = FreeName ("atom6_v1", dummy_T, Atom (6, 0))
val atom16_v1 = FreeName ("atom16_v1", dummy_T, Atom (16, 0))
val atom24_v1 = FreeName ("atom24_v1", dummy_T, Atom (24, 0))
val atom36_v1 = FreeName ("atom36_v1", dummy_T, Atom (36, 0))
val struct_atom1_atom1_v1 =
  FreeName ("struct_atom1_atom1_v1", dummy_T, Struct [Atom (1, 0), Atom (1, 0)])

(*
              Formula    Atom    Struct    Vect    Func
    Formula      X       X        X       N/A     N/A
    Atom         X       X        X        X       X
    Struct      N/A      X        X       N/A     N/A
    Vect        N/A      X       N/A       X       X
    Func        N/A      X       N/A       X       X
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
   ("rep_conversion_atom_formula_atom",
    Op2 (Eq, bool_T, Formula Neut,
         cast_to_rep (Atom (2, 0)) (cast_to_rep (Formula Neut) atom2_v1),
         atom2_v1)),
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
                      struct_atom1_atom1_v1))]

fun problem_for_nut ctxt (name, u) =
  let
    val debug = false
    val peephole_optim = true
    val nat_card = 4
    val int_card = 9
    val j0 = 0
    val constrs = kodkod_constrs peephole_optim nat_card int_card j0
    val (free_rels, pool, table) =
      rename_free_vars (fst (add_free_and_const_names u ([], []))) initial_pool
                       NameTable.empty
    val u = Op1 (Not, type_of u, rep_of u, u)
            |> rename_vars_in_nut pool table
    val formula = kodkod_formula_from_nut Typtab.empty constrs u
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

fun run_all_tests () =
  let
    val {debug, overlord, timeout, ...} = Nitpick_Commands.default_params \<^theory> []
    val deadline = Timeout.end_time timeout
    val max_threads = 1
    val max_solutions = 1
  in
    case Kodkod.solve_any_problem debug overlord deadline max_threads max_solutions
                                  (map (problem_for_nut \<^context>) tests) of
      Kodkod.Normal ([], _, _) => ()
    | _ => error "Tests failed"
  end

end;
