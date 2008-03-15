(*  Title:      FOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner.
*)

section "Classical Reasoner";

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val mp        = @{thm mp}
  val not_elim  = @{thm notE}
  val classical = @{thm classical}
  val sizef     = size_of_thm
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Cla = ClassicalFun(Classical_Data);
structure BasicClassical: BASIC_CLASSICAL = Cla; open BasicClassical;

ML_Context.value_antiq "claset"
  (Scan.succeed ("claset", "Cla.local_claset_of (ML_Context.the_local_context ())"));


(*Propositional rules*)
val prop_cs = empty_cs
  addSIs [@{thm refl}, @{thm TrueI}, @{thm conjI}, @{thm disjCI}, @{thm impI},
    @{thm notI}, @{thm iffI}]
  addSEs [@{thm conjE}, @{thm disjE}, @{thm impCE}, @{thm FalseE}, @{thm iffCE}];

(*Quantifier rules*)
val FOL_cs = prop_cs addSIs [@{thm allI}, @{thm ex_ex1I}] addIs [@{thm exI}]
                     addSEs [@{thm exE}, @{thm alt_ex1E}] addEs [@{thm allE}];

val cla_setup = (fn thy => (change_claset_of thy (fn _ => FOL_cs); thy));

val case_setup =
 (Method.add_methods
    [("case_tac", Method.goal_args Args.name case_tac,
      "case_tac emulation (dynamic instantiation!)")]);
