(*  Title:      HOL/Tools/typedef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Gordon/HOL-style type definitions.
*)

signature TYPEDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val add_typedef_x: string -> bstring * string list * mixfix ->
    string -> string list -> thm list -> tactic option -> theory -> theory
  val add_typedef: bool -> string option -> bstring * string list * mixfix ->
    string -> (bstring * bstring) option -> tactic -> theory -> theory *
    {type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
      Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
      Rep_induct: thm, Abs_induct: thm}
  val add_typedef_i: bool -> string option -> bstring * string list * mixfix ->
    term -> (bstring * bstring) option -> tactic -> theory -> theory *
    {type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
      Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
      Rep_induct: thm, Abs_induct: thm}
  val typedef_proof:
    (string * (bstring * string list * mixfix) * string * (string * string) option) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val typedef_proof_i:
    (string * (bstring * string list * mixfix) * term * (string * string) option) * Comment.text
    -> bool -> theory -> ProofHistory.T
end;

structure TypedefPackage: TYPEDEF_PACKAGE =
struct


(** theory context references **)

val type_definitionN = "Typedef.type_definition";
val type_definition_def = thm "type_definition_def";

val Rep = thm "Rep";
val Rep_inverse = thm "Rep_inverse";
val Abs_inverse = thm "Abs_inverse";
val Rep_inject = thm "Rep_inject";
val Abs_inject = thm "Abs_inject";
val Rep_cases = thm "Rep_cases";
val Abs_cases = thm "Abs_cases";
val Rep_induct = thm "Rep_induct";
val Abs_induct = thm "Abs_induct";



(** type declarations **)

fun add_typedecls decls thy =
  let
    val full = Sign.full_name (Theory.sign_of thy);

    fun arity_of (raw_name, args, mx) =
      (full (Syntax.type_name raw_name mx), replicate (length args) HOLogic.typeS, HOLogic.typeS);
  in
    if can (Theory.assert_super HOL.thy) thy then
      thy
      |> PureThy.add_typedecls decls
      |> Theory.add_arities_i (map arity_of decls)
    else thy |> PureThy.add_typedecls decls
  end;



(** type definitions **)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* prove_nonempty -- tactical version *)        (*exception ERROR*)

fun prove_nonempty thy cset goal (witn1_tac, witn_names, witn_thms, witn2_tac) =
  let
    val is_def = Logic.is_equals o #prop o Thm.rep_thm;
    val thms = PureThy.get_thmss thy witn_names @ witn_thms;
    val tac =
      witn1_tac THEN
      TRY (rewrite_goals_tac (filter is_def thms)) THEN
      TRY (REPEAT_FIRST (resolve_tac (filter_out is_def thms))) THEN
      if_none witn2_tac (TRY (ALLGOALS (CLASET' blast_tac)));
  in
    message ("Proving non-emptiness of set " ^ quote (string_of_cterm cset) ^ " ...");
    Tactic.prove (Theory.sign_of thy) [] [] goal (K tac)
  end handle ERROR => error ("Failed to prove non-emptiness of " ^ quote (string_of_cterm cset));


(* prepare_typedef *)

fun read_term sg used s =
  #1 (Thm.read_def_cterm (sg, K None, K None) used true (s, HOLogic.typeT));

fun cert_term sg _ t = Thm.cterm_of sg t handle TERM (msg, _) => error msg;

fun err_in_typedef name =
  error ("The error(s) above occurred in typedef " ^ quote name);

fun prepare_typedef prep_term def name (t, vs, mx) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Typedef" "typedefs";
    val sign = Theory.sign_of thy;
    val full = Sign.full_name sign;

    (*rhs*)
    val full_name = full name;
    val cset = prep_term sign vs raw_set;
    val {T = setT, t = set, ...} = Thm.rep_cterm cset;
    val rhs_tfrees = term_tfrees set;
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Sign.string_of_typ sign setT));
    fun mk_nonempty A =
      HOLogic.mk_Trueprop (HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), A)));
    val goal = mk_nonempty set;
    val vname = take_suffix Symbol.is_digit (Symbol.explode name)
      |> apfst implode |> apsnd (#1 o Term.read_int);
    val goal_pat = mk_nonempty (Var (vname, setT));

    (*lhs*)
    val lhs_tfrees = map (fn v => (v, if_none (assoc (rhs_tfrees, v)) HOLogic.typeS)) vs;
    val tname = Syntax.type_name t mx;
    val full_tname = full tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val (Rep_name, Abs_name) = if_none opt_morphs ("Rep_" ^ name, "Abs_" ^ name);
    val setC = Const (full_name, setT);
    val RepC = Const (full Rep_name, newT --> oldT);
    val AbsC = Const (full Abs_name, oldT --> newT);
    val x_new = Free ("x", newT);
    val y_old = Free ("y", oldT);

    val set' = if def then setC else set;

    val typedef_name = "type_definition_" ^ name;
    val typedefC =
      Const (type_definitionN, (newT --> oldT) --> (oldT --> newT) --> setT --> HOLogic.boolT);
    val typedef_prop =
      Logic.mk_implies (goal, HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ set'));

    fun typedef_result (theory, nonempty) =
      theory
      |> add_typedecls [(t, vs, mx)]
      |> Theory.add_consts_i
       ((if def then [(name, setT, NoSyn)] else []) @
        [(Rep_name, newT --> oldT, NoSyn),
         (Abs_name, oldT --> newT, NoSyn)])
      |> (if def then (apsnd (Some o hd) oo (PureThy.add_defs_i false o map Thm.no_attributes))
           [Logic.mk_defpair (setC, set)]
          else rpair None)
      |>> PureThy.add_axioms_i [((typedef_name, typedef_prop),
          [apsnd (fn cond_axm => Drule.standard (nonempty RS cond_axm))])]
      |> (fn ((theory', [type_definition]), set_def) =>
        let
          fun make th = Drule.standard (th OF [type_definition]);
          val (theory'', [Rep, Rep_inverse, Abs_inverse, Rep_inject, Abs_inject,
              Rep_cases, Abs_cases, Rep_induct, Abs_induct]) =
            theory'
            |> Theory.add_path name
            |> PureThy.add_thms
              ([((Rep_name, make Rep), []),
                ((Rep_name ^ "_inverse", make Rep_inverse), []),
                ((Abs_name ^ "_inverse", make Abs_inverse), []),
                ((Rep_name ^ "_inject", make Rep_inject), []),
                ((Abs_name ^ "_inject", make Abs_inject), []),
                ((Rep_name ^ "_cases", make Rep_cases),
                  [RuleCases.case_names [Rep_name], InductAttrib.cases_set_global full_name]),
                ((Abs_name ^ "_cases", make Abs_cases),
                  [RuleCases.case_names [Abs_name], InductAttrib.cases_type_global full_tname]),
                ((Rep_name ^ "_induct", make Rep_induct),
                  [RuleCases.case_names [Rep_name], InductAttrib.induct_set_global full_name]),
                ((Abs_name ^ "_induct", make Abs_induct),
                  [RuleCases.case_names [Abs_name], InductAttrib.induct_type_global full_tname])])
            |>> Theory.parent_path;
          val result = {type_definition = type_definition, set_def = set_def,
            Rep = Rep, Rep_inverse = Rep_inverse, Abs_inverse = Abs_inverse,
            Rep_inject = Rep_inject, Abs_inject = Abs_inject, Rep_cases = Rep_cases,
            Abs_cases = Abs_cases, Rep_induct = Rep_induct, Abs_induct = Abs_induct};
        in ((theory'', type_definition), result) end);


    (* errors *)

    fun show_names pairs = commas_quote (map fst pairs);

    val illegal_vars =
      if null (term_vars set) andalso null (term_tvars set) then []
      else ["Illegal schematic variable(s) on rhs"];

    val dup_lhs_tfrees =
      (case duplicates lhs_tfrees of [] => []
      | dups => ["Duplicate type variables on lhs: " ^ show_names dups]);

    val extra_rhs_tfrees =
      (case gen_rems (op =) (rhs_tfrees, lhs_tfrees) of [] => []
      | extras => ["Extra type variables on rhs: " ^ show_names extras]);

    val illegal_frees =
      (case term_frees set of [] => []
      | xs => ["Illegal variables on rhs: " ^ show_names (map dest_Free xs)]);

    val errs = illegal_vars @ dup_lhs_tfrees @ extra_rhs_tfrees @ illegal_frees;
    val _ = if null errs then () else error (cat_lines errs);

    (*test theory errors now!*)
    val test_thy = Theory.copy thy;
    val _ = (test_thy,
      setmp quick_and_dirty true (SkipProof.make_thm test_thy) goal) |> typedef_result;

  in (cset, goal, goal_pat, typedef_result) end
  handle ERROR => err_in_typedef name;


(* add_typedef interfaces *)

fun gen_typedef prep_term def name typ set opt_morphs tac1 names thms tac2 thy =
  let
    val (cset, goal, _, typedef_result) =
      prepare_typedef prep_term def name typ set opt_morphs thy;
    val non_empty = prove_nonempty thy cset goal (tac1, names, thms, tac2);
    val ((thy', _), result) = (thy, non_empty) |> typedef_result;
  in (thy', result) end;

fun sane_typedef prep_term def opt_name typ set opt_morphs tac =
  gen_typedef prep_term def
    (if_none opt_name (#1 typ)) typ set opt_morphs all_tac [] [] (Some tac);

fun add_typedef_x name typ set names thms tac =
  #1 o gen_typedef read_term true name typ set None (Tactic.rtac exI 1) names thms tac;

val add_typedef = sane_typedef read_term;
val add_typedef_i = sane_typedef cert_term;


(* typedef_proof interface *)

fun gen_typedef_proof prep_term ((name, typ, set, opt_morphs), comment) int thy =
  let
    val (_, goal, goal_pat, att_result) =
      prepare_typedef prep_term true name typ set opt_morphs thy;
    val att = #1 o att_result;
  in
    thy
    |> IsarThy.theorem_i Drule.internalK ((("", [att]), (goal, ([goal_pat], []))), comment) int
  end;

val typedef_proof = gen_typedef_proof read_term;
val typedef_proof_i = gen_typedef_proof cert_term;



(** outer syntax **)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val typedeclP =
  OuterSyntax.command "typedecl" "type declaration (HOL)" K.thy_decl
    (P.type_args -- P.name -- P.opt_infix --| P.marg_comment >> (fn ((vs, t), mx) =>
      Toplevel.theory (add_typedecls [(t, vs, mx)])));


val typedef_proof_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") --
    (P.type_args -- P.name) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.name -- P.name)) --
    P.marg_comment;

fun mk_typedef_proof (((((opt_name, (vs, t)), mx), A), morphs), comment) =
  typedef_proof ((if_none opt_name (Syntax.type_name t mx), (t, vs, mx), A, morphs), comment);

val typedefP =
  OuterSyntax.command "typedef" "HOL type definition (requires non-emptiness proof)" K.thy_goal
    (typedef_proof_decl >> (Toplevel.print oo (Toplevel.theory_to_proof o mk_typedef_proof)));


val _ = OuterSyntax.add_keywords ["morphisms"];
val _ = OuterSyntax.add_parsers [typedeclP, typedefP];

end;


end;
