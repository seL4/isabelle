(*  Title:      HOL/Tools/typedef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Gordon/HOL-style type definitions.

TODO:
  - typedefP: elim witness;
*)

signature TYPEDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val prove_nonempty: cterm -> thm list -> tactic option -> thm
  val add_typedef: string -> bstring * string list * mixfix ->
    string -> string list -> thm list -> tactic option -> theory -> theory
  val add_typedef_i: string -> bstring * string list * mixfix ->
    term -> string list -> thm list -> tactic option -> theory -> theory
  val add_typedef_i_no_def: string -> bstring * string list * mixfix ->
    term -> string list -> thm list -> tactic option -> theory -> theory
end;

structure TypedefPackage: TYPEDEF_PACKAGE =
struct


(** type declarations **)

fun add_typedecls decls thy =
  let
    val full = Sign.full_name (Theory.sign_of thy);

    fun arity_of (raw_name, args, mx) =
      (full (Syntax.type_name raw_name mx), replicate (length args) HOLogic.termS, HOLogic.termS);
  in
    thy
    |> PureThy.add_typedecls decls
    |> Theory.add_arities_i (map arity_of decls)
  end;



(** type definitions **)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* prove non-emptyness of a set *)   (*exception ERROR*)

val is_def = Logic.is_equals o #prop o rep_thm;

fun prove_nonempty cset thms usr_tac =
  let
    val {T = setT, t = set, maxidx, sign} = rep_cterm cset;
    val T = HOLogic.dest_setT setT;
    val goal = cterm_of sign
      (HOLogic.mk_Trueprop (HOLogic.mk_mem (Var (("x", maxidx + 1), T), set)));
    val tac =
      TRY (rewrite_goals_tac (filter is_def thms)) THEN
      TRY (REPEAT_FIRST (resolve_tac (filter_out is_def thms))) THEN
      if_none usr_tac (TRY (ALLGOALS (CLASET' blast_tac)));
  in
    prove_goalw_cterm [] goal (K [tac])
  end handle ERROR => error ("Failed to prove nonemptiness of " ^ quote (string_of_cterm cset));


(* gen_add_typedef *)

fun gen_add_typedef prep_term no_def name (t, vs, mx) raw_set thm_names thms usr_tac thy =
  let
    val _ = Theory.requires thy "Set" "typedefs";
    val sign = sign_of thy;
    val full_name = Sign.full_name sign;

    (*rhs*)
    val cset = prep_term sign raw_set;
    val {T = setT, t = set, ...} = rep_cterm cset;
    val rhs_tfrees = term_tfrees set;
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Sign.string_of_typ sign setT));

    (*lhs*)
    val lhs_tfrees =
      map (fn v => (v, if_none (assoc (rhs_tfrees, v)) HOLogic.termS)) vs;

    val tname = Syntax.type_name t mx;
    val newT = Type (full_name tname, map TFree lhs_tfrees);

    val Rep_name = "Rep_" ^ name;
    val Abs_name = "Abs_" ^ name;
    val setC = Const (full_name name, setT);
    val RepC = Const (full_name Rep_name, newT --> oldT);
    val AbsC = Const (full_name Abs_name, oldT --> newT);
    val x_new = Free ("x", newT);
    val y_old = Free ("y", oldT);
    val set' = if no_def then set else setC;

    (*axioms*)
    val rep_type = HOLogic.mk_Trueprop (HOLogic.mk_mem (RepC $ x_new, set'));
    val rep_type_inv = HOLogic.mk_Trueprop (HOLogic.mk_eq (AbsC $ (RepC $ x_new), x_new));
    val abs_type_inv = Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (y_old, set')),
      HOLogic.mk_Trueprop (HOLogic.mk_eq (RepC $ (AbsC $ y_old), y_old)));


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
  in
    if null errs then ()
    else error (cat_lines errs);

    message ("Proving nonemptiness of " ^ quote name ^ " ...");
    prove_nonempty cset (PureThy.get_thmss thy thm_names @ thms) usr_tac;

    thy
    |> PureThy.add_typedecls [(t, vs, mx)]
    |> Theory.add_arities_i
     [(full_name tname, replicate (length vs) HOLogic.termS, HOLogic.termS)]
    |> Theory.add_consts_i
     ((if no_def then [] else [(name, setT, NoSyn)]) @
      [(Rep_name, newT --> oldT, NoSyn),
       (Abs_name, oldT --> newT, NoSyn)])
    |> (if no_def then I else (PureThy.add_defs_i o map Thm.no_attributes)
     [(name ^ "_def", Logic.mk_equals (setC, set))])
    |> (PureThy.add_axioms_i o map Thm.no_attributes)
     [(Rep_name, rep_type),
      (Rep_name ^ "_inverse", rep_type_inv),
      (Abs_name ^ "_inverse", abs_type_inv)]
  end handle ERROR => error ("The error(s) above occurred in typedef " ^ quote name);


(* external interfaces *)

fun read_term sg str =
  read_cterm sg (str, HOLogic.termTVar);

fun cert_term sg tm =
  cterm_of sg tm handle TERM (msg, _) => error msg;

val add_typedef = gen_add_typedef read_term false;
val add_typedef_i = gen_add_typedef cert_term false;
val add_typedef_i_no_def = gen_add_typedef cert_term true;


(* outer syntax *)

open OuterParse;


val typedeclP =
  OuterSyntax.parser false "typedecl" "HOL type declaration"
    ((type_args -- name -- opt_mixfix) >> (fn ((vs, t), mx) =>
      Toplevel.theory (add_typedecls [(t, vs, mx)])));

val opt_witness =
  Scan.optional ($$$ "(" |-- !!! (list1 xname --| $$$ ")")) [];

val typedef_decl =
  Scan.option ($$$ "(" |-- name --| $$$ ")") --
    (type_args -- name) -- opt_infix -- ($$$ "=" |-- term -- opt_witness);

val typedefP =
  OuterSyntax.parser false "typedef" "HOL type definition"
    (typedef_decl >> (fn (((opt_name, (vs, t)), mx), (A, witn)) =>
      Toplevel.theory (add_typedef (if_none opt_name t) (t, vs, mx) A witn [] None)));


val _ = OuterSyntax.add_parsers [typedeclP, typedefP];

end;
