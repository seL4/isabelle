(*  Title:      HOL/typedef.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Internal interface for typedefs.
*)

signature TYPEDEF =
sig
  val prove_nonempty: cterm -> thm list -> tactic option -> thm
  val add_typedef: string -> bstring * string list * mixfix ->
    string -> string list -> thm list -> tactic option -> theory -> theory
  val add_typedef_i: string -> bstring * string list * mixfix ->
    term -> string list -> thm list -> tactic option -> theory -> theory
end;

structure Typedef: TYPEDEF =
struct


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
  end
  handle ERROR =>
    error ("Failed to prove nonemptiness of " ^ quote (string_of_cterm cset));


(* ext_typedef *)

fun ext_typedef prep_term name (t, vs, mx) raw_set axms thms usr_tac thy =
  let
    val _ = require_thy thy "Set" "typedefs";
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
    val tlen = length vs;
    val newT = Type (full_name tname, map TFree lhs_tfrees);

    val Rep_name = "Rep_" ^ name;
    val Abs_name = "Abs_" ^ name;
    val setC = Const (full_name name, setT);
    val RepC = Const (full_name Rep_name, newT --> oldT);
    val AbsC = Const (full_name Abs_name, oldT --> newT);
    val x_new = Free ("x", newT);
    val y_old = Free ("y", oldT);

    (*axioms*)
    val rep_type = HOLogic.mk_Trueprop (HOLogic.mk_mem (RepC $ x_new, setC));
    val rep_type_inv = HOLogic.mk_Trueprop (HOLogic.mk_eq (AbsC $ (RepC $ x_new), x_new));
    val abs_type_inv = Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (y_old, setC)),
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

    writeln("Proving nonemptiness of " ^ quote name ^ " ...");
    prove_nonempty cset (map (get_axiom thy) axms @ thms) usr_tac;

    thy
    |> Theory.add_types [(t, tlen, mx)]
    |> Theory.add_arities_i
     [(full_name tname, replicate tlen logicS, logicS),
      (full_name tname, replicate tlen HOLogic.termS, HOLogic.termS)]
    |> Theory.add_consts_i
     [(name, setT, NoSyn),
      (Rep_name, newT --> oldT, NoSyn),
      (Abs_name, oldT --> newT, NoSyn)]
    |> PureThy.add_store_defs_i
     [(name ^ "_def", Logic.mk_equals (setC, set))]
    |> PureThy.add_store_axioms_i
     [(Rep_name, rep_type),
      (Rep_name ^ "_inverse", rep_type_inv),
      (Abs_name ^ "_inverse", abs_type_inv)]
  end
  handle ERROR =>
    error ("The error(s) above occurred in typedef " ^ quote name);


(* external interfaces *)

fun read_term sg str =
  read_cterm sg (str, HOLogic.termTVar);

fun cert_term sg tm =
  cterm_of sg tm handle TERM (msg, _) => error msg;

val add_typedef = ext_typedef read_term;
val add_typedef_i = ext_typedef cert_term;


end;
