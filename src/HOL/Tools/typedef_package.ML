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
  val add_typedef: string -> bstring * string list * mixfix ->
    string -> string list -> thm list -> tactic option -> theory -> theory
  val add_typedef_i: string -> bstring * string list * mixfix ->
    term -> string list -> thm list -> tactic option -> theory -> theory
  val add_typedef_i_no_def: string -> bstring * string list * mixfix ->
    term -> string list -> thm list -> tactic option -> theory -> theory
  val typedef_proof: (string * (bstring * string list * mixfix) * string) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val typedef_proof_i: (string * (bstring * string list * mixfix) * term) * Comment.text
    -> bool -> theory -> ProofHistory.T
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


(* non-emptiness of set *)              (*exception ERROR*)

fun check_nonempty cset thm =
  let
    val {t, sign, maxidx, ...} = Thm.rep_cterm cset;
    val {prop, ...} = Thm.rep_thm (Thm.transfer_sg sign (Drule.standard thm));
    val matches = Pattern.matches (Sign.tsig_of sign);
  in
    (case try (HOLogic.dest_mem o HOLogic.dest_Trueprop) prop of
      None => raise ERROR
    | Some (_, A) => if matches (Logic.incr_indexes ([], maxidx) A, t) then () else raise ERROR)
  end handle ERROR => error ("Bad non-emptiness theorem " ^ Display.string_of_thm thm ^
    "\nfor set " ^ quote (Display.string_of_cterm cset));

fun goal_nonempty ex cset =
  let
    val {T = setT, t = A, maxidx, sign} = Thm.rep_cterm cset;
    val T = HOLogic.dest_setT setT;
    val tm =
      if ex then HOLogic.mk_exists ("x", T, HOLogic.mk_mem (Free ("x", T), A))
      else HOLogic.mk_mem (Var (("x", maxidx + 1), T), A);   (*old-style version*)
  in Thm.cterm_of sign (HOLogic.mk_Trueprop tm) end;

fun prove_nonempty thy cset (witn_names, witn_thms, witn_tac) =
  let
    val is_def = Logic.is_equals o #prop o Thm.rep_thm;
    val thms = PureThy.get_thmss thy witn_names @ witn_thms;
    val tac =
      TRY (rewrite_goals_tac (filter is_def thms)) THEN
      TRY (REPEAT_FIRST (resolve_tac (filter_out is_def thms))) THEN
      if_none witn_tac (TRY (ALLGOALS (CLASET' blast_tac)));
  in
    message ("Proving non-emptiness of set " ^ quote (string_of_cterm cset) ^ " ...");
    prove_goalw_cterm [] (goal_nonempty false cset) (K [tac])
  end handle ERROR => error ("Failed to prove non-emptiness of " ^ quote (string_of_cterm cset));


(* prepare_typedef *)

fun read_term sg used s =
  #1 (Thm.read_def_cterm (sg, K None, K None) used true (s, HOLogic.termT));

fun cert_term sg _ t = Thm.cterm_of sg t handle TERM (msg, _) => error msg;

fun err_in_typedef name =
  error ("The error(s) above occurred in typedef " ^ quote name);

fun prepare_typedef prep_term no_def name (t, vs, mx) raw_set thy =
  let
    val _ = Theory.requires thy "Set" "typedefs";
    val sign = Theory.sign_of thy;
    val full_name = Sign.full_name sign;

    (*rhs*)
    val cset = prep_term sign vs raw_set;
    val {T = setT, t = set, ...} = Thm.rep_cterm cset;
    val rhs_tfrees = term_tfrees set;
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Sign.string_of_typ sign setT));

    (*lhs*)
    val lhs_tfrees = map (fn v => (v, if_none (assoc (rhs_tfrees, v)) HOLogic.termS)) vs;
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

    (*theory extender*)
    fun do_typedef theory =
      theory
      |> Theory.assert_super thy
      |> add_typedecls [(t, vs, mx)]
      |> Theory.add_consts_i
       ((if no_def then [] else [(name, setT, NoSyn)]) @
        [(Rep_name, newT --> oldT, NoSyn),
         (Abs_name, oldT --> newT, NoSyn)])
      |> (if no_def then I else (#1 oo (PureThy.add_defs_i o map Thm.no_attributes))
       [Logic.mk_defpair (setC, set)])
      |> (#1 oo (PureThy.add_axioms_i o map Thm.no_attributes))
       [(Rep_name, rep_type),
        (Rep_name ^ "_inverse", rep_type_inv),
        (Abs_name ^ "_inverse", abs_type_inv)]
      handle ERROR => err_in_typedef name;


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
    if null errs then () else error (cat_lines errs);
    (cset, do_typedef)
  end handle ERROR => err_in_typedef name;


(* add_typedef interfaces *)

fun gen_add_typedef prep_term no_def name typ set names thms tac thy =
  let
    val (cset, do_typedef) = prepare_typedef prep_term no_def name typ set thy;
    val result = prove_nonempty thy cset (names, thms, tac);
  in check_nonempty cset result; thy |> do_typedef end;

val add_typedef = gen_add_typedef read_term false;
val add_typedef_i = gen_add_typedef cert_term false;
val add_typedef_i_no_def = gen_add_typedef cert_term true;


(* typedef_proof interface *)

fun typedef_attribute cset do_typedef (thy, thm) =
  (check_nonempty cset (thm RS (select_eq_Ex RS iffD2)); (thy |> do_typedef, thm));

fun gen_typedef_proof prep_term ((name, typ, set), comment) int thy =
  let
    val (cset, do_typedef) = prepare_typedef prep_term false name typ set thy;
    val goal = Thm.term_of (goal_nonempty true cset);
  in
    thy
    |> IsarThy.theorem_i (("", [typedef_attribute cset do_typedef], (goal, ([], []))), comment) int
  end;

val typedef_proof = gen_typedef_proof read_term;
val typedef_proof_i = gen_typedef_proof cert_term;



(** outer syntax **)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val typedeclP =
  OuterSyntax.command "typedecl" "HOL type declaration" K.thy_decl
    (P.type_args -- P.name -- P.opt_infix --| P.marg_comment >> (fn ((vs, t), mx) =>
      Toplevel.theory (add_typedecls [(t, vs, mx)])));


val typedef_proof_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") --
    (P.type_args -- P.name) -- P.opt_infix -- (P.$$$ "=" |-- P.term) -- P.marg_comment;

fun mk_typedef_proof ((((opt_name, (vs, t)), mx), A), comment) =
  typedef_proof ((if_none opt_name (Syntax.type_name t mx), (t, vs, mx), A), comment);

val typedefP =
  OuterSyntax.command "typedef" "HOL type definition (requires non-emptiness proof)" K.thy_goal
    (typedef_proof_decl >> (Toplevel.print oo (Toplevel.theory_to_proof o mk_typedef_proof)));


val _ = OuterSyntax.add_parsers [typedeclP, typedefP];

end;


end;
