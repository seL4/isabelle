(*  Title:      HOL/Tools/typedef_package.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Gordon/HOL-style type definitions.
*)

signature TYPEDEF_PACKAGE =
sig
  val quiet_mode: bool ref
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val add_typedef: bool -> string option -> bstring * string list * mixfix ->
    string -> (bstring * bstring) option -> tactic -> theory ->
    {type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
      Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
      Rep_induct: thm, Abs_induct: thm} * theory
  val add_typedef_i: bool -> string option -> bstring * string list * mixfix ->
    term -> (bstring * bstring) option -> tactic -> theory ->
    {type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
      Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
      Rep_induct: thm, Abs_induct: thm} * theory
  val typedef: (bool * string) * (bstring * string list * mixfix) * string
    * (string * string) option -> theory -> Proof.state
  val typedef_i: (bool * string) * (bstring * string list * mixfix) * term
    * (string * string) option -> theory -> Proof.state
  type typedef_info = (typ * typ * string * string) * (thm option * thm * thm)
  val get_typedef_info: theory -> string -> typedef_info option
  val setup: theory -> theory
end;

structure TypedefPackage: TYPEDEF_PACKAGE =
struct


(** theory context references **)

val type_definitionN = "Typedef.type_definition";

val Rep = thm "type_definition.Rep";
val Rep_inverse = thm "type_definition.Rep_inverse";
val Abs_inverse = thm "type_definition.Abs_inverse";
val Rep_inject = thm "type_definition.Rep_inject";
val Abs_inject = thm "type_definition.Abs_inject";
val Rep_cases = thm "type_definition.Rep_cases";
val Abs_cases = thm "type_definition.Abs_cases";
val Rep_induct = thm "type_definition.Rep_induct";
val Abs_induct = thm "type_definition.Abs_induct";



(** type declarations **)

fun HOL_arity (raw_name, args, mx) thy =
  thy |> AxClass.axiomatize_arity_i
    (Sign.full_name thy (Syntax.type_name raw_name mx),
      replicate (length args) HOLogic.typeS, HOLogic.typeS);

fun add_typedecls decls thy =
  thy
  |> Theory.add_typedecls decls
  |> can (Theory.assert_super HOL.thy) ? fold HOL_arity decls;



(** type definitions **)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* theory data *)

type typedef_info = (typ * typ * string * string) * (thm option * thm * thm);

structure TypedefData = TheoryDataFun
(struct
  val name = "HOL/typedef";
  type T = typedef_info Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ (tabs: T * T) = Symtab.merge (op =) tabs;
  fun print _ _ = ();
end);

val get_typedef_info = Symtab.lookup o TypedefData.get;

fun put_typedef newT oldT Abs_name Rep_name def inject inverse =
  TypedefData.map (Symtab.update_new (fst (dest_Type newT),
    ((newT, oldT, Abs_name, Rep_name), (def, inject, inverse))));


(* prepare_typedef *)

fun read_term thy used s =
  #1 (Thm.read_def_cterm (thy, K NONE, K NONE) used true (s, HOLogic.typeT));

fun cert_term thy _ t = Thm.cterm_of thy t handle TERM (msg, _) => error msg;

fun err_in_typedef msg name =
  cat_error msg ("The error(s) above occurred in typedef " ^ quote name);

fun prepare_typedef prep_term def name (t, vs, mx) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Typedef" "typedefs";
    val full = Sign.full_name thy;

    (*rhs*)
    val full_name = full name;
    val cset = prep_term thy vs raw_set;
    val {T = setT, t = set, ...} = Thm.rep_cterm cset;
    val rhs_tfrees = Term.add_tfrees set [];
    val rhs_tfreesT = Term.add_tfreesT setT [];
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Sign.string_of_typ thy setT));
    fun mk_nonempty A =
      HOLogic.mk_Trueprop (HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), A)));
    val goal = mk_nonempty set;
    val goal_pat = mk_nonempty (Var (the_default (name, 0) (Syntax.read_variable name), setT));

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, the_default defS (AList.lookup (op =) rhs_tfrees v))) vs;
    val args_setT = lhs_tfrees
      |> filter (member (op =) rhs_tfrees andf (not o member (op =) rhs_tfreesT))
      |> map TFree;

    val tname = Syntax.type_name t mx;
    val full_tname = full tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val (Rep_name, Abs_name) = the_default ("Rep_" ^ name, "Abs_" ^ name) opt_morphs;
    val setT' = map Term.itselfT args_setT ---> setT;
    val setC = Term.list_comb (Const (full_name, setT'), map Logic.mk_type args_setT);
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

    fun add_def def def' thy =
      if def
      then
        thy
        |> PureThy.add_defs_i false [Thm.no_attributes def']
        |-> (fn [def'] => pair (SOME def'))
      else
        (NONE, thy);

    fun typedef_result nonempty context =
      Context.the_theory context
      |> add_typedecls [(t, vs, mx)]
      |> Theory.add_consts_i
       ((if def then [(name, setT', NoSyn)] else []) @
        [(Rep_name, newT --> oldT, NoSyn),
         (Abs_name, oldT --> newT, NoSyn)])
      |> add_def def (Logic.mk_defpair (setC, set))
      ||>> PureThy.add_axioms_i [((typedef_name, typedef_prop),
          [apsnd (fn cond_axm => Drule.standard (nonempty RS cond_axm))])]
      ||> Theory.add_finals_i false [RepC, AbsC]
      |-> (fn (set_def, [type_definition]) => fn theory' =>
        let
          fun make th = Drule.standard (th OF [type_definition]);
          val abs_inject = make Abs_inject;
          val abs_inverse = make Abs_inverse;
          val ([Rep, Rep_inverse, Abs_inverse, Rep_inject, Abs_inject,
              Rep_cases, Abs_cases, Rep_induct, Abs_induct], theory'') =
            theory'
            |> Theory.add_path name
            |> PureThy.add_thms
              ([((Rep_name, make Rep), []),
                ((Rep_name ^ "_inverse", make Rep_inverse), []),
                ((Abs_name ^ "_inverse", abs_inverse), []),
                ((Rep_name ^ "_inject", make Rep_inject), []),
                ((Abs_name ^ "_inject", abs_inject), []),
                ((Rep_name ^ "_cases", make Rep_cases),
                  [RuleCases.case_names [Rep_name], InductAttrib.cases_set full_name]),
                ((Abs_name ^ "_cases", make Abs_cases),
                  [RuleCases.case_names [Abs_name], InductAttrib.cases_type full_tname]),
                ((Rep_name ^ "_induct", make Rep_induct),
                  [RuleCases.case_names [Rep_name], InductAttrib.induct_set full_name]),
                ((Abs_name ^ "_induct", make Abs_induct),
                  [RuleCases.case_names [Abs_name], InductAttrib.induct_type full_tname])])
            ||> Theory.parent_path
            ||> put_typedef newT oldT (full Abs_name) (full Rep_name)
                 set_def abs_inject abs_inverse
          val result = {type_definition = type_definition, set_def = set_def,
            Rep = Rep, Rep_inverse = Rep_inverse, Abs_inverse = Abs_inverse,
            Rep_inject = Rep_inject, Abs_inject = Abs_inject, Rep_cases = Rep_cases,
            Abs_cases = Abs_cases, Rep_induct = Rep_induct, Abs_induct = Abs_induct};
        in ((type_definition, result), Context.Theory theory'') end);


    (* errors *)

    fun show_names pairs = commas_quote (map fst pairs);

    val illegal_vars =
      if null (term_vars set) andalso null (term_tvars set) then []
      else ["Illegal schematic variable(s) on rhs"];

    val dup_lhs_tfrees =
      (case duplicates (op =) lhs_tfrees of [] => []
      | dups => ["Duplicate type variables on lhs: " ^ show_names dups]);

    val extra_rhs_tfrees =
      (case fold (remove (op =)) lhs_tfrees rhs_tfrees of [] => []
      | extras => ["Extra type variables on rhs: " ^ show_names extras]);

    val illegal_frees =
      (case term_frees set of [] => []
      | xs => ["Illegal variables on rhs: " ^ show_names (map dest_Free xs)]);

    val errs = illegal_vars @ dup_lhs_tfrees @ extra_rhs_tfrees @ illegal_frees;
    val _ = if null errs then () else error (cat_lines errs);

    (*test theory errors now!*)
    val test_thy = Theory.copy thy;
    val _ = 
      Context.Theory test_thy
      |> typedef_result (setmp quick_and_dirty true (SkipProof.make_thm test_thy) goal);

  in (cset, goal, goal_pat, typedef_result) end
  handle ERROR msg => err_in_typedef msg name;


(* add_typedef interfaces *)

local

fun gen_typedef prep_term def opt_name typ set opt_morphs tac thy =
  let
    val name = the_default (#1 typ) opt_name;
    val (cset, goal, _, typedef_result) =
      prepare_typedef prep_term def name typ set opt_morphs thy;
    val _ = message ("Proving non-emptiness of set " ^ quote (string_of_cterm cset) ^ " ...");
    val non_empty = Goal.prove thy [] [] goal (K tac) handle ERROR msg =>
      cat_error msg ("Failed to prove non-emptiness of " ^ quote (string_of_cterm cset));
  in
    Context.Theory thy
    |> typedef_result non_empty
    ||> Context.the_theory
    |-> (fn (_, result) => pair result)
  end;

in

val add_typedef = gen_typedef read_term;
val add_typedef_i = gen_typedef cert_term;

end;


(* Isar typedef interface *)

local

fun gen_typedef prep_term ((def, name), typ, set, opt_morphs) thy =
  let
    val (_, goal, goal_pat, att_result) =
      prepare_typedef prep_term def name typ set opt_morphs thy;
    fun att (thy, th) =
      let val ((th', _), thy') = att_result th thy
      in (thy', th') end;
  in IsarThy.theorem_i PureThy.internalK ("", [att]) (goal, [goal_pat]) thy end;

in

val typedef = gen_typedef read_term;
val typedef_i = gen_typedef cert_term;

end; (*local*)

val setup = TypedefData.init;



(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val typedeclP =
  OuterSyntax.command "typedecl" "type declaration (HOL)" K.thy_decl
    (P.type_args -- P.name -- P.opt_infix >> (fn ((vs, t), mx) =>
      Toplevel.theory (add_typedecls [(t, vs, mx)])));


val typedef_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.name || P.name >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.name) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.name -- P.name));

fun mk_typedef ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  typedef ((def, the_default (Syntax.type_name t mx) opt_name), (t, vs, mx), A, morphs);

val typedefP =
  OuterSyntax.command "typedef" "HOL type definition (requires non-emptiness proof)" K.thy_goal
    (typedef_decl >> (Toplevel.print oo (Toplevel.theory_to_proof o mk_typedef)));


val _ = OuterSyntax.add_keywords ["morphisms"];
val _ = OuterSyntax.add_parsers [typedeclP, typedefP];

end;

end;
