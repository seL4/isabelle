(*  Title:      HOL/Tools/typedef.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Gordon/HOL-style type definitions: create a new syntactic type
represented by a non-empty subset.
*)

signature TYPEDEF =
sig
  type info =
   {rep_type: typ, abs_type: typ, Rep_name: string, Abs_name: string, inhabited: thm,
    type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
    Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
    Rep_induct: thm, Abs_induct: thm}
  val add_typedef: bool -> binding option -> binding * string list * mixfix ->
    term -> (binding * binding) option -> tactic -> theory -> (string * info) * theory
  val typedef: (bool * binding) * (binding * string list * mixfix) * term
    * (binding * binding) option -> theory -> Proof.state
  val typedef_cmd: (bool * binding) * (binding * string list * mixfix) * string
    * (binding * binding) option -> theory -> Proof.state
  val get_info: theory -> string -> info option
  val interpretation: (string -> theory -> theory) -> theory -> theory
  val setup: theory -> theory
end;

structure Typedef: TYPEDEF =
struct

(** type definitions **)

(* theory data *)

type info =
 {rep_type: typ, abs_type: typ, Rep_name: string, Abs_name: string, inhabited: thm,
  type_definition: thm, set_def: thm option, Rep: thm, Rep_inverse: thm,
  Abs_inverse: thm, Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
  Rep_induct: thm, Abs_induct: thm};

structure TypedefData = TheoryDataFun
(
  type T = info Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ tabs : T = Symtab.merge (K true) tabs;
);

val get_info = Symtab.lookup o TypedefData.get;
fun put_info name info = TypedefData.map (Symtab.update (name, info));


(* prepare_typedef *)

fun declare_type_name a = Variable.declare_constraints (Logic.mk_type (TFree (a, dummyS)));

structure TypedefInterpretation = InterpretationFun(type T = string val eq = op =);
val interpretation = TypedefInterpretation.interpretation;

fun prepare_typedef prep_term def name (t, vs, mx) raw_set opt_morphs thy =
  let
    val _ = Theory.requires thy "Typedef" "typedefs";
    val ctxt = ProofContext.init thy;

    val full = Sign.full_name thy;
    val full_name = full name;
    val bname = Binding.name_of name;

    (*rhs*)
    val set = prep_term (ctxt |> fold declare_type_name vs) raw_set;
    val setT = Term.fastype_of set;
    val rhs_tfrees = Term.add_tfrees set [];
    val rhs_tfreesT = Term.add_tfreesT setT [];
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Syntax.string_of_typ ctxt setT));

    (*lhs*)
    val defS = Sign.defaultS thy;
    val lhs_tfrees = map (fn v => (v, the_default defS (AList.lookup (op =) rhs_tfrees v))) vs;
    val args_setT = lhs_tfrees
      |> filter (member (op =) rhs_tfrees andf (not o member (op =) rhs_tfreesT))
      |> map TFree;

    val tname = Binding.map_name (Syntax.type_name mx) t;
    val full_tname = full tname;
    val newT = Type (full_tname, map TFree lhs_tfrees);

    val (Rep_name, Abs_name) =
      (case opt_morphs of
        NONE => (Binding.prefix_name "Rep_" name, Binding.prefix_name "Abs_" name)
      | SOME morphs => morphs);
    val setT' = map Term.itselfT args_setT ---> setT;
    val setC = Term.list_comb (Const (full_name, setT'), map Logic.mk_type args_setT);
    val RepC = Const (full Rep_name, newT --> oldT);
    val AbsC = Const (full Abs_name, oldT --> newT);

    (*inhabitance*)
    fun mk_inhabited A =
      HOLogic.mk_Trueprop (HOLogic.mk_exists ("x", oldT, HOLogic.mk_mem (Free ("x", oldT), A)));
    val set' = if def then setC else set;
    val goal' = mk_inhabited set';
    val goal = mk_inhabited set;
    val goal_pat = mk_inhabited (Var (the_default (bname, 0) (Syntax.read_variable bname), setT));

    (*axiomatization*)
    val typedef_name = Binding.prefix_name "type_definition_" name;
    val typedefC =
      Const (@{const_name type_definition},
        (newT --> oldT) --> (oldT --> newT) --> setT --> HOLogic.boolT);
    val typedef_prop = Logic.mk_implies (goal', HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ set'));
    val typedef_deps = Term.add_consts set' [];

    (*set definition*)
    fun add_def theory =
      if def then
        theory
        |> Sign.add_consts_i [(name, setT', NoSyn)]
        |> PureThy.add_defs false [Thm.no_attributes (apfst (Binding.name)
            (PrimitiveDefs.mk_defpair (setC, set)))]
        |-> (fn [th] => pair (SOME th))
      else (NONE, theory);
    fun contract_def NONE th = th
      | contract_def (SOME def_eq) th =
          let
            val cert = Thm.cterm_of (Thm.theory_of_thm def_eq);
            val goal_eq = MetaSimplifier.rewrite true [def_eq] (cert goal');
          in Drule.standard (Drule.equal_elim_rule2 OF [goal_eq, th]) end;

    fun typedef_result inhabited =
      ObjectLogic.typedecl (t, vs, mx)
      #> snd
      #> Sign.add_consts_i
        [(Rep_name, newT --> oldT, NoSyn),
         (Abs_name, oldT --> newT, NoSyn)]
      #> add_def
      #-> (fn set_def =>
        PureThy.add_axioms [((typedef_name, typedef_prop),
          [Thm.rule_attribute (K (fn cond_axm => contract_def set_def inhabited RS cond_axm))])]
        ##>> pair set_def)
      ##> Theory.add_deps "" (dest_Const RepC) typedef_deps
      ##> Theory.add_deps "" (dest_Const AbsC) typedef_deps
      #-> (fn ([type_definition], set_def) => fn thy1 =>
        let
          fun make th = Drule.standard (th OF [type_definition]);
          val ([Rep, Rep_inverse, Abs_inverse, Rep_inject, Abs_inject,
              Rep_cases, Abs_cases, Rep_induct, Abs_induct], thy2) =
            thy1
            |> Sign.add_path (Binding.name_of name)
            |> PureThy.add_thms
              [((Rep_name, make @{thm type_definition.Rep}), []),
                ((Binding.suffix_name "_inverse" Rep_name, make @{thm type_definition.Rep_inverse}), []),
                ((Binding.suffix_name "_inverse" Abs_name, make @{thm type_definition.Abs_inverse}), []),
                ((Binding.suffix_name "_inject" Rep_name, make @{thm type_definition.Rep_inject}), []),
                ((Binding.suffix_name "_inject" Abs_name, make @{thm type_definition.Abs_inject}), []),
                ((Binding.suffix_name "_cases" Rep_name, make @{thm type_definition.Rep_cases}),
                  [RuleCases.case_names [Binding.name_of Rep_name], Induct.cases_pred full_name]),
                ((Binding.suffix_name "_cases" Abs_name, make @{thm type_definition.Abs_cases}),
                  [RuleCases.case_names [Binding.name_of Abs_name], Induct.cases_type full_tname]),
                ((Binding.suffix_name "_induct" Rep_name, make @{thm type_definition.Rep_induct}),
                  [RuleCases.case_names [Binding.name_of Rep_name], Induct.induct_pred full_name]),
                ((Binding.suffix_name "_induct" Abs_name, make @{thm type_definition.Abs_induct}),
                  [RuleCases.case_names [Binding.name_of Abs_name], Induct.induct_type full_tname])]
            ||> Sign.parent_path;
          val info = {rep_type = oldT, abs_type = newT,
            Rep_name = full Rep_name, Abs_name = full Abs_name,
              inhabited = inhabited, type_definition = type_definition, set_def = set_def,
              Rep = Rep, Rep_inverse = Rep_inverse, Abs_inverse = Abs_inverse,
              Rep_inject = Rep_inject, Abs_inject = Abs_inject, Rep_cases = Rep_cases,
            Abs_cases = Abs_cases, Rep_induct = Rep_induct, Abs_induct = Abs_induct};
        in
          thy2
          |> put_info full_tname info
          |> TypedefInterpretation.data full_tname
          |> pair (full_tname, info)
        end);


    (* errors *)

    fun show_names pairs = commas_quote (map fst pairs);

    val illegal_vars =
      if null (Term.add_vars set []) andalso null (Term.add_tvars set []) then []
      else ["Illegal schematic variable(s) on rhs"];

    val dup_lhs_tfrees =
      (case duplicates (op =) lhs_tfrees of [] => []
      | dups => ["Duplicate type variables on lhs: " ^ show_names dups]);

    val extra_rhs_tfrees =
      (case fold (remove (op =)) lhs_tfrees rhs_tfrees of [] => []
      | extras => ["Extra type variables on rhs: " ^ show_names extras]);

    val illegal_frees =
      (case Term.add_frees set [] of [] => []
      | xs => ["Illegal variables on rhs: " ^ show_names xs]);

    val errs = illegal_vars @ dup_lhs_tfrees @ extra_rhs_tfrees @ illegal_frees;
    val _ = if null errs then () else error (cat_lines errs);

    (*test theory errors now!*)
    val test_thy = Theory.copy thy;
    val _ = test_thy
      |> typedef_result (setmp quick_and_dirty true (SkipProof.make_thm test_thy) goal);

  in (set, goal, goal_pat, typedef_result) end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in typedef " ^ quote (Binding.str_of name));


(* add_typedef: tactic interface *)

fun add_typedef def opt_name typ set opt_morphs tac thy =
  let
    val name = the_default (#1 typ) opt_name;
    val (set, goal, _, typedef_result) =
      prepare_typedef Syntax.check_term def name typ set opt_morphs thy;
    val inhabited = Goal.prove_global thy [] [] goal (K tac)
      handle ERROR msg => cat_error msg
        ("Failed to prove non-emptiness of " ^ quote (Syntax.string_of_term_global thy set));
  in typedef_result inhabited thy end;


(* typedef: proof interface *)

local

fun gen_typedef prep_term ((def, name), typ, set, opt_morphs) thy =
  let
    val (_, goal, goal_pat, typedef_result) =
      prepare_typedef prep_term def name typ set opt_morphs thy;
    fun after_qed [[th]] = ProofContext.theory (snd o typedef_result th);
  in Proof.theorem_i NONE after_qed [[(goal, [goal_pat])]] (ProofContext.init thy) end;

in

val typedef = gen_typedef Syntax.check_term;
val typedef_cmd = gen_typedef Syntax.read_term;

end;



(** outer syntax **)

local structure P = OuterParse in

val _ = OuterKeyword.keyword "morphisms";

val typedef_decl =
  Scan.optional (P.$$$ "(" |--
      ((P.$$$ "open" >> K false) -- Scan.option P.binding || P.binding >> (fn s => (true, SOME s)))
        --| P.$$$ ")") (true, NONE) --
    (P.type_args -- P.binding) -- P.opt_infix -- (P.$$$ "=" |-- P.term) --
    Scan.option (P.$$$ "morphisms" |-- P.!!! (P.binding -- P.binding));

fun mk_typedef ((((((def, opt_name), (vs, t)), mx), A), morphs)) =
  typedef_cmd ((def, the_default (Binding.map_name (Syntax.type_name mx) t) opt_name),
    (t, vs, mx), A, morphs);

val _ =
  OuterSyntax.command "typedef" "HOL type definition (requires non-emptiness proof)"
    OuterKeyword.thy_goal
    (typedef_decl >> (Toplevel.print oo (Toplevel.theory_to_proof o mk_typedef)));

end;


val setup = TypedefInterpretation.init;

end;
