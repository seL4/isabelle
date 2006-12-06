(*  Title:      Pure/Isar/local_defs.ML
    ID:         $Id$
    Author:     Makarius

Local definitions.
*)

signature LOCAL_DEFS =
sig
  val cert_def: Proof.context -> term -> (string * typ) * term
  val abs_def: term -> (string * typ) * term
  val mk_def: Proof.context -> (string * term) list -> term list
  val expand: cterm list -> thm -> thm
  val def_export: Assumption.export
  val add_defs: ((string * mixfix) * ((bstring * attribute list) * term)) list -> Proof.context ->
    (term * (bstring * thm)) list * Proof.context
  val export: Proof.context -> Proof.context -> thm -> thm list * thm
  val print_rules: Proof.context -> unit
  val defn_add: attribute
  val defn_del: attribute
  val meta_rewrite_rule: Proof.context -> thm -> thm
  val unfold: Proof.context -> thm list -> thm -> thm
  val unfold_goals: Proof.context -> thm list -> thm -> thm
  val unfold_tac: Proof.context -> thm list -> tactic
  val fold: Proof.context -> thm list -> thm -> thm
  val fold_tac: Proof.context -> thm list -> tactic
  val derived_def: Proof.context -> bool -> term ->
    ((string * typ) * term) * (Proof.context -> thm -> thm)
end;

structure LocalDefs: LOCAL_DEFS =
struct

(** primitive definitions **)

(* prepare defs *)

fun cert_def ctxt eq =
  let
    val pp = ProofContext.pp ctxt;
    val display_term = quote o Pretty.string_of_term pp;
    fun err msg = cat_error msg ("The error(s) above occurred in definition: " ^ display_term eq);
    val ((lhs, _), eq') = eq
      |> Sign.no_vars pp
      |> Logic.dest_def pp Term.is_Free (Variable.is_fixed ctxt) (K true)
      handle TERM (msg, _) => err msg | ERROR msg => err msg;
  in (Term.dest_Free (Term.head_of lhs), eq') end;

val abs_def = Logic.abs_def #> apfst Term.dest_Free;

fun mk_def ctxt args =
  let
    val (xs, rhss) = split_list args;
    val (bind, _) = ProofContext.bind_fixes xs ctxt;
    val lhss = map (fn (x, rhs) => bind (Free (x, Term.fastype_of rhs))) args;
  in map Logic.mk_equals (lhss ~~ rhss) end;


(* export defs *)

val head_of_def =
  #1 o Term.dest_Free o Term.head_of o #1 o Logic.dest_equals o Term.strip_all_body;


(*
  [x, x == a]
       :
      B x
  -----------
      B a
*)
fun expand defs =
  Drule.implies_intr_list defs
  #> Drule.generalize ([], map (head_of_def o Thm.term_of) defs)
  #> funpow (length defs) (fn th => Drule.reflexive_thm RS th);

fun expand_term [] = I
  | expand_term defs = Pattern.rewrite_term
      (Theory.merge_list (map Thm.theory_of_cterm defs))
      (map (Logic.dest_equals o Thm.prop_of o Assumption.assume) defs) [];

fun def_export _ defs = (expand defs, expand_term defs);


(* add defs *)

fun add_defs defs ctxt =
  let
    val ((xs, mxs), specs) = defs |> split_list |>> split_list;
    val ((names, atts), rhss) = specs |> split_list |>> split_list;
    val names' = map2 Thm.def_name_optional xs names;
    val eqs = mk_def ctxt (xs ~~ rhss);
    val lhss = map (fst o Logic.dest_equals) eqs;
  in
    ctxt
    |> ProofContext.add_fixes_i (map2 (fn x => fn mx => (x, NONE, mx)) xs mxs) |> #2
    |> fold Variable.declare_term eqs
    |> ProofContext.add_assms_i def_export
      (map2 (fn a => fn eq => (a, [(eq, [])])) (names' ~~ atts) eqs)
    |>> map2 (fn lhs => fn (name, [th]) => (lhs, (name, th))) lhss
  end;


(* specific export -- result based on educated guessing *)

fun export inner outer th =
  let
    val th' = Assumption.export false inner outer th;
    val still_fixed = map #1 (Drule.fold_terms Term.add_frees th' []);
    val defs = Assumption.prems_of inner |> filter_out (fn prem =>
      (case try (head_of_def o Thm.prop_of) prem of
        SOME x => member (op =) still_fixed x
      | NONE => true));
  in (map Drule.abs_def defs, th') end;



(** defived definitions **)

(* transformation rules *)

structure Rules = GenericDataFun
(
  val name = "Pure/derived_defs";
  type T = thm list;
  val empty = []
  val extend = I;
  fun merge _ = Drule.merge_rules;
  fun print context rules =
    Pretty.writeln (Pretty.big_list "definitional transformations:"
      (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
);

val _ = Context.add_setup Rules.init;

val print_rules = Rules.print o Context.Proof;

val defn_add = Thm.declaration_attribute (Rules.map o Drule.add_rule);
val defn_del = Thm.declaration_attribute (Rules.map o Drule.del_rule);


(* meta rewrite rules *)

val equals_ss =
  MetaSimplifier.theory_context ProtoPure.thy MetaSimplifier.empty_ss
    addeqcongs [Drule.equals_cong];    (*protect meta-level equality*)

fun meta_rewrite ctxt =
  MetaSimplifier.rewrite_cterm (false, false, false) (K (K NONE))
    (equals_ss addsimps (Rules.get (Context.Proof ctxt)));

val meta_rewrite_rule = Drule.fconv_rule o meta_rewrite;

fun meta_rewrite_tac ctxt i =
  PRIMITIVE (Drule.fconv_rule (Drule.goals_conv (equal i) (meta_rewrite ctxt)));


(* rewriting with object-level rules *)

fun meta f ctxt = f o map (meta_rewrite_rule ctxt);

val unfold       = meta Tactic.rewrite_rule;
val unfold_goals = meta Tactic.rewrite_goals_rule;
val unfold_tac   = meta Tactic.rewrite_goals_tac;
val fold         = meta Tactic.fold_rule;
val fold_tac     = meta Tactic.fold_goals_tac;


(* derived defs -- potentially within the object-logic *)

fun derived_def ctxt conditional prop =
  let
    val ((c, T), rhs) = prop
      |> Thm.cterm_of (ProofContext.theory_of ctxt)
      |> meta_rewrite ctxt
      |> (snd o Logic.dest_equals o Thm.prop_of)
      |> conditional ? Logic.strip_imp_concl
      |> (abs_def o #2 o cert_def ctxt);
    fun prove ctxt' def =
      let
        val frees = Term.fold_aterms (fn Free (x, _) =>
          if Variable.is_fixed ctxt' x then I else insert (op =) x | _ => I) prop [];
      in
        Goal.prove ctxt' frees [] prop (K (ALLGOALS
          (meta_rewrite_tac ctxt' THEN'
            Goal.rewrite_goal_tac [def] THEN'
            Tactic.resolve_tac [Drule.reflexive_thm])))
        handle ERROR msg => cat_error msg "Failed to prove definitional specification."
      end;
  in (((c, T), rhs), prove) end;

end;
