(*  Title:      Pure/Isar/local_defs.ML
    ID:         $Id$
    Author:     Makarius

Local definitions.
*)

signature LOCAL_DEFS =
sig
  val cert_def: ProofContext.context -> term -> (string * typ) * term
  val abs_def: term -> (string * typ) * term
  val mk_def: ProofContext.context -> (string * term) list -> term list
  val def_export: ProofContext.export
  val add_def: string * term -> ProofContext.context ->
    ((string * typ) * thm) * ProofContext.context
  val print_rules: Context.generic -> unit
  val defn_add: attribute
  val defn_del: attribute
  val meta_rewrite_rule: Context.generic -> thm -> thm
  val unfold: ProofContext.context -> thm list -> thm -> thm
  val unfold_goals: ProofContext.context -> thm list -> thm -> thm
  val unfold_tac: ProofContext.context -> thm list -> tactic
  val fold: ProofContext.context -> thm list -> thm -> thm
  val fold_tac: ProofContext.context -> thm list -> tactic
  val derived_def: ProofContext.context -> bool -> term ->
    ((string * typ) * term) * (ProofContext.context -> term -> thm -> thm)
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

fun head_of_def cprop =
  Term.head_of (#1 (Logic.dest_equals (Term.strip_all_body (Thm.term_of cprop))))
  |> Thm.cterm_of (Thm.theory_of_cterm cprop);

(*
  [x, x == t]
       :
      B x
  -----------
      B t
*)
fun def_export _ cprops thm =
  thm
  |> Drule.implies_intr_list cprops
  |> Drule.forall_intr_list (map head_of_def cprops)
  |> Drule.forall_elim_vars 0
  |> RANGE (replicate (length cprops) (Tactic.rtac Drule.reflexive_thm)) 1;


(* add defs *)

fun add_def (x, t) ctxt =
  let
    val [eq] = mk_def ctxt [(x, t)];
    val x' = Term.dest_Free (fst (Logic.dest_equals eq));
  in
    ctxt
    |> ProofContext.add_fixes_i [(x, NONE, NoSyn)] |> snd
    |> ProofContext.add_assms_i def_export [(("", []), [(eq, [])])]
    |>> (fn [(_, [th])] => (x', th))
  end;



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

val print_rules = Rules.print;

val defn_add = Thm.declaration_attribute (Rules.map o Drule.add_rule);
val defn_del = Thm.declaration_attribute (Rules.map o Drule.del_rule);


(* meta rewrite rules *)

val equals_ss =
  MetaSimplifier.theory_context ProtoPure.thy MetaSimplifier.empty_ss
    addeqcongs [Drule.equals_cong];    (*protect meta-level equality*)

fun meta_rewrite context =
  MetaSimplifier.rewrite_cterm (false, false, false) (K (K NONE))
    (equals_ss addsimps (Rules.get context));

val meta_rewrite_rule = Drule.fconv_rule o meta_rewrite;

fun meta_rewrite_tac ctxt i =
  PRIMITIVE (Drule.fconv_rule (Drule.goals_conv (equal i) (meta_rewrite (Context.Proof ctxt))));


(* rewriting with object-level rules *)

fun meta f ctxt = f o map (meta_rewrite_rule (Context.Proof ctxt));

val unfold       = meta Tactic.rewrite_rule;
val unfold_goals = meta Tactic.rewrite_goals_rule;
val unfold_tac   = meta Tactic.rewrite_goals_tac;
val fold         = meta Tactic.fold_rule;
val fold_tac     = meta Tactic.fold_goals_tac;


(* derived defs -- potentially within the object-logic *)

fun derived_def ctxt conditional prop =
  let
    val thy = ProofContext.theory_of ctxt;
    val ((c, T), rhs) = prop
      |> Thm.cterm_of thy
      |> meta_rewrite (Context.Proof ctxt)
      |> (snd o Logic.dest_equals o Thm.prop_of)
      |> K conditional ? Logic.strip_imp_concl
      |> (abs_def o #2 o cert_def ctxt);
    fun prove ctxt' t def =
      let
        val thy' = ProofContext.theory_of ctxt';
        val prop' = Term.subst_atomic [(Free (c, T), t)] prop;
        val frees = Term.fold_aterms (fn Free (x, _) =>
          if Variable.is_fixed ctxt' x then I else insert (op =) x | _ => I) prop' [];
      in
        Goal.prove thy' frees [] prop' (K (ALLGOALS
          (meta_rewrite_tac ctxt' THEN'
            Tactic.rewrite_goal_tac [def] THEN'
            Tactic.resolve_tac [Drule.reflexive_thm])))
        handle ERROR msg => cat_error msg "Failed to prove definitional specification."
      end;
  in (((c, T), rhs), prove) end;

end;
