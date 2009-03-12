(*  Title:      Pure/Isar/local_defs.ML
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
  val add_defs: ((binding * mixfix) * (Thm.binding * term)) list -> Proof.context ->
    (term * (string * thm)) list * Proof.context
  val add_def: (binding * mixfix) * term -> Proof.context -> (term * thm) * Proof.context
  val fixed_abbrev: (binding * mixfix) * term -> Proof.context ->
    (term * term) * Proof.context
  val export: Proof.context -> Proof.context -> thm -> thm list * thm
  val export_cterm: Proof.context -> Proof.context -> cterm -> cterm * thm
  val trans_terms: Proof.context -> thm list -> thm
  val trans_props: Proof.context -> thm list -> thm
  val print_rules: Proof.context -> unit
  val defn_add: attribute
  val defn_del: attribute
  val meta_rewrite_conv: Proof.context -> conv
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
    fun err msg = cat_error msg ("The error(s) above occurred in definition: " ^
      quote (Syntax.string_of_term ctxt eq));
    val ((lhs, _), eq') = eq
      |> Sign.no_vars (Syntax.pp ctxt)
      |> PrimitiveDefs.dest_def ctxt Term.is_Free (Variable.is_fixed ctxt) (K true)
      handle TERM (msg, _) => err msg | ERROR msg => err msg;
  in (Term.dest_Free (Term.head_of lhs), eq') end;

val abs_def = PrimitiveDefs.abs_def #>> Term.dest_Free;

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

val expand_term = Envir.expand_term_frees o map (abs_def o Thm.term_of);

fun def_export _ defs = (expand defs, expand_term defs);


(* add defs *)

fun add_defs defs ctxt =
  let
    val ((bvars, mxs), specs) = defs |> split_list |>> split_list;
    val ((bfacts, atts), rhss) = specs |> split_list |>> split_list;
    val xs = map Binding.name_of bvars;
    val names = map2 Thm.def_binding_optional bvars bfacts;
    val eqs = mk_def ctxt (xs ~~ rhss);
    val lhss = map (fst o Logic.dest_equals) eqs;
  in
    ctxt
    |> ProofContext.add_fixes_i (map2 (fn x => fn mx => (x, NONE, mx)) bvars mxs) |> #2
    |> fold Variable.declare_term eqs
    |> ProofContext.add_assms_i def_export
      (map2 (fn a => fn eq => (a, [(eq, [])])) (names ~~ atts) eqs)
    |>> map2 (fn lhs => fn (name, [th]) => (lhs, (name, th))) lhss
  end;

fun add_def (var, rhs) ctxt =
  let val ([(lhs, (_, th))], ctxt') = add_defs [(var, (Thm.empty_binding, rhs))] ctxt
  in ((lhs, th), ctxt') end;


(* fixed_abbrev *)

fun fixed_abbrev ((x, mx), rhs) ctxt =
  let
    val T = Term.fastype_of rhs;
    val ([x'], ctxt') = ctxt
      |> Variable.declare_term rhs
      |> ProofContext.add_fixes_i [(x, SOME T, mx)];
    val lhs = Free (x', T);
    val _ = cert_def ctxt' (Logic.mk_equals (lhs, rhs));
    fun abbrev_export _ _ = (I, Envir.expand_term_frees [((x', T), rhs)]);
    val (_, ctxt'') = Assumption.add_assms abbrev_export [] ctxt';
  in ((lhs, rhs), ctxt'') end;


(* specific export -- result based on educated guessing *)

(*
  [xs, xs == as]
        :
       B xs
  --------------
       B as
*)
fun export inner outer =    (*beware of closure sizes*)
  let
    val exp = Assumption.export false inner outer;
    val prems = Assumption.all_prems_of inner;
  in fn th =>
    let
      val th' = exp th;
      val still_fixed = map #1 (Thm.fold_terms Term.add_frees th' []);
      val defs = prems |> filter_out (fn prem =>
        (case try (head_of_def o Thm.prop_of) prem of
          SOME x => member (op =) still_fixed x
        | NONE => true));
    in (map Drule.abs_def defs, th') end
  end;

(*
  [xs, xs == as]
        :
     TERM b xs
  --------------  and  --------------
     TERM b as          b xs == b as
*)
fun export_cterm inner outer ct =
  let val (defs, ct') = export inner outer (Drule.mk_term ct) ||> Drule.dest_term
  in (ct', MetaSimplifier.rewrite true defs ct) end;


(* basic transitivity reasoning -- modulo beta-eta *)

local

val is_trivial = Pattern.aeconv o Logic.dest_equals o Thm.prop_of;

fun trans_list _ _ [] = raise Empty
  | trans_list trans ctxt (th :: raw_eqs) =
      (case filter_out is_trivial raw_eqs of
        [] => th
      | eqs =>
          let val ((_, th' :: eqs'), ctxt') = Variable.import_thms true (th :: eqs) ctxt
          in singleton (Variable.export ctxt' ctxt) (fold trans eqs' th') end);

in

val trans_terms = trans_list (fn eq2 => fn eq1 => eq2 COMP (eq1 COMP Drule.transitive_thm));
val trans_props = trans_list (fn eq => fn th => th COMP (eq COMP Drule.equal_elim_rule1));

end;



(** defived definitions **)

(* transformation rules *)

structure Rules = GenericDataFun
(
  type T = thm list;
  val empty = []
  val extend = I;
  fun merge _ = Thm.merge_thms;
);

fun print_rules ctxt =
  Pretty.writeln (Pretty.big_list "definitional transformations:"
    (map (ProofContext.pretty_thm ctxt) (Rules.get (Context.Proof ctxt))));

val defn_add = Thm.declaration_attribute (Rules.map o Thm.add_thm);
val defn_del = Thm.declaration_attribute (Rules.map o Thm.del_thm);


(* meta rewrite rules *)

fun meta_rewrite_conv ctxt =
  MetaSimplifier.rewrite_cterm (false, false, false) (K (K NONE))
    (MetaSimplifier.context ctxt MetaSimplifier.empty_ss
      addeqcongs [Drule.equals_cong]    (*protect meta-level equality*)
      addsimps (Rules.get (Context.Proof ctxt)));

val meta_rewrite_rule = Conv.fconv_rule o meta_rewrite_conv;


(* rewriting with object-level rules *)

fun meta f ctxt = f o map (meta_rewrite_rule ctxt);

val unfold       = meta MetaSimplifier.rewrite_rule;
val unfold_goals = meta MetaSimplifier.rewrite_goals_rule;
val unfold_tac   = meta MetaSimplifier.rewrite_goals_tac;
val fold         = meta MetaSimplifier.fold_rule;
val fold_tac     = meta MetaSimplifier.fold_goals_tac;


(* derived defs -- potentially within the object-logic *)

fun derived_def ctxt conditional prop =
  let
    val ((c, T), rhs) = prop
      |> Thm.cterm_of (ProofContext.theory_of ctxt)
      |> meta_rewrite_conv ctxt
      |> (snd o Logic.dest_equals o Thm.prop_of)
      |> conditional ? Logic.strip_imp_concl
      |> (abs_def o #2 o cert_def ctxt);
    fun prove ctxt' def =
      let
        val frees = Term.fold_aterms (fn Free (x, _) =>
          if Variable.is_fixed ctxt' x then I else insert (op =) x | _ => I) prop [];
      in
        Goal.prove ctxt' frees [] prop (K (ALLGOALS
          (CONVERSION (meta_rewrite_conv ctxt') THEN'
            MetaSimplifier.rewrite_goal_tac [def] THEN'
            resolve_tac [Drule.reflexive_thm])))
        handle ERROR msg => cat_error msg "Failed to prove definitional specification."
      end;
  in (((c, T), rhs), prove) end;

end;
