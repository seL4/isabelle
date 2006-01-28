(*  Title:      Pure/Isar/local_defs.ML
    ID:         $Id$
    Author:     Makarius

Basic operations on local definitions.
*)

signature LOCAL_DEFS =
sig
  val mk_def: ProofContext.context -> (string * term) list -> term list
  val cert_def: ProofContext.context -> term -> string * term
  val abs_def: term -> (string * typ) * term
  val derived_def: ProofContext.context -> term ->
    ((string * typ) * term) * (ProofContext.context -> term -> thm -> thm)
  val def_export: ProofContext.export
  val add_def: string * term -> ProofContext.context ->
    ((string * typ) * thm) * ProofContext.context
end;

structure LocalDefs: LOCAL_DEFS =
struct

(* prepare defs *)

fun mk_def ctxt args =
  let
    val (xs, rhss) = split_list args;
    val (bind, _) = ProofContext.bind_fixes xs ctxt;
    val lhss = map (fn (x, rhs) => bind (Free (x, Term.fastype_of rhs))) args;
  in map Logic.mk_equals (lhss ~~ rhss) end;

fun cert_def ctxt eq =
  let
    fun err msg = cat_error msg
      ("The error(s) above occurred in definition: " ^ ProofContext.string_of_term ctxt eq);

    val (lhs, rhs) = Logic.dest_equals (Term.strip_all_body eq)
      handle TERM _ => err "Not a meta-equality (==)";
    val (f, xs) = Term.strip_comb (Pattern.beta_eta_contract lhs);
    val (c, _) = Term.dest_Free f handle TERM _ =>
      err "Head of lhs must be a free/fixed variable";

    fun check_arg (Bound _) = true
      | check_arg (Free (x, _)) = not (ProofContext.is_fixed ctxt x)
      | check_arg t = (case try Logic.dest_type t of SOME (TFree _) => true | _ => false);
    fun close_arg (Free (x, T)) t = Term.all T $ Term.absfree (x, T, t)
      | close_arg (Const ("TYPE", T)) t = Term.all T $ Term.absdummy (T, t)
      | close_arg _ t = t;

    val extra_frees = Term.fold_aterms (fn v as Free (x, _) =>
      if ProofContext.is_fixed ctxt x orelse member (op aconv) xs v then I
      else insert (op =) x | _ => I) rhs [];
  in
    if not (forall check_arg xs) orelse has_duplicates (op =) xs then
      err "Arguments of lhs must be distinct free/bound variables"
    else if not (null extra_frees) then
      err ("Extra free variables on rhs: " ^ commas_quote extra_frees)
    else if Term.exists_subterm (fn t => t = f) rhs then
      err "Element to be defined occurs on rhs"
    else (c, fold_rev close_arg xs eq)
  end;

fun abs_def eq =
  let
    val body = Term.strip_all_body eq;
    val vars = map Free (Term.rename_wrt_term body (Term.strip_all_vars eq));
    val (lhs, rhs) = Logic.dest_equals (Term.subst_bounds (vars, body));
    val (f, xs) = Term.strip_comb (Pattern.beta_eta_contract lhs);
    val eq' = Term.list_abs_free (map Term.dest_Free xs, rhs);
  in (Term.dest_Free f, eq') end;


(* derived defs -- potentially within the object-logic *)

fun derived_def ctxt prop =
  let
    val thy = ProofContext.theory_of ctxt;
    val ((c, T), rhs) = prop
      |> Thm.cterm_of thy
      |> ObjectLogic.meta_rewrite_cterm
      |> (snd o Logic.dest_equals o Thm.prop_of)
      |> Logic.strip_imp_concl
      |> (snd o cert_def ctxt)
      |> abs_def;
    fun prove ctxt' t def =
      let
        val thy' = ProofContext.theory_of ctxt';
        val prop' = Term.subst_atomic [(Free (c, T), t)] prop;
        val frees = Term.fold_aterms (fn Free (x, _) =>
          if ProofContext.is_fixed ctxt' x then I else insert (op =) x | _ => I) prop' [];
      in
        Goal.prove thy' frees [] prop' (K (ALLGOALS
          (ObjectLogic.meta_rewrite_tac THEN'
            Tactic.rewrite_goal_tac [def] THEN'
            Tactic.resolve_tac [Drule.reflexive_thm])))
        handle ERROR msg => cat_error msg "Failed to prove definitional specification."
      end;
  in (((c, T), rhs), prove) end;


(* export defs *)

fun head_of_def cprop =
  #1 (Term.strip_comb (#1 (Logic.dest_equals (Term.strip_all_body (Thm.term_of cprop)))))
  |> Thm.cterm_of (Thm.theory_of_cterm cprop);

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
    |> ProofContext.add_assms_i def_export [(("", []), [(eq, ([], []))])]
    |>> (fn [(_, [th])] => (x', th))
  end;

end;
