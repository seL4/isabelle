(*  Title:      Pure/Isar/specification.ML
    ID:         $Id$
    Author:     Makarius

Common theory/locale specifications --- with type-inference and
toplevel polymorphism.
*)

signature SPECIFICATION =
sig
  val read_specification: (string * string option * mixfix) list ->
    ((string * Attrib.src list) * string list) list -> Proof.context ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    Proof.context
  val cert_specification: (string * typ option * mixfix) list ->
    ((string * Attrib.src list) * term list) list -> Proof.context ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    Proof.context
  val axiomatization: xstring option -> (string * string option * mixfix) list ->
    ((bstring * Attrib.src list) * string list) list -> theory ->
    (term list * (bstring * thm list) list) * (Proof.context * theory)
  val axiomatization_i: string option -> (string * typ option * mixfix) list ->
    ((bstring * Attrib.src list) * term list) list -> theory ->
    (term list * (bstring * thm list) list) * (Proof.context * theory)
  val definition: xstring option ->
    ((string * string option * mixfix) option * ((string * Attrib.src list) * string)) list ->
    theory -> (term * (bstring * thm)) list * (Proof.context * theory)
  val definition_i: string option ->
    ((string * typ option * mixfix) option * ((string * Attrib.src list) * term)) list ->
    theory -> (term * (bstring * thm)) list * (Proof.context * theory)
end;

structure Specification: SPECIFICATION =
struct

(* prepare specification *)

fun prep_specification prep_vars prep_propp prep_att
    raw_vars raw_specs ctxt =
  let
    val thy = ProofContext.theory_of ctxt;

    val (vars, vars_ctxt) = ctxt |> prep_vars raw_vars;
    val (xs, params_ctxt) = vars_ctxt |> ProofContext.add_fixes_i vars;
    val ((specs, vs), specs_ctxt) =
      prep_propp (params_ctxt, map (map (rpair ([], [])) o snd) raw_specs)
      |> swap |>> map (map fst)
      ||>> fold_map ProofContext.inferred_param xs;

    val params = vs ~~ map #3 vars;
    val names = map (fst o fst) raw_specs;
    val atts = map (map (prep_att thy) o snd o fst) raw_specs;
  in ((params, (names ~~ atts) ~~ specs), specs_ctxt) end;

fun read_specification x =
  prep_specification ProofContext.read_vars ProofContext.read_propp Attrib.intern_src x;
fun cert_specification x =
  prep_specification ProofContext.cert_vars ProofContext.cert_propp (K I) x;


(* axiomatization *)

fun gen_axiomatization prep init locale raw_vars raw_specs thy =
  let
    val ctxt = init locale thy;
    val (vars, specs) = fst (prep raw_vars raw_specs ctxt);

    val (consts, consts_ctxt) = ctxt |> LocalTheory.consts vars;
    val subst = Term.subst_atomic (map (Free o fst) vars ~~ consts);

    val (axioms, axioms_ctxt) =
      consts_ctxt
      |> LocalTheory.axioms (specs |> map (fn (a, props) => (a, map subst props)))
      ||> LocalTheory.theory (Theory.add_finals_i false (map Term.head_of consts));

    val _ =
      if null vars then ()
      else Pretty.writeln (LocalTheory.pretty_consts ctxt (map fst vars));
  in ((consts, axioms), LocalTheory.exit axioms_ctxt) end;

val axiomatization = gen_axiomatization read_specification LocalTheory.init;
val axiomatization_i = gen_axiomatization cert_specification LocalTheory.init_i;


(* definition *)

fun gen_definition prep init locale args thy =
  let
    fun define (raw_var, (raw_a, raw_prop)) ctxt =
      let
        val (vars, [(a, [prop])]) = fst (prep (the_list raw_var) [(raw_a, [raw_prop])] ctxt);
        val ((x, T), rhs) = prop
          |> ObjectLogic.rulify_term thy
          |> ObjectLogic.unatomize_term thy   (*produce meta-level equality*)
          |> Logic.strip_imp_concl
          |> (snd o ProofContext.cert_def ctxt)
          |> ProofContext.abs_def;
        val mx = (case vars of [] => NoSyn | [((x', _), mx)] =>
          if x = x' then mx
          else error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote x'));

        fun prove ctxt' const def =
          let
            val thy' = ProofContext.theory_of ctxt';
            val prop' = Term.subst_atomic [(Free (x, T), const)] prop;
            val frees = Term.fold_aterms (fn Free (x, _) =>
              if ProofContext.is_fixed ctxt' x then I else insert (op =) x | _ => I) prop' [];
          in
            Goal.prove thy' frees [] prop' (K (ALLGOALS
              (ObjectLogic.rulify_tac THEN'
                ObjectLogic.unatomize_tac THEN'
                Tactic.rewrite_goal_tac [def] THEN'
                Tactic.resolve_tac [Drule.reflexive_thm])))
            handle ERROR msg => cat_error msg "Failed to prove definitional specification."
          end;
      in
        ctxt
        |> LocalTheory.def_finish prove ((x, mx), (a, rhs))
        |>> pair (x, T)
      end;

    val ctxt = init locale thy;
    val ((decls, defs), defs_ctxt) = ctxt |> fold_map define args |>> split_list;
    val _ =
      if null decls then ()
      else Pretty.writeln (LocalTheory.pretty_consts ctxt decls);
  in (defs, LocalTheory.exit defs_ctxt) end;

val definition = gen_definition read_specification LocalTheory.init;
val definition_i = gen_definition cert_specification LocalTheory.init_i;

end;
