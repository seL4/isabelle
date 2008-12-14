(*  Title:      Pure/Isar/expression.ML
    Author:     Clemens Ballarin, TU Muenchen

New locale development --- experimental.
*)

signature EXPRESSION =
sig
  datatype 'term map = Positional of 'term option list | Named of (string * 'term) list;
  type 'term expr = (string * ((string * bool) * 'term map)) list;
  type expression = string expr * (Binding.T * string option * mixfix) list;
  type expression_i = term expr * (Binding.T * typ option * mixfix) list;

  (* Processing of context statements *)
  val read_statement: Element.context list -> (string * string list) list list ->
    Proof.context ->  (term * term list) list list * Proof.context;
  val cert_statement: Element.context_i list -> (term * term list) list list ->
    Proof.context -> (term * term list) list list * Proof.context;

  (* Declaring locales *)
  val add_locale_cmd: string -> bstring -> expression -> Element.context list -> theory ->
    (string * (string * (Attrib.binding * (thm list * Attrib.src list) list) list) list) *
    Proof.context
  val add_locale: string -> bstring -> expression_i -> Element.context_i list -> theory ->
    (string * (string * (Attrib.binding * (thm list * Attrib.src list) list) list) list) *
    Proof.context

  (* Interpretation *)
  val sublocale_cmd: string -> expression -> theory -> Proof.state;
  val sublocale: string -> expression_i -> theory -> Proof.state;
  val interpretation_cmd: expression -> (Attrib.binding * string) list -> theory -> Proof.state;
  val interpretation: expression_i -> (Attrib.binding * term) list -> theory -> Proof.state;
  val interpret_cmd: expression -> bool -> Proof.state -> Proof.state;
  val interpret: expression_i -> bool -> Proof.state -> Proof.state;
end;


structure Expression : EXPRESSION =
struct

datatype ctxt = datatype Element.ctxt;


(*** Expressions ***)

datatype 'term map =
  Positional of 'term option list |
  Named of (string * 'term) list;

type 'term expr = (string * ((string * bool) * 'term map)) list;

type expression = string expr * (Binding.T * string option * mixfix) list;
type expression_i = term expr * (Binding.T * typ option * mixfix) list;


(** Internalise locale names in expr **)

fun intern thy instances =  map (apfst (NewLocale.intern thy)) instances;


(** Parameters of expression.

   Sanity check of instantiations and extraction of implicit parameters.
   The latter only occurs iff strict = false.
   Positional instantiations are extended to match full length of parameter list
   of instantiated locale. **)

fun parameters_of thy strict (expr, fixed) =
  let
    fun reject_dups message xs =
      let val dups = duplicates (op =) xs
      in
        if null dups then () else error (message ^ commas dups)
      end;

    fun match_bind (n, b) = (n = Binding.base_name b);
    fun parm_eq ((b1, mx1), (b2, mx2)) =
      (* FIXME: cannot compare bindings for equality, instead check for equal name and syntax *)
      (Binding.base_name b1 = Binding.base_name b2) andalso
      (if mx1 = mx2 then true
      else error ("Conflicting syntax for parameter" ^ quote (Binding.display b1) ^
                    " in expression."));
      
    fun bind_eq (b1, b2) = (Binding.base_name b1 = Binding.base_name b2);
      (* FIXME: cannot compare bindings for equality. *)

    fun params_loc loc =
          (NewLocale.params_of thy loc |> map (fn (p, _, mx) => (p, mx)), loc);
    fun params_inst (expr as (loc, (prfx, Positional insts))) =
          let
            val (ps, loc') = params_loc loc;
	    val d = length ps - length insts;
	    val insts' =
	      if d < 0 then error ("More arguments than parameters in instantiation of locale " ^
                quote (NewLocale.extern thy loc))
	      else insts @ replicate d NONE;
            val ps' = (ps ~~ insts') |>
              map_filter (fn (p, NONE) => SOME p | (_, SOME _) => NONE);
          in (ps', (loc', (prfx, Positional insts'))) end
      | params_inst (expr as (loc, (prfx, Named insts))) =
          let
            val _ = reject_dups "Duplicate instantiation of the following parameter(s): "
              (map fst insts);

            val (ps, loc') = params_loc loc;
            val ps' = fold (fn (p, _) => fn ps =>
              if AList.defined match_bind ps p then AList.delete match_bind p ps
              else error (quote p ^" not a parameter of instantiated expression.")) insts ps;
          in (ps', (loc', (prfx, Named insts))) end;
    fun params_expr is =
          let
            val (is', ps') = fold_map (fn i => fn ps =>
              let
                val (ps', i') = params_inst i;
                val ps'' = distinct parm_eq (ps @ ps');
              in (i', ps'') end) is []
          in (ps', is') end;

    val (implicit, expr') = params_expr expr;

    val implicit' = map (#1 #> Binding.base_name) implicit;
    val fixed' = map (#1 #> Binding.base_name) fixed;
    val _ = reject_dups "Duplicate fixed parameter(s): " fixed';
    val implicit'' = if strict then []
      else let val _ = reject_dups
          "Parameter(s) declared simultaneously in expression and for clause: " (implicit' @ fixed')
        in map (fn (b, mx) => (b, NONE, mx)) implicit end;

  in (expr', implicit'' @ fixed) end;


(** Read instantiation **)

(* Parse positional or named instantiation *)

local

fun prep_inst parse_term parms (Positional insts) ctxt =
      (insts ~~ parms) |> map (fn
        (NONE, p) => Syntax.parse_term ctxt p |
        (SOME t, _) => parse_term ctxt t)
  | prep_inst parse_term parms (Named insts) ctxt =
      parms |> map (fn p => case AList.lookup (op =) insts p of
        SOME t => parse_term ctxt t |
        NONE => Syntax.parse_term ctxt p);

in

fun parse_inst x = prep_inst Syntax.parse_term x;
fun make_inst x = prep_inst (K I) x;

end;


(* Instantiation morphism *)

fun inst_morph (parm_names, parm_types) ((prfx, strict), insts') ctxt =
  let
    (* parameters *)
    val type_parm_names = fold Term.add_tfreesT parm_types [] |> map fst;

    (* type inference and contexts *)
    val parm_types' = map (TypeInfer.paramify_vars o Logic.varifyT) parm_types;
    val type_parms = fold Term.add_tvarsT parm_types' [] |> map (Logic.mk_type o TVar);
    val arg = type_parms @ map2 TypeInfer.constrain parm_types' insts';
    val res = Syntax.check_terms ctxt arg;
    val ctxt' = ctxt |> fold Variable.auto_fixes res;
    
    (* instantiation *)
    val (type_parms'', res') = chop (length type_parms) res;
    val insts'' = (parm_names ~~ res') |> map_filter
      (fn (inst as (x, Free (y, _))) => if x = y then NONE else SOME inst |
        inst => SOME inst);
    val instT = Symtab.make (type_parm_names ~~ map Logic.dest_type type_parms'');
    val inst = Symtab.make insts'';
  in
    (Element.inst_morphism (ProofContext.theory_of ctxt) (instT, inst) $>
      Morphism.binding_morphism (Binding.add_prefix strict prfx), ctxt')
  end;


(*** Locale processing ***)

(** Parsing **)

fun parse_elem prep_typ prep_term ctxt elem =
  Element.map_ctxt {binding = I, var = I, typ = prep_typ ctxt,
    term = prep_term ctxt, fact = I, attrib = I} elem;

fun parse_concl prep_term ctxt concl =
  (map o map) (fn (t, ps) =>
    (prep_term ctxt, map (prep_term ctxt) ps)) concl;


(** Simultaneous type inference: instantiations + elements + conclusion **)

local

fun mk_type T = (Logic.mk_type T, []);
fun mk_term t = (t, []);
fun mk_propp (p, pats) = (Syntax.type_constraint propT p, pats);

fun dest_type (T, []) = Logic.dest_type T;
fun dest_term (t, []) = t;
fun dest_propp (p, pats) = (p, pats);

fun extract_inst (_, (_, ts)) = map mk_term ts;
fun restore_inst ((l, (p, _)), cs) = (l, (p, map dest_term cs));

fun extract_elem (Fixes fixes) = map (#2 #> the_list #> map mk_type) fixes
  | extract_elem (Constrains csts) = map (#2 #> single #> map mk_type) csts
  | extract_elem (Assumes asms) = map (#2 #> map mk_propp) asms
  | extract_elem (Defines defs) = map (fn (_, (t, ps)) => [mk_propp (t, ps)]) defs
  | extract_elem (Notes _) = [];

fun restore_elem (Fixes fixes, css) =
      (fixes ~~ css) |> map (fn ((x, _, mx), cs) =>
        (x, cs |> map dest_type |> try hd, mx)) |> Fixes
  | restore_elem (Constrains csts, css) =
      (csts ~~ css) |> map (fn ((x, _), cs) =>
        (x, cs |> map dest_type |> hd)) |> Constrains
  | restore_elem (Assumes asms, css) =
      (asms ~~ css) |> map (fn ((b, _), cs) => (b, map dest_propp cs)) |> Assumes
  | restore_elem (Defines defs, css) =
      (defs ~~ css) |> map (fn ((b, _), [c]) => (b, dest_propp c)) |> Defines
  | restore_elem (Notes notes, _) = Notes notes;

fun check cs context =
  let
    fun prep (_, pats) (ctxt, t :: ts) =
      let val ctxt' = Variable.auto_fixes t ctxt
      in
        ((t, Syntax.check_props (ProofContext.set_mode ProofContext.mode_pattern ctxt') pats),
          (ctxt', ts))
      end
    val (cs', (context', _)) = fold_map prep cs
      (context, Syntax.check_terms
        (ProofContext.set_mode ProofContext.mode_schematic context) (map fst cs));
  in (cs', context') end;

in

fun check_autofix insts elems concl ctxt =
  let
    val inst_cs = map extract_inst insts;
    val elem_css = map extract_elem elems;
    val concl_cs = (map o map) mk_propp concl;
    (* Type inference *)
    val (inst_cs' :: css', ctxt') =
      (fold_burrow o fold_burrow) check (inst_cs :: elem_css @ [concl_cs]) ctxt;
    val (elem_css', [concl_cs']) = chop (length elem_css) css';
  in
    (map restore_inst (insts ~~ inst_cs'), map restore_elem (elems ~~ elem_css'),
      concl_cs', ctxt')
  end;

end;


(** Prepare locale elements **)

fun declare_elem prep_vars (Fixes fixes) ctxt =
      let val (vars, _) = prep_vars fixes ctxt
      in ctxt |> ProofContext.add_fixes_i vars |> snd end
  | declare_elem prep_vars (Constrains csts) ctxt =
      ctxt |> prep_vars (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) csts) |> snd
  | declare_elem _ (Assumes _) ctxt = ctxt
  | declare_elem _ (Defines _) ctxt = ctxt
  | declare_elem _ (Notes _) ctxt = ctxt;

(** Finish locale elements, extract specification text **)

val norm_term = Envir.beta_norm oo Term.subst_atomic;

fun bind_def ctxt eq (xs, env, eqs) =
  let
    val _ = LocalDefs.cert_def ctxt eq;
    val ((y, T), b) = LocalDefs.abs_def eq;
    val b' = norm_term env b;
    fun err msg = error (msg ^ ": " ^ quote y);
  in
    exists (fn (x, _) => x = y) xs andalso
      err "Attempt to define previously specified variable";
    exists (fn (Free (y', _), _) => y = y' | _ => false) env andalso
      err "Attempt to redefine variable";
    (Term.add_frees b' xs, (Free (y, T), b') :: env, eq :: eqs)
  end;

fun eval_text _ _ (Fixes _) text = text
  | eval_text _ _ (Constrains _) text = text
  | eval_text _ is_ext (Assumes asms)
        (((exts, exts'), (ints, ints')), (xs, env, defs)) =
      let
        val ts = maps (map #1 o #2) asms;
        val ts' = map (norm_term env) ts;
        val spec' =
          if is_ext then ((exts @ ts, exts' @ ts'), (ints, ints'))
          else ((exts, exts'), (ints @ ts, ints' @ ts'));
      in (spec', (fold Term.add_frees ts' xs, env, defs)) end
  | eval_text ctxt _ (Defines defs) (spec, binds) =
      (spec, fold (bind_def ctxt o #1 o #2) defs binds)
  | eval_text _ _ (Notes _) text = text;

fun closeup _ _ false elem = elem
  | closeup ctxt parms true elem =
      let
        fun close_frees t =
          let
            val rev_frees =
              Term.fold_aterms (fn Free (x, T) =>
                if AList.defined (op =) parms x then I else insert (op =) (x, T) | _ => I) t [];
          in Term.list_all_free (rev rev_frees, t) end; (* FIXME use fold Logic.all *)
  (* FIXME consider closing in syntactic phase *)

        fun no_binds [] = []
          | no_binds _ = error "Illegal term bindings in context element";
      in
        (case elem of
          Assumes asms => Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, ps) => (close_frees t, no_binds ps)) propps)))
        | Defines defs => Defines (defs |> map (fn ((name, atts), (t, ps)) =>
            let val ((c, _), t') = LocalDefs.cert_def ctxt (close_frees t)
            in
              ((Binding.map_base (Thm.def_name_optional c) name, atts), (t', no_binds ps))
            end))
        | e => e)
      end;

fun finish_primitive parms _ (Fixes fixes) = Fixes (map (fn (binding, _, mx) =>
      let val x = Binding.base_name binding
      in (binding, AList.lookup (op =) parms x, mx) end) fixes)
  | finish_primitive _ _ (Constrains _) = Constrains []
  | finish_primitive _ close (Assumes asms) = close (Assumes asms)
  | finish_primitive _ close (Defines defs) = close (Defines defs)
  | finish_primitive _ _ (Notes facts) = Notes facts;

fun finish_inst ctxt parms do_close (loc, (prfx, inst)) text =
  let
    val thy = ProofContext.theory_of ctxt;
    val (parm_names, parm_types) = NewLocale.params_of thy loc |>
      map (fn (b, SOME T, _) => (Binding.base_name b, T)) |> split_list;
    val (asm, defs) = NewLocale.specification_of thy loc;
    val (morph, _) = inst_morph (parm_names, parm_types) (prfx, inst) ctxt;
    val asm' = Option.map (Morphism.term morph) asm;
    val defs' = map (Morphism.term morph) defs;
    val text' = text |>
      (if is_some asm
        then eval_text ctxt false (Assumes [(Attrib.empty_binding, [(the asm', [])])])
        else I) |>
      (if not (null defs)
        then eval_text ctxt false (Defines (map (fn def => (Attrib.empty_binding, (def, []))) defs'))
        else I)
(* FIXME clone from new_locale.ML *)
  in ((loc, morph), text') end;

fun finish_elem ctxt parms do_close elem text =
  let
    val elem' = finish_primitive parms (closeup ctxt parms do_close) elem;
    val text' = eval_text ctxt true elem' text;
  in (elem', text') end
  
fun finish ctxt parms do_close insts elems text =
  let
    val (deps, text') = fold_map (finish_inst ctxt parms do_close) insts text;
    val (elems', text'') = fold_map (finish_elem ctxt parms do_close) elems text';
  in (deps, elems', text'') end;


(** Process full context statement: instantiations + elements + conclusion **)

(* Interleave incremental parsing and type inference over entire parsed stretch. *)

local

fun prep_full_context_statement parse_typ parse_prop parse_inst prep_vars prep_expr
    strict do_close context raw_import raw_elems raw_concl =
  let
    val thy = ProofContext.theory_of context;

    val (raw_insts, fixed) = parameters_of thy strict (apfst (prep_expr thy) raw_import);

    fun prep_inst (loc, (prfx, inst)) (i, insts, ctxt) =
      let
        val (parm_names, parm_types) = NewLocale.params_of thy loc |>
          map (fn (b, SOME T, _) => (Binding.base_name b, T)) |> split_list;
        val inst' = parse_inst parm_names inst ctxt;
        val parm_types' = map (TypeInfer.paramify_vars o
          Term.map_type_tvar (fn ((x, _), S) => TVar ((x, i), S)) o Logic.varifyT) parm_types;
        val inst'' = map2 TypeInfer.constrain parm_types' inst';
        val insts' = insts @ [(loc, (prfx, inst''))];
        val (insts'', _, _, ctxt' (* FIXME not used *) ) = check_autofix insts' [] [] ctxt;
        val inst''' = insts'' |> List.last |> snd |> snd;
        val (morph, _) = inst_morph (parm_names, parm_types) (prfx, inst''') ctxt;
        val ctxt'' = NewLocale.activate_declarations thy (loc, morph) ctxt;
      in (i+1, insts', ctxt'') end;
  
    fun prep_elem raw_elem (insts, elems, ctxt) =
      let
        val ctxt' = declare_elem prep_vars raw_elem ctxt;
        val elems' = elems @ [parse_elem parse_typ parse_prop ctxt' raw_elem];
        (* FIXME term bindings *)
        val (_, _, _, ctxt'') = check_autofix insts elems' [] ctxt';
      in (insts, elems', ctxt') end;

    fun prep_concl raw_concl (insts, elems, ctxt) =
      let
        val concl = (map o map) (fn (t, ps) =>
          (parse_prop ctxt t, map (parse_prop ctxt) ps)) raw_concl;
      in check_autofix insts elems concl ctxt end;

    val fors = prep_vars fixed context |> fst;
    val ctxt = context |> ProofContext.add_fixes_i fors |> snd;
    val (_, insts', ctxt') = fold prep_inst raw_insts (0, [], ctxt);
    val (_, elems'', ctxt'') = fold prep_elem raw_elems (insts', [], ctxt');
    val (insts, elems, concl, ctxt) = prep_concl raw_concl (insts', elems'', ctxt'');

    (* Retrieve parameter types *)
    val xs = fold (fn Fixes fixes => (fn ps => ps @ map (Binding.base_name o #1) fixes) |
      _ => fn ps => ps) (Fixes fors :: elems) [];
    val (Ts, ctxt') = fold_map ProofContext.inferred_param xs ctxt; 
    val parms = xs ~~ Ts;  (* params from expression and elements *)

    val Fixes fors' = finish_primitive parms I (Fixes fors);
    val (deps, elems', text) = finish ctxt' parms do_close insts elems ((([], []), ([], [])), ([], [], []));
    (* text has the following structure:
           (((exts, exts'), (ints, ints')), (xs, env, defs))
       where
         exts: external assumptions (terms in assumes elements)
         exts': dito, normalised wrt. env
         ints: internal assumptions (terms in assumptions from insts)
         ints': dito, normalised wrt. env
         xs: the free variables in exts' and ints' and rhss of definitions,
           this includes parameters except defined parameters
         env: list of term pairs encoding substitutions, where the first term
           is a free variable; substitutions represent defines elements and
           the rhs is normalised wrt. the previous env
         defs: the equations from the defines elements
       elems is an updated version of raw_elems:
         - type info added to Fixes and modified in Constrains
         - axiom and definition statement replaced by corresponding one
           from proppss in Assumes and Defines
         - Facts unchanged
       *)

  in ((fors', deps, elems', concl), (parms, text)) end

in

fun read_full_context_statement x =
  prep_full_context_statement Syntax.parse_typ Syntax.parse_prop parse_inst
  ProofContext.read_vars intern x;
fun cert_full_context_statement x =
  prep_full_context_statement (K I) (K I) make_inst ProofContext.cert_vars (K I) x;

end;


(* Context statement: elements + conclusion *)

local

fun prep_statement prep activate raw_elems raw_concl context =
  let
     val ((_, _, elems, concl), _) = prep true false context ([], []) raw_elems raw_concl;
     val (_, context') = activate elems (ProofContext.set_stmt true context);
  in (concl, context') end;

in

fun read_statement x = prep_statement read_full_context_statement Element.activate x;
fun cert_statement x = prep_statement cert_full_context_statement Element.activate_i x;

end;


(* Locale declaration: import + elements *)

local

fun prep_declaration prep activate raw_import raw_elems context =
  let
    val ((fixed, deps, elems, _), (parms, (spec, (_, _, defs)))) =
      prep false true context raw_import raw_elems [];
    (* Declare parameters and imported facts *)
    val context' = context |>
      ProofContext.add_fixes_i fixed |> snd |>
      fold NewLocale.activate_local_facts deps;
    val ((elems', _), _) = activate elems (ProofContext.set_stmt true context');
  in ((fixed, deps, elems'), (parms, spec, defs)) end;

in

fun read_declaration x = prep_declaration read_full_context_statement Element.activate x;
fun cert_declaration x = prep_declaration cert_full_context_statement Element.activate_i x;

end;


(* Locale expression to set up a goal *)

local

fun props_of thy (name, morph) =
  let
    val (asm, defs) = NewLocale.specification_of thy name;
  in
    (case asm of NONE => defs | SOME asm => asm :: defs) |> map (Morphism.term morph)
  end;

fun prep_goal_expression prep expression context =
  let
    val thy = ProofContext.theory_of context;

    val ((fixed, deps, _, _), _) = prep true true context expression [] [];
    (* proof obligations *)
    val propss = map (props_of thy) deps;

    val goal_ctxt = context |>
      ProofContext.add_fixes_i fixed |> snd |>
      (fold o fold) Variable.auto_fixes propss;

    val export = Variable.export_morphism goal_ctxt context;
    val exp_fact = Drule.zero_var_indexes_list o map Thm.strip_shyps o Morphism.fact export;
    val exp_term = Drule.term_rule thy (singleton exp_fact);
    val exp_typ = Logic.type_map exp_term;
    val export' =
      Morphism.morphism {binding = I, var = I, typ = exp_typ, term = exp_term, fact = exp_fact};
  in ((propss, deps, export'), goal_ctxt) end;
    
in

fun read_goal_expression x = prep_goal_expression read_full_context_statement x;
fun cert_goal_expression x = prep_goal_expression cert_full_context_statement x;

end;


(*** Locale declarations ***)

(* axiomsN: name of theorem set with destruct rules for locale predicates,
     also name suffix of delta predicates and assumptions. *)

val axiomsN = "axioms";

local

(* introN: name of theorems for introduction rules of locale and
     delta predicates *)

val introN = "intro";

fun atomize_spec thy ts =
  let
    val t = Logic.mk_conjunction_balanced ts;
    val body = ObjectLogic.atomize_term thy t;
    val bodyT = Term.fastype_of body;
  in
    if bodyT = propT then (t, propT, Thm.reflexive (Thm.cterm_of thy t))
    else (body, bodyT, ObjectLogic.atomize (Thm.cterm_of thy t))
  end;

(* achieve plain syntax for locale predicates (without "PROP") *)

fun aprop_tr' n c = (Syntax.constN ^ c, fn ctxt => fn args =>
  if length args = n then
    Syntax.const "_aprop" $
      Term.list_comb (Syntax.free (Consts.extern (ProofContext.consts_of ctxt) c), args)
  else raise Match);

(* define one predicate including its intro rule and axioms
   - bname: predicate name
   - parms: locale parameters
   - defs: thms representing substitutions from defines elements
   - ts: terms representing locale assumptions (not normalised wrt. defs)
   - norm_ts: terms representing locale assumptions (normalised wrt. defs)
   - thy: the theory
*)

fun def_pred bname parms defs ts norm_ts thy =
  let
    val name = Sign.full_bname thy bname;

    val (body, bodyT, body_eq) = atomize_spec thy norm_ts;
    val env = Term.add_term_free_names (body, []);
    val xs = filter (member (op =) env o #1) parms;
    val Ts = map #2 xs;
    val extraTs = (Term.term_tfrees body \\ fold Term.add_tfreesT Ts [])
      |> Library.sort_wrt #1 |> map TFree;
    val predT = map Term.itselfT extraTs ---> Ts ---> bodyT;

    val args = map Logic.mk_type extraTs @ map Free xs;
    val head = Term.list_comb (Const (name, predT), args);
    val statement = ObjectLogic.ensure_propT thy head;

    val ([pred_def], defs_thy) =
      thy
      |> bodyT = propT ? Sign.add_advanced_trfuns ([], [], [aprop_tr' (length args) name], [])
      |> Sign.declare_const [] ((Binding.name bname, predT), NoSyn) |> snd
      |> PureThy.add_defs false
        [((Thm.def_name bname, Logic.mk_equals (head, body)), [Thm.kind_internal])];
    val defs_ctxt = ProofContext.init defs_thy |> Variable.declare_term head;

    val cert = Thm.cterm_of defs_thy;

    val intro = Goal.prove_global defs_thy [] norm_ts statement (fn _ =>
      MetaSimplifier.rewrite_goals_tac [pred_def] THEN
      Tactic.compose_tac (false, body_eq RS Drule.equal_elim_rule1, 1) 1 THEN
      Tactic.compose_tac (false,
        Conjunction.intr_balanced (map (Thm.assume o cert) norm_ts), 0) 1);

    val conjuncts =
      (Drule.equal_elim_rule2 OF [body_eq,
        MetaSimplifier.rewrite_rule [pred_def] (Thm.assume (cert statement))])
      |> Conjunction.elim_balanced (length ts);
    val axioms = ts ~~ conjuncts |> map (fn (t, ax) =>
      Element.prove_witness defs_ctxt t
       (MetaSimplifier.rewrite_goals_tac defs THEN
        Tactic.compose_tac (false, ax, 0) 1));
  in ((statement, intro, axioms), defs_thy) end;

in

(* CB: main predicate definition function *)

fun define_preds pname (parms, ((exts, exts'), (ints, ints')), defs) thy =
  let
    val defs' = map (cterm_of thy #> Assumption.assume #> Drule.gen_all #> Drule.abs_def) defs;

    val (a_pred, a_intro, a_axioms, thy'') =
      if null exts then (NONE, NONE, [], thy)
      else
        let
          val aname = if null ints then pname else pname ^ "_" ^ axiomsN;
          val ((statement, intro, axioms), thy') =
            thy
            |> def_pred aname parms defs' exts exts';
          val (_, thy'') =
            thy'
            |> Sign.add_path aname
            |> Sign.no_base_names
            |> PureThy.note_thmss Thm.internalK
              [((Binding.name introN, []), [([intro], [NewLocale.unfold_attrib])])]
            ||> Sign.restore_naming thy';
          in (SOME statement, SOME intro, axioms, thy'') end;
    val (b_pred, b_intro, b_axioms, thy'''') =
      if null ints then (NONE, NONE, [], thy'')
      else
        let
          val ((statement, intro, axioms), thy''') =
            thy''
            |> def_pred pname parms defs' (ints @ the_list a_pred) (ints' @ the_list a_pred);
          val (_, thy'''') =
            thy'''
            |> Sign.add_path pname
            |> Sign.no_base_names
            |> PureThy.note_thmss Thm.internalK
                 [((Binding.name introN, []), [([intro], [NewLocale.intro_attrib])]),
                  ((Binding.name axiomsN, []),
                    [(map (Drule.standard o Element.conclude_witness) axioms, [])])]
            ||> Sign.restore_naming thy''';
        in (SOME statement, SOME intro, axioms, thy'''') end;
  in ((a_pred, a_intro, a_axioms), (b_pred, b_intro, b_axioms), thy'''') end;

end;


local

fun assumes_to_notes (Assumes asms) axms =
      fold_map (fn (a, spec) => fn axs =>
          let val (ps, qs) = chop (length spec) axs
          in ((a, [(ps, [])]), qs) end) asms axms
      |> apfst (curry Notes Thm.assumptionK)
  | assumes_to_notes e axms = (e, axms);

fun defines_to_notes thy (Defines defs) =
      Notes (Thm.definitionK, map (fn (a, (def, _)) =>
        (a, [([Assumption.assume (cterm_of thy def)], [])])) defs)
  | defines_to_notes _ e = e;

fun gen_add_locale prep_decl
    bname predicate_name raw_imprt raw_body thy =
  let
    val name = Sign.full_bname thy bname;
    val _ = NewLocale.test_locale thy name andalso
      error ("Duplicate definition of locale " ^ quote name);

    val ((fixed, deps, body_elems), text as (parms, ((_, exts'), _), defs)) =
      prep_decl raw_imprt raw_body (ProofContext.init thy);
    val ((a_statement, a_intro, a_axioms), (b_statement, b_intro, b_axioms), thy') =
      define_preds predicate_name text thy;

    val extraTs = fold Term.add_tfrees exts' [] \\ fold Term.add_tfreesT (map snd parms) [];
    val _ = if null extraTs then ()
      else warning ("Additional type variable(s) in locale specification " ^ quote bname);

    val a_satisfy = Element.satisfy_morphism a_axioms;
    val b_satisfy = Element.satisfy_morphism b_axioms;

    val params = fixed @
      (body_elems |> map_filter (fn Fixes fixes => SOME fixes | _ => NONE) |> flat);
    val asm = if is_some b_statement then b_statement else a_statement;

    (* These are added immediately. *)
    val notes =
        if is_some asm
        then [(Thm.internalK, [((Binding.name (bname ^ "_" ^ axiomsN), []),
          [([Assumption.assume (cterm_of thy' (the asm))],
            [(Attrib.internal o K) NewLocale.witness_attrib])])])]
        else [];

    (* These will be added in the local theory. *)
    val notes' = body_elems |>
      map (defines_to_notes thy') |>
      map (Element.morph_ctxt a_satisfy) |>
      (fn elems => fold_map assumes_to_notes elems (map Element.conclude_witness a_axioms)) |>
      fst |>
      map (Element.morph_ctxt b_satisfy) |>
      map_filter (fn Notes notes => SOME notes | _ => NONE);

    val deps' = map (fn (l, morph) => (l, morph $> b_satisfy)) deps;

    val loc_ctxt = thy' |>
      NewLocale.register_locale bname (extraTs, params)
        (asm, rev defs) ([], [])
        (map (fn n => (n, stamp ())) notes |> rev) (map (fn d => (d, stamp ())) deps' |> rev) |>
      NewLocale.init name;

  in ((name, notes'), loc_ctxt) end;

in

val add_locale_cmd = gen_add_locale read_declaration;
val add_locale = gen_add_locale cert_declaration;

end;


(*** Interpretation ***)

(** Witnesses and goals **)

fun prep_propp propss = propss |> map (map (rpair [] o Element.mark_witness));

fun prep_result propps thmss =
  ListPair.map (fn (props, thms) => map2 Element.make_witness props thms) (propps, thmss);


(** Interpretation between locales: declaring sublocale relationships **)

local

fun gen_sublocale prep_expr intern
    raw_target expression thy =
  let
    val target = intern thy raw_target;
    val target_ctxt = NewLocale.init target thy;

    val ((propss, deps, export), goal_ctxt) = prep_expr expression target_ctxt;
    
    fun store_dep ((name, morph), thms) =
      NewLocale.add_dependency target (name, morph $> Element.satisfy_morphism thms $> export);

    fun after_qed results =
      ProofContext.theory (
        (* store dependencies *)
        fold store_dep (deps ~~ prep_result propss results) #>
        (* propagate registrations *)
        (fn thy => fold_rev (fn reg => NewLocale.activate_global_facts reg)
          (NewLocale.get_global_registrations thy) thy));
  in
    goal_ctxt |>
      Proof.theorem_i NONE after_qed (prep_propp propss) |>
      Element.refine_witness |> Seq.hd
  end;

in

fun sublocale_cmd x = gen_sublocale read_goal_expression NewLocale.intern x;
fun sublocale x = gen_sublocale cert_goal_expression (K I) x;

end;


(** Interpretation in theories **)

local

datatype goal = Reg of string * Morphism.morphism | Eqns of Attrib.binding list;

fun gen_interpretation prep_expr parse_prop prep_attr
    expression equations thy =
  let
    val ctxt = ProofContext.init thy;

    val ((propss, regs, export), expr_ctxt) = prep_expr expression ctxt;
    
    val eqns = map (parse_prop expr_ctxt o snd) equations |> Syntax.check_terms expr_ctxt;
    val eq_attns = map ((apsnd o map) (prep_attr thy) o fst) equations;
    val goal_ctxt = fold Variable.auto_fixes eqns expr_ctxt;
    val export' = Variable.export_morphism goal_ctxt expr_ctxt;

    fun store (Reg (name, morph), thms) (regs, thy) =
        let
          val thms' = map (Element.morph_witness export') thms;
          val morph' = morph $> Element.satisfy_morphism thms';
          val add = NewLocale.add_global_registration (name, (morph', export));
        in ((name, morph') :: regs, add thy) end
      | store (Eqns [], []) (regs, thy) =
        let val add = fold_rev (fn (name, morph) =>
              NewLocale.activate_global_facts (name, morph $> export)) regs;
        in (regs, add thy) end
      | store (Eqns attns, thms) (regs, thy) =
        let
          val thms' = thms |> map (Element.conclude_witness #>
            Morphism.thm (export' $> export) #>
            LocalDefs.meta_rewrite_rule (ProofContext.init thy) #>
            Drule.abs_def);
          val eq_morph =
            Morphism.term_morphism (MetaSimplifier.rewrite_term thy thms' []) $>
            Morphism.thm_morphism (MetaSimplifier.rewrite_rule thms');
          val attns' = map ((apsnd o map) (Attrib.attribute_i thy)) attns;
          val add =
            fold_rev (fn (name, morph) =>
              NewLocale.amend_global_registration eq_morph (name, morph) #>
              NewLocale.activate_global_facts (name, morph $> eq_morph $> export)) regs #>
            PureThy.note_thmss Thm.lemmaK (attns' ~~ map (fn th => [([th], [])]) thms') #>
            snd
        in (regs, add thy) end;

    fun after_qed results =
      ProofContext.theory (fn thy =>
        fold store (map Reg regs @ [Eqns eq_attns] ~~
          prep_result (propss @ [eqns]) results) ([], thy) |> snd);
  in
    goal_ctxt |>
      Proof.theorem_i NONE after_qed (prep_propp (propss @ [eqns])) |>
      Element.refine_witness |> Seq.hd
  end;

in

fun interpretation_cmd x = gen_interpretation read_goal_expression
  Syntax.parse_prop Attrib.intern_src x;
fun interpretation x = gen_interpretation cert_goal_expression (K I) (K I) x;

end;


(** Interpretation in proof contexts **)

local

fun gen_interpret prep_expr
    expression int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;

    val ((propss, regs, export), goal_ctxt) = prep_expr expression ctxt;
    
    fun store_reg ((name, morph), thms) =
      let
        val morph' = morph $> Element.satisfy_morphism thms $> export;
      in
        NewLocale.activate_local_facts (name, morph')
      end;

    fun after_qed results =
      Proof.map_context (fold store_reg (regs ~~ prep_result propss results)) #> Seq.single;
  in
    state |> Proof.map_context (K goal_ctxt) |>
      Proof.local_goal (ProofDisplay.print_results int) (K I) ProofContext.bind_propp_i
      "interpret" NONE after_qed (map (pair (Binding.empty, [])) (prep_propp propss)) |>
      Element.refine_witness |> Seq.hd
  end;

in

fun interpret_cmd x = gen_interpret read_goal_expression x;
fun interpret x = gen_interpret cert_goal_expression x;

end;

end;

