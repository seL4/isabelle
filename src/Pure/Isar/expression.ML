(*  Title:      Pure/Isar/expression.ML
    ID:         $Id$
    Author:     Clemens Ballarin, TU Muenchen

New locale development --- experimental.
*)

signature EXPRESSION =
sig
  type map
  type 'morph expr

  val empty_expr: 'morph expr

  type expression = (string * map) expr * (Name.binding * string option * mixfix) list
  type expression_i = Morphism.morphism expr * (Name.binding * typ option * mixfix) list

  (* Declaring locales *)
  val add_locale: string -> bstring -> expression -> Element.context list -> theory ->
    string * Proof.context
(*
  val add_locale_i: string -> bstring -> expression_i -> Element.context_i list -> theory ->
    string * Proof.context
*)

  (* Debugging and development *)
  val parse_expression: OuterParse.token list -> expression * OuterParse.token list
  val debug_parameters: expression -> Proof.context -> Proof.context
  val debug_context: expression -> Proof.context -> Proof.context

end;


structure Expression: EXPRESSION =
struct

datatype ctxt = datatype Element.ctxt;


(*** Expressions ***)

datatype map =
  Positional of string option list |
  Named of (string * string) list;

datatype 'morph expr = Expr of (string * 'morph) list;

type expression = (string * map) expr * (Name.binding * string option * mixfix) list;
type expression_i = Morphism.morphism expr * (Name.binding * typ option * mixfix) list;

val empty_expr = Expr [];


(** Parsing and printing **)

local

structure P = OuterParse;

val loc_keyword = P.$$$ "fixes" || P.$$$ "constrains" || P.$$$ "assumes" ||
   P.$$$ "defines" || P.$$$ "notes";
fun plus1_unless test scan =
  scan ::: Scan.repeat (P.$$$ "+" |-- Scan.unless test (P.!!! scan));

val prefix = P.name --| P.$$$ ":";
val named = P.name -- (P.$$$ "=" |-- P.term);
val position = P.maybe P.term;
val instance = P.$$$ "where" |-- P.and_list1 named >> Named ||
  Scan.repeat1 position >> Positional;

in

val parse_expression =
  let
    fun expr2 x = P.xname x;
    fun expr1 x = (Scan.optional prefix "" -- expr2 --
      Scan.optional instance (Named []) >> (fn ((p, l), i) => (l, (p, i)))) x;
    fun expr0 x = (plus1_unless loc_keyword expr1 >> Expr) x;
  in expr0 -- P.for_fixes end;

end;

fun pretty_expr thy (Expr expr) =
  let
    fun pretty_pos NONE = Pretty.str "_"
      | pretty_pos (SOME x) = Pretty.str x;
    fun pretty_named (x, y) = [Pretty.str x, Pretty.brk 1, Pretty.str "=",
          Pretty.brk 1, Pretty.str y] |> Pretty.block;
    fun pretty_ren (Positional ps) = take_suffix is_none ps |> snd |>
          map pretty_pos |> Pretty.breaks
      | pretty_ren (Named []) = []
      | pretty_ren (Named ps) = Pretty.str "where" :: Pretty.brk 1 ::
          (ps |> map pretty_named |> Pretty.separate "and");
    fun pretty_rename (loc, ("", ren)) =
          Pretty.block (Pretty.str (NewLocale.extern thy loc) :: Pretty.brk 1 :: pretty_ren ren) 
      | pretty_rename (loc, (prfx, ren)) =
          Pretty.block (Pretty.str prfx :: Pretty.brk 1 :: Pretty.str (NewLocale.extern thy loc) ::
            Pretty.brk 1 :: pretty_ren ren);
  in Pretty.separate "+" (map pretty_rename expr) |> Pretty.block end;

fun err_in_expr thy msg (Expr expr) =
  let
    val err_msg =
      if null expr then msg
      else msg ^ "\n" ^ Pretty.string_of (Pretty.block
        [Pretty.str "The above error(s) occurred in expression:", Pretty.brk 1,
          pretty_expr thy (Expr expr)])
  in error err_msg end;


(** Internalise locale names in expr **)

fun intern thy (Expr instances) = Expr (map (apfst (NewLocale.intern thy)) instances);


(** Parameters of expression.
   Sanity check of instantiations.
   Positional instantiations are extended to match full length of parameter list. **)

fun parameters_of thy (expr, fixed) =
  let
    fun reject_dups message xs =
      let val dups = duplicates (op =) xs
      in
        if null dups then () else error (message ^ commas dups)
      end;

    fun match_bind (n, b) = (n = Name.name_of b);
    fun bind_eq (b1, b2) = (Name.name_of b1 = Name.name_of b2);
      (* FIXME: cannot compare bindings for equality. *)

    fun params_loc loc =
          (NewLocale.params_of thy loc |> map (fn (p, _, mx) => (p, mx)), loc);
    fun params_inst (expr as (loc, (prfx, Positional insts))) =
          let
            val (ps, loc') = params_loc loc;
	    val d = length ps - length insts;
	    val insts' =
	      if d < 0 then err_in_expr thy "More arguments than parameters in instantiation."
                (Expr [expr])
	      else insts @ replicate d NONE;
            val ps' = (ps ~~ insts') |>
              map_filter (fn (p, NONE) => SOME p | (_, SOME _) => NONE);
          in
            (ps', (loc', (prfx, Positional insts')))
          end
      | params_inst (expr as (loc, (prfx, Named insts))) =
          let
            val _ = reject_dups "Duplicate instantiation of the following parameter(s): "
              (map fst insts);

            val (ps, loc') = params_loc loc;
            val ps' = fold (fn (p, _) => fn ps =>
              if AList.defined match_bind ps p then AList.delete match_bind p ps
              else error (quote p ^" not a parameter of instantiated expression.")) insts ps;
          in
            (ps', (loc', (prfx, Named insts)))
          end;
    fun params_expr (Expr is) =
          let
            val (is', ps') = fold_map (fn i => fn ps =>
              let
                val (ps', i') = params_inst i;
                val ps'' = AList.join bind_eq (fn p => fn (mx1, mx2) =>
                  (* FIXME: should check for bindings being the same.
                     Instead we check for equal name and syntax. *)
                  if mx1 = mx2 then mx1
                  else error ("Conflicting syntax for parameter" ^ quote (Name.name_of p) ^
                    " in expression.")) (ps, ps')
              in (i', ps'') end) is []
          in
            (ps', Expr is')
          end;

    val (parms, expr') = params_expr expr;

    val parms' = map (#1 #> Name.name_of) parms;
    val fixed' = map (#1 #> Name.name_of) fixed;
    val _ = reject_dups "Duplicate fixed parameter(s): " fixed';
    val _ = reject_dups "Parameter(s) declared simultaneously in expression and for clause: " (parms' @ fixed');

  in (expr', (map (fn (b, mx) => (b, NONE, mx)) parms @ fixed)) end;


(** Read instantiation **)

local

fun prep_inst parse_term parms (prfx, insts) ctxt =
  let
    (* parameters *)
    val (parm_names, parm_types) = split_list parms;
    val type_parm_names = fold Term.add_tfreesT parm_types [] |> map fst;

    (* parameter instantiations *)
    val insts' = case insts of
      Positional insts => (insts ~~ parm_names) |> map (fn
        (NONE, p) => parse_term ctxt p |
        (SOME t, _) => parse_term ctxt t) |
      Named insts => parm_names |> map (fn
        p => case AList.lookup (op =) insts p of
          SOME t => parse_term ctxt t |
          NONE => parse_term ctxt p);

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
      Morphism.name_morphism (Name.qualified prfx), ctxt')
  end;

in

fun read_inst x = prep_inst Syntax.parse_term x;
(* fun cert_inst x = prep_inst (K I) x; *)

end;

        
(** Test code **)
  
fun debug_parameters raw_expr ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val expr = apfst (intern thy) raw_expr;
    val (expr', fixed) = parameters_of thy expr;
  in ctxt end;


fun debug_context (raw_expr, fixed) ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val expr = intern thy raw_expr;
    val (expr', fixed) = parameters_of thy (expr, fixed);

    fun declare_parameters fixed ctxt =
      let
      val (fixed', ctxt') = ProofContext.add_fixes fixed ctxt;
      in
        (fixed', ctxt')
      end;

    fun rough_inst loc prfx insts ctxt =
      let
        (* locale data *)
        val (parm_names, parm_types) = loc |> NewLocale.params_of thy |>
          map (fn (b, SOME T, _) => (Name.name_of b, T)) |> split_list;

        (* type parameters *)
        val type_parm_names = fold Term.add_tfreesT parm_types [] |> map fst;

        (* parameter instantiations *)
        val insts' = case insts of
          Positional insts => (insts ~~ parm_names) |> map (fn
            (NONE, p) => Syntax.parse_term ctxt p |
            (SOME t, _) => Syntax.parse_term ctxt t) |
          Named insts => parm_names |> map (fn
            p => case AList.lookup (op =) insts p of
              SOME t => Syntax.parse_term ctxt t |
              NONE => Syntax.parse_term ctxt p);

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
        (Element.inst_morphism thy (instT, inst) $>
          Morphism.name_morphism (Name.qualified prfx), ctxt')
      end;

    fun add_declarations loc morph ctxt =
      let
        (* locale data *)
        val parms = loc |> NewLocale.params_of thy |>
          map (fn (b, SOME T, mx) => ((Name.name_of b, T), mx));
        val (typ_decls, term_decls) = NewLocale.declarations_of thy loc;

        (* declarations from locale *)
	val ctxt'' = ctxt |>
	  fold_rev (fn decl => Context.proof_map (decl morph)) typ_decls |>
	  fold_rev (fn decl => Context.proof_map (decl morph)) term_decls;
      in
        ctxt''
      end;

    val Expr [(loc1, (prfx1, insts1))] = expr';
    val ctxt0 = ProofContext.init thy;
    val (parms, ctxt') = declare_parameters fixed ctxt0;
    val (morph1, ctxt'') = rough_inst loc1 prfx1 insts1 ctxt';
    val ctxt'' = add_declarations loc1 morph1 ctxt';
  in ctxt0 end;


(*** Locale processing ***)

(** Parsing **)

fun parse_elem prep_typ prep_term ctxt elem =
  Element.map_ctxt {name = I, var = I, typ = prep_typ ctxt,
    term = prep_term ctxt, fact = I, attrib = I} elem;

fun parse_concl prep_term ctxt concl =
  (map o map) (fn (t, ps) =>
    (prep_term ctxt, map (prep_term ctxt) ps)) concl;


(** Type checking **)

fun extract_elem (Fixes fixes) = map (#2 #> the_list #> map (Logic.mk_type #> rpair [])) fixes
  | extract_elem (Constrains csts) = map (#2 #> single #> map (Logic.mk_type #> rpair [])) csts
  | extract_elem (Assumes asms) = map #2 asms
  | extract_elem (Defines defs) = map (fn (_, (t, ps)) => [(t, ps)]) defs
  | extract_elem (Notes _) = [];

fun restore_elem (Fixes fixes, propps) =
      (fixes ~~ propps) |> map (fn ((x, _, mx), propp) =>
        (x, propp |> map (fst #> Logic.dest_type) |> try hd, mx)) |> Fixes
  | restore_elem (Constrains csts, propps) =
      (csts ~~ propps) |> map (fn ((x, _), propp) =>
        (x, propp |> map (fst #> Logic.dest_type) |> hd)) |> Constrains
  | restore_elem (Assumes asms, propps) =
      (asms ~~ propps) |> map (fn ((b, _), propp) => (b, propp)) |> Assumes
  | restore_elem (Defines defs, propps) =
      (defs ~~ propps) |> map (fn ((b, _), [propp]) => (b, propp)) |> Defines
  | restore_elem (Notes notes, _) = Notes notes;

fun check_autofix_elems elems concl ctxt =
  let
    val termss = elems |> map extract_elem;
    val all_terms' = (burrow o burrow_fst) (Syntax.check_terms ctxt) (concl @ flat termss); 
(*    val (ctxt', all_props') = ProofContext.check_propp_schematic (ctxt, concl @ flat propss); *)
    val (concl', terms') = chop (length concl) all_terms';
    val ctxt'' = (fold o fold) (fn (t, _) => Variable.auto_fixes t) terms' ctxt;
  in (terms' |> unflat termss |> curry (op ~~) elems |> map restore_elem, concl', ctxt'') end;


(** Prepare locale elements **)

fun declare_elem prep_vars (Fixes fixes) ctxt =
      let val (vars, _) = prep_vars fixes ctxt
      in ctxt |> ProofContext.add_fixes_i vars |> snd end
  | declare_elem prep_vars (Constrains csts) ctxt =
      ctxt |> prep_vars (map (fn (x, T) => (Name.binding x, SOME T, NoSyn)) csts) |> snd
  | declare_elem _ (Assumes asms) ctxt = ctxt
  | declare_elem _ (Defines defs) ctxt = ctxt
  | declare_elem _ (Notes _) ctxt = ctxt;

(** Finish locale elements, extract specification text **)

local

val norm_term = Envir.beta_norm oo Term.subst_atomic;

fun abstract_thm thy eq =
  Thm.assume (Thm.cterm_of thy eq) |> Drule.gen_all |> Drule.abs_def;

fun bind_def ctxt eq (xs, env, ths) =
  let
    val ((y, T), b) = LocalDefs.abs_def eq;
    val b' = norm_term env b;
    val th = abstract_thm (ProofContext.theory_of ctxt) eq;
    fun err msg = error (msg ^ ": " ^ quote y);
  in
    exists (fn (x, _) => x = y) xs andalso
      err "Attempt to define previously specified variable";
    exists (fn (Free (y', _), _) => y = y' | _ => false) env andalso
      err "Attempt to redefine variable";
    (Term.add_frees b' xs, (Free (y, T), b') :: env, th :: ths)
  end;

fun eval_text _ (Fixes _) text = text
  | eval_text _ (Constrains _) text = text
  | eval_text _ (Assumes asms)
        (((exts, exts'), (ints, ints')), (xs, env, defs)) =
      let
        val ts = maps (map #1 o #2) asms;
        val ts' = map (norm_term env) ts;
        val spec' = ((exts @ ts, exts' @ ts'), (ints, ints'));
      in (spec', (fold Term.add_frees ts' xs, env, defs)) end
  | eval_text ctxt (Defines defs) (spec, binds) =
      (spec, fold (bind_def ctxt o #1 o #2) defs binds)
  | eval_text _ (Notes _) text = text;

fun closeup _ _ false elem = elem
  | closeup ctxt parms true elem =
      let
        fun close_frees t =
          let
            val rev_frees =
              Term.fold_aterms (fn Free (x, T) =>
                if AList.defined (op =) parms x then I else insert (op =) (x, T) | _ => I) t [];
          in Term.list_all_free (rev rev_frees, t) end;

        fun no_binds [] = []
          | no_binds _ = error "Illegal term bindings in context element";
      in
        (case elem of
          Assumes asms => Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, ps) => (close_frees t, no_binds ps)) propps)))
        | Defines defs => Defines (defs |> map (fn (a, (t, ps)) =>
            (a, (close_frees (#2 (LocalDefs.cert_def ctxt t)), no_binds ps))))
        | e => e)
      end;

fun finish_ext_elem parms _ (Fixes fixes) = Fixes (map (fn (binding, _, mx) =>
      let val x = Name.name_of binding
      in (binding, AList.lookup (op =) parms x, mx) end) fixes)
  | finish_ext_elem _ _ (Constrains _) = Constrains []
  | finish_ext_elem _ close (Assumes asms) = close (Assumes asms)
  | finish_ext_elem _ close (Defines defs) = close (Defines defs)
  | finish_ext_elem _ _ (Notes facts) = Notes facts;

fun finish_elem ctxt parms do_close elem text =
  let
    val elem' = finish_ext_elem parms (closeup ctxt parms do_close) elem;
    val text' = eval_text ctxt elem' text;
  in (elem', text') end
  
in

fun finish_elems ctxt parms do_close elems text =
  fold_map (finish_elem ctxt parms do_close) elems text;

end;


local

(* nice, but for now not needed
fun fold_suffixes f [] y = f [] y
  | fold_suffixes f (x :: xs) y = f (x :: xs) (f xs y);

fun fold_prefixes f xs y = fold_suffixes (f o rev) (rev xs) y;
*)

fun prep_elems parse_typ parse_prop prep_vars do_close context raw_elems raw_concl =
  let
    fun prep_elem raw_elem (elems, ctxt) =
      let
        val ctxt' = declare_elem prep_vars raw_elem ctxt;
        val elems' = elems @ [parse_elem parse_typ parse_prop ctxt' raw_elem];
        (* FIXME term bindings *)
        val (_, _, ctxt'') = check_autofix_elems elems' [] ctxt';
      in (elems', ctxt'') end;

    fun prep_concl raw_concl (elems, ctxt) =
      let
        val concl = (map o map) (fn (t, ps) =>
          (parse_prop ctxt t, map (parse_prop ctxt) ps)) raw_concl;
      in check_autofix_elems elems concl ctxt end;

    val (elems, concl, ctxt) = fold prep_elem raw_elems ([], context) |>
      prep_concl raw_concl;

    (* Retrieve parameter types *) 
    val xs = fold (fn Fixes fixes => (fn ps => ps @ map (Name.name_of o #1) fixes) |
      _ => fn ps => ps) elems [];
    val (Ts, ctxt') = fold_map ProofContext.inferred_param xs ctxt; 
    val parms = xs ~~ Ts;

    val (elems', text) = finish_elems ctxt' parms do_close elems ((([], []), ([], [])), ([], [], []));
    (* text has the following structure:
           (((exts, exts'), (ints, ints')), (xs, env, defs))
       where
         exts: external assumptions (terms in external assumes elements)
         exts': dito, normalised wrt. env
         ints: internal assumptions (terms in internal assumes elements)
         ints': dito, normalised wrt. env
         xs: the free variables in exts' and ints' and rhss of definitions,
           this includes parameters except defined parameters
         env: list of term pairs encoding substitutions, where the first term
           is a free variable; substitutions represent defines elements and
           the rhs is normalised wrt. the previous env
         defs: theorems representing the substitutions from defines elements
           (thms are normalised wrt. env).
       elems is an updated version of raw_elems:
         - type info added to Fixes and modified in Constrains
         - axiom and definition statement replaced by corresponding one
           from proppss in Assumes and Defines
         - Facts unchanged
       *)

  in ((parms, elems', concl), text) end

in

fun read_elems x = prep_elems Syntax.parse_typ Syntax.parse_prop ProofContext.read_vars x;
fun cert_elems x = prep_elems (K I) (K I) ProofContext.cert_vars x;

end;


(* full context statements: import + elements + conclusion *)

local

fun prep_context_statement prep_expr prep_elems
    do_close imprt elements raw_concl context =
  let
    val thy = ProofContext.theory_of context;

    val (expr, fixed) = parameters_of thy (apfst (prep_expr thy) imprt);
    val ctxt = context |> ProofContext.add_fixes fixed |> snd;
  in
    case expr of
        Expr [] => let
          val ((parms, elems, concl), (spec, (_, _, defs))) = prep_elems do_close
            context elements raw_concl;
          val ((elems', _), ctxt') =
            Element.activate elems (ProofContext.set_stmt true ctxt);
        in
          (((ctxt', elems'), (parms, spec, defs)), concl)
        end
(*
        | Expr [(name, insts)] => let
          val parms = parameters_of thy name |> map (fn (b, SOME T, _) => (Name.name_of b, T));
          val (morph, ctxt') = read_inst parms insts context;
        in
          
        end
*)
end

in

fun read_context imprt body ctxt =
  #1 (prep_context_statement intern read_elems true imprt body [] ctxt);
fun cert_context imprt body ctxt =
  #1 (prep_context_statement (K I) cert_elems true imprt body [] ctxt);

end;


(** Dependencies **)



(*** Locale declarations ***)

local

(* introN: name of theorems for introduction rules of locale and
     delta predicates;
   axiomsN: name of theorem set with destruct rules for locale predicates,
     also name suffix of delta predicates. *)

val introN = "intro";
val axiomsN = "axioms";

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

(* CB: define one predicate including its intro rule and axioms
   - bname: predicate name
   - parms: locale parameters
   - defs: thms representing substitutions from defines elements
   - ts: terms representing locale assumptions (not normalised wrt. defs)
   - norm_ts: terms representing locale assumptions (normalised wrt. defs)
   - thy: the theory
*)

fun def_pred bname parms defs ts norm_ts thy =
  let
    val name = Sign.full_name thy bname;

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
      |> Sign.declare_const [] ((Name.binding bname, predT), NoSyn) |> snd
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
    val (a_pred, a_intro, a_axioms, thy'') =
      if null exts then (NONE, NONE, [], thy)
      else
        let
          val aname = if null ints then pname else pname ^ "_" ^ axiomsN;
          val ((statement, intro, axioms), thy') =
            thy
            |> def_pred aname parms defs exts exts';
          val (_, thy'') =
            thy'
            |> Sign.add_path aname
            |> Sign.no_base_names
            |> PureThy.note_thmss Thm.internalK [((Name.binding introN, []), [([intro], [])])]
            ||> Sign.restore_naming thy';
          in (SOME statement, SOME intro, axioms, thy'') end;
    val (b_pred, b_intro, b_axioms, thy'''') =
      if null ints then (NONE, NONE, [], thy'')
      else
        let
          val ((statement, intro, axioms), thy''') =
            thy''
            |> def_pred pname parms defs (ints @ the_list a_pred) (ints' @ the_list a_pred);
          val (_, thy'''') =
            thy'''
            |> Sign.add_path pname
            |> Sign.no_base_names
            |> PureThy.note_thmss Thm.internalK
                 [((Name.binding introN, []), [([intro], [])]),
                  ((Name.binding axiomsN, []),
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

fun defines_to_notes thy (Defines defs) defns =
    let
      val defs' = map (fn (_, (def, _)) => def) defs
      val notes = map (fn (a, (def, _)) =>
        (a, [([assume (cterm_of thy def)], [])])) defs
    in
      (Notes (Thm.definitionK, notes), defns @ defs')
    end
  | defines_to_notes _ e defns = (e, defns);

fun gen_add_locale prep_ctxt
    bname predicate_name raw_imprt raw_body thy =
  let
    val thy_ctxt = ProofContext.init thy;
    val name = Sign.full_name thy bname;
    val _ = NewLocale.test_locale thy name andalso
      error ("Duplicate definition of locale " ^ quote name);

    val ((body_ctxt, body_elems), text as (parms, ((_, exts'), _), defs)) =
      prep_ctxt raw_imprt raw_body thy_ctxt;
    val ((statement, intro, axioms), _, thy') =
      define_preds predicate_name text thy;

    val extraTs = fold Term.add_tfrees exts' [] \\ fold Term.add_tfreesT (map snd parms) [];
    val _ = if null extraTs then ()
      else warning ("Additional type variable(s) in locale specification " ^ quote bname);

    val params = body_elems |>
      map_filter (fn Fixes fixes => SOME fixes | _ => NONE) |> flat;

    val (body_elems', defns) = fold_map (defines_to_notes thy) body_elems [];

    val notes = body_elems' |>
      (fn elems => fold_map assumes_to_notes elems (map Element.conclude_witness axioms)) |>
      fst |>
      map_filter (fn Notes notes => SOME notes | _ => NONE);

    val loc_ctxt = thy' |>
      NewLocale.register_locale name (extraTs, params) (statement, defns) ([], [])
        (map (fn n => (n, stamp ())) notes |> rev) [] |>
      NewLocale.init name
  in (name, loc_ctxt) end;

in

val add_locale = gen_add_locale read_context;
(* val add_locale_i = gen_add_locale cert_context; *)

end;

end;
