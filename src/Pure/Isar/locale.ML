(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Markus Wenzel, LMU/TU München
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.

Draws some basic ideas from Florian Kammüller's original version of
locales, but uses the richer infrastructure of Isar instead of the raw
meta-logic.  Furthermore, we provide structured import of contexts
(with merge and rename operations), well as type-inference of the
signature parts, and predicate definitions of the specification text.
*)

signature LOCALE =
sig
  type context
  datatype ('typ, 'term, 'fact, 'att) elem =
    Fixes of (string * 'typ option * mixfix option) list |
    Assumes of ((string * 'att list) * ('term * ('term list * 'term list)) list) list |
    Defines of ((string * 'att list) * ('term * 'term list)) list |
    Notes of ((string * 'att list) * ('fact * 'att list) list) list
  datatype expr =
    Locale of string |
    Rename of expr * string option list |
    Merge of expr list
  val empty: expr
  datatype ('typ, 'term, 'fact, 'att) elem_expr =
    Elem of ('typ, 'term, 'fact, 'att) elem | Expr of expr
  type 'att element
  type 'att element_i
  type locale
  val intern: Sign.sg -> xstring -> string
  val cond_extern: Sign.sg -> string -> xstring
  val the_locale: theory -> string -> locale
  val attribute: ('att -> context attribute) -> ('typ, 'term, 'thm, 'att) elem_expr
    -> ('typ, 'term, 'thm, context attribute) elem_expr
  val read_context_statement: xstring option -> context attribute element list ->
    (string * (string list * string list)) list list -> context ->
    string option * cterm list * context * context * (term * (term list * term list)) list list
  val cert_context_statement: string option -> context attribute element_i list ->
    (term * (term list * term list)) list list -> context ->
    string option * cterm list * context * context * (term * (term list * term list)) list list
  val print_locales: theory -> unit
  val print_locale: theory -> expr -> context attribute element list -> unit
  val add_locale: bool -> bstring -> expr -> context attribute element list -> theory -> theory
  val add_locale_i: bool -> bstring -> expr -> context attribute element_i list
    -> theory -> theory
  val smart_have_thmss: string -> (string * 'a) Library.option ->
    ((bstring * theory attribute list) * (thm list * theory attribute list) list) list ->
    theory -> theory * (bstring * thm list) list
  val have_thmss: string -> xstring ->
    ((bstring * context attribute list) * (xstring * context attribute list) list) list ->
    theory -> theory * (bstring * thm list) list
  val have_thmss_i: string -> string ->
    ((bstring * context attribute list) * (thm list * context attribute list) list) list ->
    theory -> theory * (bstring * thm list) list
  val add_thmss: string -> ((string * thm list) * context attribute list) list ->
    theory * context -> (theory * context) * (string * thm list) list
  val setup: (theory -> theory) list
end;

structure Locale: LOCALE =
struct

(** locale elements and expressions **)

type context = ProofContext.context;

datatype ('typ, 'term, 'fact, 'att) elem =
  Fixes of (string * 'typ option * mixfix option) list |
  Assumes of ((string * 'att list) * ('term * ('term list * 'term list)) list) list |
  Defines of ((string * 'att list) * ('term * 'term list)) list |
  Notes of ((string * 'att list) * ('fact * 'att list) list) list;

datatype expr =
  Locale of string |
  Rename of expr * string option list |
  Merge of expr list;

val empty = Merge [];

datatype ('typ, 'term, 'fact, 'att) elem_expr =
  Elem of ('typ, 'term, 'fact, 'att) elem | Expr of expr;

type 'att element = (string, string, string, 'att) elem_expr;
type 'att element_i = (typ, term, thm list, 'att) elem_expr;

type locale =
 {view: cterm list * thm list,                            (*external view on assumptions*)
  import: expr,                                                         (*dynamic import*)
  elems: ((typ, term, thm list, context attribute) elem * stamp) list,  (*static content*)
  params: (string * typ option) list * string list};                  (*all/local params*)

fun make_locale view import elems params =
 {view = view, import = import, elems = elems, params = params}: locale;



(** theory data **)

structure LocalesArgs =
struct
  val name = "Isar/locales";
  type T = NameSpace.T * locale Symtab.table;

  val empty = (NameSpace.empty, Symtab.empty);
  val copy = I;
  val prep_ext = I;

  (*joining of locale elements: only facts may be added later!*)
  fun join ({view, import, elems, params}: locale, {elems = elems', ...}: locale) =
    Some (make_locale view import (gen_merge_lists eq_snd elems elems') params);
  fun merge ((space1, locs1), (space2, locs2)) =
    (NameSpace.merge (space1, space2), Symtab.join join (locs1, locs2));

  fun print _ (space, locs) =
    Pretty.strs ("locales:" :: map (NameSpace.cond_extern space o #1) (Symtab.dest locs))
    |> Pretty.writeln;
end;

structure LocalesData = TheoryDataFun(LocalesArgs);
val print_locales = LocalesData.print;

val intern = NameSpace.intern o #1 o LocalesData.get_sg;
val cond_extern = NameSpace.cond_extern o #1 o LocalesData.get_sg;


(* access locales *)

fun declare_locale name =
  LocalesData.map (apfst (fn space => (NameSpace.extend (space, [name]))));

fun put_locale name loc = LocalesData.map (apsnd (fn locs => Symtab.update ((name, loc), locs)));
fun get_locale thy name = Symtab.lookup (#2 (LocalesData.get thy), name);

fun the_locale thy name =
  (case get_locale thy name of
    Some loc => loc
  | None => error ("Unknown locale " ^ quote name));


(* diagnostics *)

fun err_in_locale ctxt msg ids =
  let
    val sign = ProofContext.sign_of ctxt;
    fun prt_id (name, parms) =
      [Pretty.block (Pretty.breaks (map Pretty.str (cond_extern sign name :: parms)))];
    val prt_ids = flat (separate [Pretty.str " +", Pretty.brk 1] (map prt_id ids));
    val err_msg =
      if forall (equal "" o #1) ids then msg
      else msg ^ "\n" ^ Pretty.string_of (Pretty.block
        (Pretty.str "The error(s) above occurred in locale:" :: Pretty.brk 1 :: prt_ids));
  in raise ProofContext.CONTEXT (err_msg, ctxt) end;



(** primitives **)

(* renaming *)

fun rename ren x = if_none (assoc_string (ren, x)) x;

fun rename_term ren (Free (x, T)) = Free (rename ren x, T)
  | rename_term ren (t $ u) = rename_term ren t $ rename_term ren u
  | rename_term ren (Abs (x, T, t)) = Abs (x, T, rename_term ren t)
  | rename_term _ a = a;

fun rename_thm ren th =
  let
    val {sign, hyps, prop, maxidx, ...} = Thm.rep_thm th;
    val cert = Thm.cterm_of sign;
    val (xs, Ts) = Library.split_list (foldl Term.add_frees ([], prop :: hyps));
    val xs' = map (rename ren) xs;
    fun cert_frees names = map (cert o Free) (names ~~ Ts);
    fun cert_vars names = map (cert o Var o apfst (rpair (maxidx + 1))) (names ~~ Ts);
  in
    if xs = xs' then th
    else
      th
      |> Drule.implies_intr_list (map cert hyps)
      |> Drule.forall_intr_list (cert_frees xs)
      |> Drule.forall_elim_list (cert_vars xs)
      |> Thm.instantiate ([], cert_vars xs ~~ cert_frees xs')
      |> (fn th' => Drule.implies_elim_list th' (map (Thm.assume o cert o rename_term ren) hyps))
  end;

fun rename_elem ren (Fixes fixes) = Fixes (fixes |> map (fn (x, T, mx) =>
      let val x' = rename ren x in
        if x = x' then (x, T, mx)
        else (x', T, if mx = None then mx else Some Syntax.NoSyn)    (*drop syntax*)
      end))
  | rename_elem ren (Assumes asms) = Assumes (map (apsnd (map (fn (t, (ps, qs)) =>
      (rename_term ren t, (map (rename_term ren) ps, map (rename_term ren) qs))))) asms)
  | rename_elem ren (Defines defs) = Defines (map (apsnd (fn (t, ps) =>
      (rename_term ren t, map (rename_term ren) ps))) defs)
  | rename_elem ren (Notes facts) = Notes (map (apsnd (map (apfst (map (rename_thm ren))))) facts);

fun rename_facts prfx elem =
  let
    fun qualify (arg as ((name, atts), x)) =
      if prfx = "" orelse name = "" then arg
      else ((NameSpace.pack [prfx, name], atts), x);
  in
    (case elem of
      Fixes fixes => Fixes fixes
    | Assumes asms => Assumes (map qualify asms)
    | Defines defs => Defines (map qualify defs)
    | Notes facts => Notes (map qualify facts))
  end;


(* type instantiation *)

fun inst_type [] T = T
  | inst_type env T = Term.map_type_tfree (fn v => if_none (assoc (env, v)) (TFree v)) T;

fun inst_term [] t = t
  | inst_term env t = Term.map_term_types (inst_type env) t;

fun inst_thm _ [] th = th
  | inst_thm ctxt env th =
      let
        val sign = ProofContext.sign_of ctxt;
        val cert = Thm.cterm_of sign;
        val certT = Thm.ctyp_of sign;
        val {hyps, prop, maxidx, ...} = Thm.rep_thm th;
        val tfrees = foldr Term.add_term_tfree_names (prop :: hyps, []);
        val env' = filter (fn ((a, _), _) => a mem_string tfrees) env;
      in
        if null env' then th
        else
          th
          |> Drule.implies_intr_list (map cert hyps)
          |> Drule.tvars_intr_list (map (#1 o #1) env')
          |> (fn (th', al) => th' |>
            Thm.instantiate ((map (fn ((a, _), T) => (the (assoc (al, a)), certT T)) env'), []))
          |> (fn th'' => Drule.implies_elim_list th''
              (map (Thm.assume o cert o inst_term env') hyps))
      end;

fun inst_elem _ env (Fixes fixes) =
      Fixes (map (fn (x, T, mx) => (x, apsome (inst_type env) T, mx)) fixes)
  | inst_elem _ env (Assumes asms) = Assumes (map (apsnd (map (fn (t, (ps, qs)) =>
      (inst_term env t, (map (inst_term env) ps, map (inst_term env) qs))))) asms)
  | inst_elem _ env (Defines defs) = Defines (map (apsnd (fn (t, ps) =>
      (inst_term env t, map (inst_term env) ps))) defs)
  | inst_elem ctxt env (Notes facts) =
      Notes (map (apsnd (map (apfst (map (inst_thm ctxt env))))) facts);



(** structured contexts: rename + merge + implicit type instantiation **)

(* parameter types *)

fun frozen_tvars ctxt Ts =
  let
    val tvars = rev (foldl Term.add_tvarsT ([], Ts));
    val tfrees = map TFree
      (Term.invent_type_names (ProofContext.used_types ctxt) (length tvars) ~~ map #2 tvars);
  in map #1 tvars ~~ tfrees end;

fun unify_frozen ctxt maxidx Ts Us =
  let
    val tsig = Sign.tsig_of (ProofContext.sign_of ctxt);
    fun unify (env, (Some T, Some U)) = (Type.unify tsig env (U, T)
          handle Type.TUNIFY => raise TYPE ("unify_frozen: failed to unify types", [U, T], []))
      | unify (env, _) = env;
    fun paramify (i, None) = (i, None)
      | paramify (i, Some T) = apsnd Some (Type.paramify_dummies (i, T));

    val (maxidx', Ts') = foldl_map paramify (maxidx, Ts);
    val (maxidx'', Us') = foldl_map paramify (maxidx', Us);
    val (unifier, _) = foldl unify ((Vartab.empty, maxidx''), Ts' ~~ Us');
    val Vs = map (apsome (Envir.norm_type unifier)) Us';
    val unifier' = Vartab.extend (unifier, frozen_tvars ctxt (mapfilter I Vs));
  in map (apsome (Envir.norm_type unifier')) Vs end;

fun params_of elemss = gen_distinct eq_fst (flat (map (snd o fst) elemss));
fun param_types ps = mapfilter (fn (_, None) => None | (x, Some T) => Some (x, T)) ps;


(* flatten expressions *)

local

fun unique_parms ctxt elemss =
  let
    val param_decls =
      flat (map (fn ((name, (ps, qs)), _) => map (rpair (name, ps)) qs) elemss)
      |> Symtab.make_multi |> Symtab.dest;
  in
    (case find_first (fn (_, ids) => length ids > 1) param_decls of
      Some (q, ids) => err_in_locale ctxt ("Multiple declaration of parameter " ^ quote q)
          (map (apsnd (map fst)) ids)
    | None => map (apfst (apsnd #1)) elemss)
  end;

fun unify_parms ctxt fixed_parms raw_parmss =
  let
    val tsig = Sign.tsig_of (ProofContext.sign_of ctxt);
    val maxidx = length raw_parmss;
    val idx_parmss = (0 upto maxidx - 1) ~~ raw_parmss;

    fun varify i = Term.map_type_tfree (fn (a, S) => TVar ((a, i), S));
    fun varify_parms (i, ps) = map (apsnd (varify i)) (param_types ps);
    val parms = fixed_parms @ flat (map varify_parms idx_parmss);

    fun unify T ((env, maxidx), U) = Type.unify tsig (env, maxidx) (U, T)
      handle Type.TUNIFY => raise TYPE ("unify_parms: failed to unify types", [U, T], []);
    fun unify_list (envir, T :: Us) = foldl (unify T) (envir, Us)
      | unify_list (envir, []) = envir;
    val (unifier, _) = foldl unify_list
      ((Vartab.empty, maxidx), map #2 (Symtab.dest (Symtab.make_multi parms)));

    val parms' = map (apsnd (Envir.norm_type unifier)) (gen_distinct eq_fst parms);
    val unifier' = Vartab.extend (unifier, frozen_tvars ctxt (map #2 parms'));

    fun inst_parms (i, ps) =
      foldr Term.add_typ_tfrees (mapfilter snd ps, [])
      |> mapfilter (fn (a, S) =>
          let val T = Envir.norm_type unifier' (TVar ((a, i), S))
          in if T = TFree (a, S) then None else Some ((a, S), T) end);
  in map inst_parms idx_parmss end;

in

fun unify_elemss _ _ [] = []
  | unify_elemss _ [] [elems] = [elems]
  | unify_elemss ctxt fixed_parms elemss =
      let
        val envs = unify_parms ctxt fixed_parms (map (#2 o #1) elemss);
        fun inst (((name, ps), elems), env) =
          ((name, map (apsnd (apsome (inst_type env))) ps), (map (inst_elem ctxt env) elems));
      in map inst (elemss ~~ envs) end;

fun flatten_expr ctxt (prev_idents, expr) =
  let
    val thy = ProofContext.theory_of ctxt;

    fun renaming (Some x :: xs) (y :: ys) = (y, x) :: renaming xs ys
      | renaming (None :: xs) (y :: ys) = renaming xs ys
      | renaming [] _ = []
      | renaming xs [] = raise ERROR_MESSAGE ("Too many arguments in renaming: " ^
          commas (map (fn None => "_" | Some x => quote x) xs));

    fun rename_parms ren (name, ps) =
      let val ps' = map (rename ren) ps in
        (case duplicates ps' of [] => (name, ps')
        | dups => err_in_locale ctxt ("Duplicate parameters: " ^ commas_quote dups) [(name, ps')])
      end;

    fun identify ((ids, parms), Locale name) =
          let
            val {import, params, ...} = the_locale thy name;
            val ps = map #1 (#1 params);
          in
            if (name, ps) mem ids then (ids, parms)
            else
              let val (ids', parms') = identify ((ids, parms), import);  (*acyclic dependencies!*)
              in (ids' @ [(name, ps)], merge_lists parms' ps) end
          end
      | identify ((ids, parms), Rename (e, xs)) =
          let
            val (ids', parms') = identify (([], []), e);
            val ren = renaming xs parms'
              handle ERROR_MESSAGE msg => err_in_locale ctxt msg ids';
            val ids'' = distinct (map (rename_parms ren) ids');
            val parms'' = distinct (flat (map #2 ids''));
          in (merge_lists ids ids'', merge_lists parms parms'') end
      | identify (arg, Merge es) = foldl identify (arg, es);

    fun eval (name, xs) =
      let
        val {params = (ps, qs), elems, ...} = the_locale thy name;
        val ren = filter_out (op =) (map #1 ps ~~ xs);
        val (params', elems') =
          if null ren then ((ps, qs), map #1 elems)
          else ((map (apfst (rename ren)) ps, map (rename ren) qs),
            map (rename_elem ren o #1) elems);
        val elems'' = map (rename_facts (space_implode "_" xs)) elems';
      in ((name, params'), elems'') end;

    val idents = gen_rems (op =) (#1 (identify (([], []), expr)), prev_idents);
    val raw_elemss = unique_parms ctxt (map eval idents);
    val elemss = unify_elemss ctxt [] raw_elemss;
  in (prev_idents @ idents, elemss) end;

end;


(* activate elements *)

local

fun export_axioms axs _ hyps th =
  th |> Drule.satisfy_hyps axs
  |> Drule.implies_intr_list (Library.drop (length axs, hyps))
  |> Seq.single;

fun activate_elem _ ((ctxt, axs), Fixes fixes) = ((ctxt |> ProofContext.add_fixes fixes, axs), [])
  | activate_elem _ ((ctxt, axs), Assumes asms) =
      let
        val ts = flat (map (map #1 o #2) asms);
        val n = length ts;
        val (ctxt', _) =
          ctxt |> ProofContext.fix_frees ts
          |> ProofContext.assume_i (export_axioms (Library.take (n, axs))) asms;
      in ((ctxt', Library.drop (n, axs)), []) end
  | activate_elem _ ((ctxt, axs), Defines defs) =
      let val (ctxt', _) =
        ctxt |> ProofContext.assume_i ProofContext.export_def
          (defs |> map (fn ((name, atts), (t, ps)) =>
            let val (c, t') = ProofContext.cert_def ctxt t
            in ((if name = "" then Thm.def_name c else name, atts), [(t', (ps, []))]) end))
      in ((ctxt', axs), []) end
  | activate_elem is_ext ((ctxt, axs), Notes facts) =
      let val (ctxt', res) = ctxt |> ProofContext.have_thmss_i facts
      in ((ctxt', axs), if is_ext then res else []) end;

fun activate_elems ((name, ps), elems) (ctxt, axs) =
  let val ((ctxt', axs'), res) =
    foldl_map (activate_elem (name = "")) ((ProofContext.qualified true ctxt, axs), elems)
      handle ProofContext.CONTEXT (msg, ctxt) => err_in_locale ctxt msg [(name, map fst ps)]
  in ((ProofContext.restore_qualified ctxt ctxt', axs'), res) end;

fun activate_elemss prep_facts = foldl_map (fn ((ctxt, axs), ((name, ps), raw_elems)) =>
  let
    val elems = map (prep_facts ctxt) raw_elems;
    val ((ctxt', axs'), res) = apsnd flat (activate_elems ((name, ps), elems) (ctxt, axs));
  in ((ctxt', axs'), (((name, ps), elems), res)) end);

in

fun activate_facts prep_facts arg =
  apsnd (apsnd flat o Library.split_list) (activate_elemss prep_facts arg);

end;



(** prepare context elements **)

(* expressions *)

fun intern_expr sg (Locale xname) = Locale (intern sg xname)
  | intern_expr sg (Merge exprs) = Merge (map (intern_expr sg) exprs)
  | intern_expr sg (Rename (expr, xs)) = Rename (intern_expr sg expr, xs);


(* attributes *)

local fun read_att attrib (x, srcs) = (x, map attrib srcs) in

fun attribute _ (Elem (Fixes fixes)) = Elem (Fixes fixes)
  | attribute attrib (Elem (Assumes asms)) = Elem (Assumes (map (apfst (read_att attrib)) asms))
  | attribute attrib (Elem (Defines defs)) = Elem (Defines (map (apfst (read_att attrib)) defs))
  | attribute attrib (Elem (Notes facts)) =
      Elem (Notes (map (apfst (read_att attrib) o apsnd (map (read_att attrib))) facts))
  | attribute _ (Expr expr) = Expr expr;

end;


(* parameters *)

local

fun prep_fixes prep_vars ctxt fixes =
  let val vars = snd (foldl_map prep_vars (ctxt, map (fn (x, T, _) => ([x], T)) fixes))
  in map (fn (([x'], T'), (_, _, mx)) => (x', T', mx)) (vars ~~ fixes) end;

in

fun read_fixes x = prep_fixes ProofContext.read_vars x;
fun cert_fixes x = prep_fixes ProofContext.cert_vars x;

end;


(* propositions and bindings *)

datatype ('a, 'b) int_ext = Int of 'a | Ext of 'b;

local

local

fun declare_int_elem (ctxt, Fixes fixes) =
      (ctxt |> ProofContext.add_fixes (map (fn (x, T, mx) =>
        (x, apsome (Term.map_type_tfree (Type.param 0)) T, mx)) fixes), [])
  | declare_int_elem (ctxt, _) = (ctxt, []);

fun declare_ext_elem prep_fixes (ctxt, Fixes fixes) =
      (ctxt |> ProofContext.add_fixes (prep_fixes ctxt fixes), [])
  | declare_ext_elem _ (ctxt, Assumes asms) = (ctxt, map #2 asms)
  | declare_ext_elem _ (ctxt, Defines defs) = (ctxt, map (fn (_, (t, ps)) => [(t, (ps, []))]) defs)
  | declare_ext_elem _ (ctxt, Notes facts) = (ctxt, []);

fun declare_elems prep_fixes (ctxt, ((name, ps), elems)) =
  let val (ctxt', propps) =
    (case elems of
      Int es => foldl_map declare_int_elem (ctxt, es)
    | Ext e => foldl_map (declare_ext_elem prep_fixes) (ctxt, [e]))
    handle ProofContext.CONTEXT (msg, ctxt) => err_in_locale ctxt msg [(name, map fst ps)]
  in (ctxt', propps) end;

in

fun declare_elemss prep_fixes fixed_params raw_elemss ctxt =
  let
    val int_elemss =
      raw_elemss
      |> mapfilter (fn (id, Int es) => Some (id, es) | _ => None)
      |> unify_elemss ctxt fixed_params;
    val (_, raw_elemss') =
      foldl_map (fn ((_, es) :: elemss, (id, Int _)) => (elemss, (id, Int es)) | x => x)
        (int_elemss, raw_elemss);
  in foldl_map (declare_elems prep_fixes) (ctxt, raw_elemss') end;

end;

local

val norm_term = Envir.beta_norm oo Term.subst_atomic;

fun abstract_term eq =    (*assumes well-formedness according to ProofContext.cert_def*)
  let
    val body = Term.strip_all_body eq;
    val vars = map Free (Term.rename_wrt_term body (Term.strip_all_vars eq));
    val (lhs, rhs) = Logic.dest_equals (Term.subst_bounds (vars, body));
    val (f, xs) = Term.strip_comb lhs;
    val eq' = Term.list_abs_free (map Term.dest_Free xs, rhs);
  in (Term.dest_Free f, eq') end;

fun abstract_thm sign eq =
  Thm.assume (Thm.cterm_of sign eq) |> Drule.gen_all |> Drule.abs_def;

fun bind_def ctxt (name, ps) ((xs, env, ths), eq) =
  let
    val ((y, T), b) = abstract_term eq;
    val b' = norm_term env b;
    val th = abstract_thm (ProofContext.sign_of ctxt) eq;
    fun err msg = err_in_locale ctxt (msg ^ ": " ^ quote y) [(name, map fst ps)];
  in
    conditional (exists (equal y o #1) xs) (fn () =>
      err "Attempt to define previously specified variable");
    conditional (exists (fn (Free (y', _), _) => y = y' | _ => false) env) (fn () =>
      err "Attempt to redefine variable");
    (Term.add_frees (xs, b'), (Free (y, T), b') :: env, th :: ths)
  end;

fun eval_text _ _ _ (text, Fixes _) = text
  | eval_text _ _ is_ext ((((exts, exts'), (ints, ints')), (xs, env, defs)), Assumes asms) =
      let
        val ts = flat (map (map #1 o #2) asms);
        val ts' = map (norm_term env) ts;
        val spec' =
          if is_ext then ((exts @ ts, exts' @ ts'), (ints, ints'))
          else ((exts, exts'), (ints @ ts, ints' @ ts'));
      in (spec', (foldl Term.add_frees (xs, ts'), env, defs)) end
  | eval_text ctxt id _ ((spec, binds), Defines defs) =
      (spec, foldl (bind_def ctxt id) (binds, map (#1 o #2) defs))
  | eval_text _ _ _ (text, Notes _) = text;

fun closeup _ false elem = elem
  | closeup ctxt true elem =
      let
        fun close_frees t =
          let val frees = rev (filter_out (ProofContext.is_fixed ctxt o #1)
            (Term.add_frees ([], t)))
          in Term.list_all_free (frees, t) end;

        fun no_binds [] = []
          | no_binds _ =
              raise ProofContext.CONTEXT ("Illegal term bindings in locale element", ctxt);
      in
        (case elem of
          Assumes asms => Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, (ps, qs)) => (close_frees t, (no_binds ps, no_binds qs))) propps)))
        | Defines defs => Defines (defs |> map (fn (a, (t, ps)) =>
            (a, (close_frees (#2 (ProofContext.cert_def ctxt t)), no_binds ps))))
        | e => e)
      end;


fun finish_ext_elem parms _ (Fixes fixes, _) = Fixes (map (fn (x, _, mx) =>
      (x, assoc_string (parms, x), mx)) fixes)
  | finish_ext_elem _ close (Assumes asms, propp) =
      close (Assumes (map #1 asms ~~ propp))
  | finish_ext_elem _ close (Defines defs, propp) =
      close (Defines (map #1 defs ~~ map (fn [(t, (ps, []))] => (t, ps)) propp))
  | finish_ext_elem _ _ (Notes facts, _) = Notes facts;

fun finish_parms parms ((name, ps), elems) =
  ((name, map (fn (x, _) => (x, assoc (parms, x))) ps), elems);

fun finish_elems ctxt parms _ (text, ((id, Int e), _)) =
      let
        val [(_, es)] = unify_elemss ctxt parms [(id, e)];
        val text' = foldl (eval_text ctxt id false) (text, es);
      in (text', (id, map Int es)) end
  | finish_elems ctxt parms do_close (text, ((id, Ext e), [propp])) =
      let
        val e' = finish_ext_elem parms (closeup ctxt do_close) (e, propp);
        val text' = eval_text ctxt id true (text, e');
      in (text', (id, [Ext e'])) end;

in

fun finish_elemss ctxt parms do_close =
  foldl_map (apsnd (finish_parms parms) o finish_elems ctxt parms do_close);

end;

fun prep_elemss prep_fixes prepp do_close context fixed_params raw_elemss raw_concl =
  let
    val (raw_ctxt, raw_proppss) = declare_elemss prep_fixes fixed_params raw_elemss context;
    val raw_propps = map flat raw_proppss;
    val raw_propp = flat raw_propps;
    val (ctxt, all_propp) =
      prepp (ProofContext.declare_terms (map Free fixed_params) raw_ctxt, raw_concl @ raw_propp);
    val ctxt = ProofContext.declare_terms (flat (map (map fst) all_propp)) ctxt;

    val all_propp' = map2 (op ~~)
      (#1 (#2 (ProofContext.bind_propp_schematic_i (ctxt, all_propp))), map (map snd) all_propp);
    val n = length raw_concl;
    val concl = Library.take (n, all_propp');
    val propp = Library.drop (n, all_propp');
    val propps = unflat raw_propps propp;
    val proppss = map (uncurry unflat) (raw_proppss ~~ propps);

    val xs = map #1 (params_of raw_elemss);
    val typing = unify_frozen ctxt 0
      (map (ProofContext.default_type raw_ctxt) xs)
      (map (ProofContext.default_type ctxt) xs);
    val parms = param_types (xs ~~ typing);

    val (text, elemss) = finish_elemss ctxt parms do_close
      (((([], []), ([], [])), ([], [], [])), raw_elemss ~~ proppss);
  in ((parms, elemss, concl), text) end;

in

fun read_elemss x = prep_elemss read_fixes ProofContext.read_propp_schematic x;
fun cert_elemss x = prep_elemss cert_fixes ProofContext.cert_propp_schematic x;

end;


(* facts *)

local

fun prep_name ctxt (name, atts) =
  if NameSpace.is_qualified name then
    raise ProofContext.CONTEXT ("Illegal qualified name: " ^ quote name, ctxt)
  else (name, atts);

fun prep_facts _ _ (Int elem) = elem
  | prep_facts _ _ (Ext (Fixes fixes)) = Fixes fixes
  | prep_facts _ ctxt (Ext (Assumes asms)) = Assumes (map (apfst (prep_name ctxt)) asms)
  | prep_facts _ ctxt (Ext (Defines defs)) = Defines (map (apfst (prep_name ctxt)) defs)
  | prep_facts get ctxt (Ext (Notes facts)) = Notes (facts |> map (fn (a, bs) =>
      (prep_name ctxt a, map (apfst (get ctxt)) bs)));

in

fun get_facts x = prep_facts ProofContext.get_thms x;
fun get_facts_i x = prep_facts (K I) x;

end;


(* full context statements: import + elements + conclusion *)

local

fun prep_context_statement prep_expr prep_elemss prep_facts
    do_close axioms fixed_params import elements raw_concl context =
  let
    val sign = ProofContext.sign_of context;

    fun flatten (ids, Elem (Fixes fixes)) =
          (ids, [(("", map (rpair None o #1) fixes), Ext (Fixes fixes))])
      | flatten (ids, Elem elem) = (ids, [(("", []), Ext elem)])
      | flatten (ids, Expr expr) =
          apsnd (map (apsnd Int)) (flatten_expr context (ids, prep_expr sign expr));

    val (import_ids, raw_import_elemss) = flatten ([], Expr import);
    val raw_elemss = flat (#2 ((foldl_map flatten (import_ids, elements))));
    val ((parms, all_elemss, concl), (spec, (_, _, defs))) = prep_elemss do_close
      context fixed_params (raw_import_elemss @ raw_elemss) raw_concl;

    val n = length raw_import_elemss;
    val ((import_ctxt, axioms'), (import_elemss, _)) =
      activate_facts prep_facts ((context, axioms), Library.take (n, all_elemss));
    val ((ctxt, _), (elemss, _)) =
      activate_facts prep_facts ((import_ctxt, axioms'), Library.drop (n, all_elemss));
  in
    ((((import_ctxt, import_elemss), (ctxt, elemss)), (parms, spec, defs)), concl)
  end;

val gen_context = prep_context_statement intern_expr read_elemss get_facts;
val gen_context_i = prep_context_statement (K I) cert_elemss get_facts_i;

fun gen_statement prep_locale prep_ctxt raw_locale elems concl ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val locale = apsome (prep_locale (Theory.sign_of thy)) raw_locale;
    val ((view_statement, view_axioms), fixed_params, import) =
      (case locale of None => (([], []), [], empty)
      | Some name =>
          let val {view, params = (ps, _), ...} = the_locale thy name
          in (view, param_types ps, Locale name) end);
    val ((((locale_ctxt, _), (elems_ctxt, _)), _), concl') =
      prep_ctxt false view_axioms fixed_params import elems concl ctxt;
  in (locale, view_statement, locale_ctxt, elems_ctxt, concl') end;

in

fun read_context x y z = #1 (gen_context true [] [] x y [] z);
fun cert_context x y z = #1 (gen_context_i true [] [] x y [] z);
val read_context_statement = gen_statement intern gen_context;
val cert_context_statement = gen_statement (K I) gen_context_i;

end;



(** define locales **)

(* print locale *)

fun print_locale thy import body =
  let
    val thy_ctxt = ProofContext.init thy;
    val (((_, import_elemss), (ctxt, elemss)), _) = read_context import body thy_ctxt;
    val all_elems = flat (map #2 (import_elemss @ elemss));

    val prt_typ = Pretty.quote o ProofContext.pretty_typ ctxt;
    val prt_term = Pretty.quote o ProofContext.pretty_term ctxt;
    val prt_thm = Pretty.quote o ProofContext.pretty_thm ctxt;

    fun prt_syn syn =
      let val s = (case syn of None => "(structure)" | Some mx => Syntax.string_of_mixfix mx)
      in if s = "" then [] else [Pretty.brk 2, Pretty.str s] end;
    fun prt_fix (x, Some T, syn) = Pretty.block (Pretty.str (x ^ " ::") :: Pretty.brk 1 ::
          prt_typ T :: Pretty.brk 1 :: prt_syn syn)
      | prt_fix (x, None, syn) = Pretty.block (Pretty.str x :: Pretty.brk 1 :: prt_syn syn);

    fun prt_name "" = [Pretty.brk 1]
      | prt_name name = [Pretty.str (ProofContext.cond_extern ctxt name ^ ":"), Pretty.brk 1];
    fun prt_asm ((a, _), ts) = Pretty.block (prt_name a @ Pretty.breaks (map (prt_term o fst) ts));
    fun prt_def ((a, _), (t, _)) = Pretty.block (prt_name a @ [prt_term t]);
    fun prt_fact ((a, _), ths) = Pretty.block
      (prt_name a @ Pretty.breaks (map prt_thm (flat (map fst ths))));

    fun items _ [] = []
      | items prfx (x :: xs) = Pretty.block [Pretty.str prfx, Pretty.brk 1, x] :: items "  and" xs;
    fun prt_elem (Fixes fixes) = items "fixes" (map prt_fix fixes)
      | prt_elem (Assumes asms) = items "assumes" (map prt_asm asms)
      | prt_elem (Defines defs) = items "defines" (map prt_def defs)
      | prt_elem (Notes facts) = items "notes" (map prt_fact facts);
  in
    Pretty.big_list "context elements:" (map (Pretty.chunks o prt_elem) all_elems)
    |> Pretty.writeln
  end;


(* store results *)

local

fun hide_bound_names names thy =
  thy |> PureThy.hide_thms false
    (map (Sign.full_name (Theory.sign_of thy)) (filter_out (equal "") names));

in

fun have_thmss_qualified kind name args thy =
  thy
  |> Theory.add_path (Sign.base_name name)
  |> PureThy.have_thmss_i (Drule.kind kind) args
  |>> hide_bound_names (map (#1 o #1) args)
  |>> Theory.parent_path;

fun smart_have_thmss kind None = PureThy.have_thmss_i (Drule.kind kind)
  | smart_have_thmss kind (Some (loc, _)) = have_thmss_qualified kind loc;

end;

local

fun put_facts loc args thy =
  let
    val {view, import, elems, params} = the_locale thy loc;
    val note = Notes (map (fn ((a, more_atts), th_atts) =>
      ((a, more_atts), map (apfst (map (curry Thm.name_thm a))) th_atts)) args);
  in thy |> put_locale loc (make_locale view import (elems @ [(note, stamp ())]) params) end;

fun gen_have_thmss prep_locale get_thms kind raw_loc raw_args thy =
  let
    val thy_ctxt = ProofContext.init thy;
    val loc = prep_locale (Theory.sign_of thy) raw_loc;
    val (_, view, loc_ctxt, _, _) = cert_context_statement (Some loc) [] [] thy_ctxt;
    val args = map (apsnd (map (apfst (get_thms loc_ctxt)))) raw_args;
    val export = ProofContext.export_standard view loc_ctxt thy_ctxt;
    val results = map (map export o #2) (#2 (ProofContext.have_thmss_i args loc_ctxt));
    val args' = map (rpair [] o #1 o #1) args ~~ map (single o Thm.no_attributes) results;
  in
    thy
    |> put_facts loc args
    |> have_thmss_qualified kind loc args'
  end;

in

val have_thmss = gen_have_thmss intern ProofContext.get_thms;
val have_thmss_i = gen_have_thmss (K I) (K I);

fun add_thmss loc args (thy, ctxt) =
  let
    val args' = map (fn ((a, ths), atts) => ((a, atts), [(ths, [])])) args;
    val thy' = put_facts loc args' thy;
    val {view = (_, view_axioms), ...} = the_locale thy loc;
    val ((ctxt', _), (_, facts')) =
      activate_facts (K I) ((ctxt, view_axioms), [(("", []), [Notes args'])]);
  in ((thy', ctxt'), facts') end;

end;


(* predicate text *)

local

val introN = "intro";
val axiomsN = "axioms";

fun atomize_spec sign ts =
  let
    val t = Library.foldr1 Logic.mk_conjunction ts;
    val body = ObjectLogic.atomize_term sign t;
    val bodyT = Term.fastype_of body;
  in
    if bodyT = propT then (t, propT, Thm.reflexive (Thm.cterm_of sign t))
    else (body, bodyT, ObjectLogic.atomize_rule sign (Thm.cterm_of sign t))
  end;

fun aprop_tr' n c = (c, fn args =>
  if length args = n then Syntax.const "_aprop" $ Term.list_comb (Syntax.free c, args)
  else raise Match);

fun def_pred bname parms defs ts norm_ts thy =
  let
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;

    val (body, bodyT, body_eq) = atomize_spec sign norm_ts;
    val env = Term.add_term_free_names (body, []);
    val xs = filter (fn (x, _) => x mem_string env) parms;
    val Ts = map #2 xs;
    val extraTs = (Term.term_tfrees body \\ foldr Term.add_typ_tfrees (Ts, []))
      |> Library.sort_wrt #1 |> map TFree;
    val predT = map Term.itselfT extraTs ---> Ts ---> bodyT;

    val args = map Logic.mk_type extraTs @ map Free xs;
    val head = Term.list_comb (Const (name, predT), args);
    val statement = ObjectLogic.assert_propT sign head;

    val (defs_thy, [pred_def]) =
      thy
      |> (if bodyT <> propT then I else
        Theory.add_trfuns ([], [], map (aprop_tr' (length args)) (NameSpace.accesses' name), []))
      |> Theory.add_consts_i [(bname, predT, Syntax.NoSyn)]
      |> PureThy.add_defs_i false [((Thm.def_name bname, Logic.mk_equals (head, body)), [])];

    val defs_sign = Theory.sign_of defs_thy;
    val cert = Thm.cterm_of defs_sign;

    val intro = Tactic.prove_standard defs_sign [] norm_ts statement (fn _ =>
      Tactic.rewrite_goals_tac [pred_def] THEN
      Tactic.compose_tac (false, body_eq RS Drule.equal_elim_rule1, 1) 1 THEN
      Tactic.compose_tac (false, Drule.conj_intr_list (map (Thm.assume o cert) norm_ts), 0) 1);

    val conjuncts =
      Drule.equal_elim_rule1 OF [Thm.symmetric body_eq,
        Tactic.rewrite_rule [pred_def] (Thm.assume (cert statement))]
      |> Drule.conj_elim_precise (length ts);
    val axioms = (ts ~~ conjuncts) |> map (fn (t, ax) =>
      Tactic.prove defs_sign [] [] t (fn _ =>
        Tactic.rewrite_goals_tac defs THEN
        Tactic.compose_tac (false, ax, 0) 1));
  in (defs_thy, (statement, intro, axioms)) end;

fun change_elem _ (axms, Assumes asms) =
      apsnd Notes ((axms, asms) |> foldl_map (fn (axs, (a, spec)) =>
        let val n = length spec
        in (Library.drop (n, axs), (a, [(Library.take (n, axs), [])])) end))
  | change_elem f (axms, Notes facts) = (axms, Notes (map (apsnd (map (apfst (map f)))) facts))
  | change_elem _ e = e;

fun change_elemss axioms elemss = (axioms, elemss) |> foldl_map
  (fn (axms, (id as ("", _), es)) =>
    foldl_map (change_elem (Drule.satisfy_hyps axioms)) (axms, es) |> apsnd (pair id)
  | x => x) |> #2;

in

fun define_preds bname (parms, ((exts, exts'), (ints, ints')), defs) elemss thy =
  let
    val (thy', (elemss', more_ts)) =
      if Library.null exts then (thy, (elemss, []))
      else
        let
          val aname = if Library.null ints then bname else bname ^ "_" ^ axiomsN;
          val (def_thy, (statement, intro, axioms)) =
            thy |> def_pred aname parms defs exts exts';
          val elemss' = change_elemss axioms elemss @
            [(("", []), [Assumes [((bname ^ "_" ^ axiomsN, []), [(statement, ([], []))])]])];
        in
          def_thy |> have_thmss_qualified "" aname
            [((introN, [ContextRules.intro_query_global None]), [([intro], [])])]
          |> #1 |> rpair (elemss', [statement])
        end;
    val (thy'', view) =
      if Library.null ints then (thy', ([], []))
      else
        let
          val (def_thy, (statement, intro, axioms)) =
            thy' |> def_pred bname parms defs (ints @ more_ts) (ints' @ more_ts);
          val cstatement = Thm.cterm_of (Theory.sign_of def_thy) statement;
        in
          def_thy |> have_thmss_qualified "" bname
            [((introN, [ContextRules.intro_query_global None]), [([intro], [])]),
             ((axiomsN, [ContextRules.elim_query_global None]), [(map Drule.standard axioms, [])])]
          |> #1 |> rpair ([cstatement], axioms)
        end;
  in (thy'', (elemss', view)) end;

end;


(* add_locale(_i) *)

local

fun gen_add_locale prep_ctxt prep_expr do_pred bname raw_import raw_body thy =
  let
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;
    val _ = conditional (is_some (get_locale thy name)) (fn () =>
      error ("Duplicate definition of locale " ^ quote name));

    val thy_ctxt = ProofContext.init thy;
    val (((import_ctxt, import_elemss), (body_ctxt, body_elemss)), text) =
      prep_ctxt raw_import raw_body thy_ctxt;
    val elemss = import_elemss @ body_elemss;

    val (pred_thy, (elemss', view as (view_statement, view_axioms))) =
      if do_pred then thy |> define_preds bname text elemss
      else (thy, (elemss, ([], [])));
    val pred_ctxt = ProofContext.init pred_thy;

    val ((ctxt, _), (_, facts)) = activate_facts (K I) ((pred_ctxt, view_axioms), elemss');
    val export = ProofContext.export_standard view_statement ctxt pred_ctxt;
    val facts' = facts |> map (fn (a, ths) => ((a, []), [(map export ths, [])]));
  in
    pred_thy
    |> have_thmss_qualified "" name facts' |> #1
    |> declare_locale name
    |> put_locale name (make_locale view (prep_expr sign raw_import)
        (map (fn e => (e, stamp ())) (flat (map #2 (filter (equal "" o #1 o #1) elemss'))))
        (params_of elemss', map #1 (params_of body_elemss)))
  end;

in

val add_locale = gen_add_locale read_context intern_expr;
val add_locale_i = gen_add_locale cert_context (K I);

end;



(** locale theory setup **)

val setup =
 [LocalesData.init];

end;
