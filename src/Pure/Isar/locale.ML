(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.  Draws some basic ideas from Florian
Kammüller's original version of locales, but uses the richer
infrastructure of Isar instead of the raw meta-logic.
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
  val activate_context: expr * context attribute element list -> context -> context * context
  val activate_context_i: expr * context attribute element_i list -> context -> context * context
  val add_locale: bstring -> expr -> context attribute element list -> theory -> theory
  val add_locale_i: bstring -> expr -> context attribute element_i list -> theory -> theory
  val print_locales: theory -> unit
  val print_locale: theory -> expr -> unit
  val add_thmss: string -> ((string * thm list) * context attribute list) list -> theory -> theory
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
 {import: expr,                                                         (*dynamic import*)
  elems: ((typ, term, thm list, context attribute) elem * stamp) list,  (*static content*)
  params: (string * typ option) list * string list,                     (*all vs. local params*)
  text: (string * typ) list * term list}                                (*logical representation*)

fun make_locale import elems params text =
 {import = import, elems = elems, params = params, text = text}: locale;



(** theory data **)

structure LocalesArgs =
struct
  val name = "Isar/locales";
  type T = NameSpace.T * locale Symtab.table;

  val empty = (NameSpace.empty, Symtab.empty);
  val copy = I;
  val prep_ext = I;

  (*joining of locale elements: only facts may be added later!*)
  fun join ({import, elems, params, text}: locale, {elems = elems', ...}: locale) =
    Some (make_locale import (gen_merge_lists eq_snd elems elems') params text);
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
    fun prt_id (name, parms) = [Pretty.block (Pretty.breaks (map Pretty.str (name :: parms)))];
    val prt_ids = flat (separate [Pretty.str " +", Pretty.brk 1] (map prt_id ids));
    val err_msg =
      if null ids then msg
      else msg ^ "\n" ^ Pretty.string_of (Pretty.block
        (Pretty.str "The error(s) above occurred in locale:" :: Pretty.brk 1 :: prt_ids));
  in raise ProofContext.CONTEXT (err_msg, ctxt) end;



(** operations on locale elements **)

(* misc utilities *)

fun frozen_tvars ctxt Ts =
  let
    val tvars = rev (foldl Term.add_tvarsT ([], Ts));
    val tfrees = map TFree
      (Term.invent_type_names (ProofContext.used_types ctxt) (length tvars) ~~ map #2 tvars);
  in map #1 tvars ~~ tfrees end;

fun fixes_of_elemss elemss = flat (map (snd o fst) elemss);


(* prepare elements *)

datatype fact = Int of thm list | Ext of string;

local

fun prep_name ctxt (name, atts) =
  if NameSpace.is_qualified name then
    raise ProofContext.CONTEXT ("Illegal qualified name: " ^ quote name, ctxt)
  else (name, atts);

fun prep_elem prep_vars prep_propp prep_thms ctxt =
 fn Fixes fixes =>
      let val vars = snd (foldl_map prep_vars (ctxt, map (fn (x, T, _) => ([x], T)) fixes))
      in Fixes (map (fn (([x'], T'), (_, _, mx)) => (x', T', mx)) (vars ~~ fixes)) end
  | Assumes asms =>
      Assumes (map (prep_name ctxt o #1) asms ~~ snd (prep_propp (ctxt, map #2 asms)))
  | Defines defs =>
      let val propps = snd (prep_propp (ctxt, map (fn (_, (t, ps)) => [(t, (ps, []))]) defs)) in
        Defines (map (prep_name ctxt o #1) defs ~~ map (fn [(t', (ps', []))] => (t', ps')) propps)
      end
  | Notes facts =>
      Notes (map (fn (a, bs) => (prep_name ctxt a, map (apfst (prep_thms ctxt)) bs)) facts);

in

fun read_elem x = prep_elem ProofContext.read_vars ProofContext.read_propp (K I) x;
fun cert_elem x = prep_elem ProofContext.cert_vars ProofContext.cert_propp (K I) x;
fun int_facts x = prep_elem I I (K Int) x;
fun ext_facts x = prep_elem I I (K Ext) x;
fun get_facts x = prep_elem I I
  (fn ctxt => (fn Int ths => ths | Ext name => ProofContext.get_thms ctxt name)) x;

fun read_expr ctxt (Locale xname) = Locale (intern (ProofContext.sign_of ctxt) xname)
  | read_expr ctxt (Merge exprs) = Merge (map (read_expr ctxt) exprs)
  | read_expr ctxt (Rename (expr, xs)) = Rename (read_expr ctxt expr, xs);

end;


(* internalize attributes *)

local fun read_att attrib (x, srcs) = (x, map attrib srcs) in

fun attribute _ (Elem (Fixes fixes)) = Elem (Fixes fixes)
  | attribute attrib (Elem (Assumes asms)) = Elem (Assumes (map (apfst (read_att attrib)) asms))
  | attribute attrib (Elem (Defines defs)) = Elem (Defines (map (apfst (read_att attrib)) defs))
  | attribute attrib (Elem (Notes facts)) =
      Elem (Notes (map (apfst (read_att attrib) o apsnd (map (read_att attrib))) facts))
  | attribute _ (Expr expr) = Expr expr;

end;


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

fun rename_elem ren (Fixes fixes) = Fixes (map (fn (x, T, mx) =>
      (rename ren x, T, if mx = None then mx else Some Syntax.NoSyn)) fixes)    (*drops syntax!*)
  | rename_elem ren (Assumes asms) = Assumes (map (apsnd (map (fn (t, (ps, qs)) =>
      (rename_term ren t, (map (rename_term ren) ps, map (rename_term ren) qs))))) asms)
  | rename_elem ren (Defines defs) = Defines (map (apsnd (fn (t, ps) =>
      (rename_term ren t, map (rename_term ren) ps))) defs)
  | rename_elem ren (Notes facts) = Notes (map (apsnd (map (apfst (map (rename_thm ren))))) facts);

fun qualify_elem prfx elem =
  let
    fun qualify (arg as ((name, atts), x)) =
      if name = "" then arg
      else ((NameSpace.pack (filter_out (equal "") (prfx @ [name])), atts), x);
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

fun inst_thm [] th = th
  | inst_thm env th =
      let
        val {sign, hyps, prop, maxidx, ...} = Thm.rep_thm th;
        val cert = Thm.cterm_of sign and certT = Thm.ctyp_of sign;
        val names = foldr Term.add_term_tfree_names (prop :: hyps, []);
        val env' = filter (fn ((a, _), _) => a mem_string names) env;
      in
        if null env' then th
        else
          th
          |> Drule.implies_intr_list (map cert hyps)
          |> Drule.tvars_intr_list names
          |> (fn (th', al) => th' |>
            Thm.instantiate ((map (fn ((a, _), T) => (the (assoc (al, a)), certT T)) env'), []))
          |> (fn th'' => Drule.implies_elim_list th''
              (map (Thm.assume o cert o inst_term env') hyps))
      end;

fun inst_elem env (Fixes fixes) =
      Fixes (map (fn (x, T, mx) => (x, apsome (inst_type env) T, mx)) fixes)
  | inst_elem env (Assumes asms) = Assumes (map (apsnd (map (fn (t, (ps, qs)) =>
      (inst_term env t, (map (inst_term env) ps, map (inst_term env) qs))))) asms)
  | inst_elem env (Defines defs) = Defines (map (apsnd (fn (t, ps) =>
      (inst_term env t, map (inst_term env) ps))) defs)
  | inst_elem env (Notes facts) = Notes (map (apsnd (map (apfst (map (inst_thm env))))) facts);


(* evaluation *)

local

fun unify_parms ctxt raw_parmss =
  let
    val tsig = Sign.tsig_of (ProofContext.sign_of ctxt);
    val maxidx = length raw_parmss;
    val idx_parmss = (0 upto maxidx - 1) ~~ raw_parmss;

    fun varify i = Term.map_type_tfree (fn (a, S) => TVar ((a, i), S));
    fun varify_parms (i, ps) =
      mapfilter (fn (_, None) => None | (x, Some T) => Some (x, varify i T)) ps;
    val parms = flat (map varify_parms idx_parmss);

    fun unify T ((env, maxidx), U) = Type.unify tsig maxidx env (U, T);  (*should never fail*)
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

fun inst_types _ [elems] = [elems]
  | inst_types ctxt elemss =
      let
        val envs = unify_parms ctxt (map (#2 o #1) elemss);
        fun inst (((name, ps), elems), env) =
          ((name, map (apsnd (apsome (inst_type env))) ps), map (inst_elem env) elems);
      in map inst (elemss ~~ envs) end;

in

fun eval_expr ctxt expr =
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
            val ren = renaming xs parms' handle ERROR_MESSAGE msg => err_in_locale ctxt msg ids';
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
        val elems'' = map (qualify_elem [NameSpace.base name, space_implode "_" xs]) elems';
      in ((name, params'), elems'') end;

    val raw_elemss = unique_parms ctxt (map eval (#1 (identify (([], []), expr))));
    val elemss = inst_types ctxt raw_elemss;
  in elemss end;

end;



(** activation **)

(* internalize elems *)

local

fun perform_elems f named_elems = ProofContext.qualified (fn context =>
  foldl (fn (ctxt, ((name, ps), es)) =>
    foldl (fn (c, e) => f e c) (ctxt, es) handle ProofContext.CONTEXT (msg, ctxt) =>
      err_in_locale ctxt msg [(name, map fst ps)]) (context, named_elems));

in

fun declare_elem gen =
  let
    val gen_typ = if gen then Term.map_type_tfree (Type.param []) else I;
    val gen_term = if gen then Term.map_term_types gen_typ else I;

    fun declare (Fixes fixes) = ProofContext.add_syntax fixes o
          ProofContext.fix_direct (map (fn (x, T, _) => ([x], apsome gen_typ T)) fixes)
      | declare (Assumes asms) = (fn ctxt => #1 (ProofContext.bind_propp_i
          (ctxt, map (map (fn (t, (ps, ps')) =>
            (gen_term t, (map gen_term ps, map gen_term ps'))) o #2) asms)))
      | declare (Defines defs) = (fn ctxt => #1 (ProofContext.bind_propp_i
          (ctxt, map (fn (_, (t, ps)) => [(gen_term t, (map gen_term ps, []))]) defs)))
      | declare (Notes _) = I;
  in declare end;

fun activate_elem (Fixes fixes) = ProofContext.add_syntax fixes o
      ProofContext.fix_direct (map (fn (x, T, _) => ([x], T)) fixes)
  | activate_elem (Assumes asms) =
      #1 o ProofContext.assume_i ProofContext.export_assume asms o
      ProofContext.fix_frees (flat (map (map #1 o #2) asms))
  | activate_elem (Defines defs) = (fn ctxt => #1 (ProofContext.assume_i ProofContext.export_def
      (map (fn ((name, atts), (t, ps)) =>
        let val (c, t') = ProofContext.cert_def ctxt t
        in ((if name = "" then Thm.def_name c else name, atts), [(t', (ps, []))]) end) defs) ctxt))
  | activate_elem (Notes facts) = #1 o ProofContext.have_thmss facts;

fun declare_elemss gen = perform_elems (declare_elem gen);
fun activate_elemss x = perform_elems activate_elem x;

end;


(* context specifications: import expression + external elements *)

local

fun close_frees ctxt t =
  let val frees = rev (filter_out (ProofContext.is_fixed ctxt o #1) (Term.add_frees ([], t)))
  in Term.list_all_free (frees, t) end;

(*quantify dangling frees, strip term bindings*)
fun closeup ctxt (Assumes asms) = Assumes (asms |> map (fn (a, propps) =>
      (a, map (fn (t, _) => (close_frees ctxt t, ([], []))) propps)))
  | closeup ctxt (Defines defs) = Defines (defs |> map (fn (a, (t, _)) =>
      (a, (close_frees ctxt (#2 (ProofContext.cert_def ctxt t)), []))))
  | closeup ctxt elem = elem;

fun fixes_of_elem (Fixes fixes) = map (fn (x, T, _) => (x, T)) fixes
  | fixes_of_elem _ = [];

fun prepare_context prep_expr prep_elem1 prep_elem2 close (import, elements) context =
  let
    fun declare_expr (c, raw_expr) =
      let
        val expr = prep_expr c raw_expr;
        val named_elemss = eval_expr c expr;
      in (c |> declare_elemss true named_elemss, named_elemss) end;

    fun declare_element (c, Elem raw_elem) =
          let
            val elem = (if close then closeup c else I) (prep_elem2 c (prep_elem1 c raw_elem));
            val res = [(("", fixes_of_elem elem), [elem])];
          in (c |> declare_elemss false res, res) end
      | declare_element (c, Expr raw_expr) =
          apsnd (map (apsnd (map (int_facts c)))) (declare_expr (c, raw_expr));

    fun activate_elems (c, ((name, ps), raw_elems)) =
      let
        val elems = map (get_facts c) raw_elems;
        val res = ((name, ps), elems);
      in (c |> activate_elemss [res], res) end;

    val (import_ctxt, import_elemss) = declare_expr (context, import);
    val (ctxt, elemss) = apsnd flat (foldl_map declare_element (import_ctxt, elements));
    val type_env = frozen_tvars ctxt (mapfilter (ProofContext.default_type ctxt o #1)
      (fixes_of_elemss import_elemss @ fixes_of_elemss elemss));
    val FIXME = PolyML.print type_env;

    fun inst_elems ((name, ps), elems) = ((name, ps), elems);    (* FIXME *)

    val import_elemss' = map inst_elems import_elemss;
    val import_ctxt' = context |> activate_elemss import_elemss';
    val (ctxt', elemss') = foldl_map activate_elems (import_ctxt', map inst_elems elemss);
  in ((import_ctxt', import_elemss'), (ctxt', elemss')) end;

val prep_context = prepare_context read_expr read_elem ext_facts;
val prep_context_i = prepare_context (K I) cert_elem int_facts;

in

val read_context = prep_context true;
val cert_context = prep_context_i true;
val activate_context = pairself fst oo prep_context false;
val activate_context_i = pairself fst oo prep_context_i false;
fun activate_locale name = #1 o activate_context_i (Locale name, []);

end;



(** print locale **)

fun print_locale thy raw_expr =
  let
    val sg = Theory.sign_of thy;
    val thy_ctxt = ProofContext.init thy;
    val (ctxt, elemss) = #1 (read_context (raw_expr, []) thy_ctxt);

    val prt_typ = Pretty.quote o ProofContext.pretty_typ ctxt;
    val prt_term = Pretty.quote o ProofContext.pretty_term ctxt;
    val prt_thm = Pretty.quote o ProofContext.pretty_thm ctxt;

    fun prt_syn syn =
      let val s = (case syn of None => "(structure)" | Some mx => Syntax.string_of_mixfix mx)
      in if s = "" then [] else [Pretty.brk 4, Pretty.str s] end;
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
    Pretty.big_list "locale elements:" (map (Pretty.chunks o prt_elem) (flat (map #2 elemss)))
    |> Pretty.writeln
  end;



(** define locales **)

(* add_locale(_i) *)

local

fun gen_add_locale prep_context prep_expr bname raw_import raw_body thy =
  let
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;
    val _ = conditional (is_some (get_locale thy name)) (fn () =>
      error ("Duplicate definition of locale " ^ quote name));

    val thy_ctxt = ProofContext.init thy;
    val ((import_ctxt, import_elemss), (body_ctxt, body_elemss)) =
      prep_context (raw_import, raw_body) thy_ctxt;
    val import_parms = fixes_of_elemss import_elemss;
    val import = (prep_expr thy_ctxt raw_import);

    val elems = flat (map snd body_elemss);
    val body_parms = fixes_of_elemss body_elemss;
    val text = ([], []);  (* FIXME *)
  in
    thy
    |> declare_locale name
    |> put_locale name (make_locale import (map (fn e => (e, stamp ())) elems)
      (import_parms @ body_parms, map #1 body_parms) text)
  end;

in

val add_locale = gen_add_locale read_context read_expr;
val add_locale_i = gen_add_locale cert_context (K I);

end;



(** store results **)

fun add_thmss name args thy =
  let
    val {import, params, elems, text} = the_locale thy name;
    val note = Notes (map (fn ((a, ths), atts) =>
      ((a, atts), [(map (curry Thm.name_thm a) ths, [])])) args);
  in
    thy |> ProofContext.init |> activate_locale name |> activate_elem note;  (*test attributes!*)
    thy |> put_locale name (make_locale import (elems @ [(note, stamp ())]) params text)
  end;



(** locale theory setup **)

val setup =
 [LocalesData.init];

end;
