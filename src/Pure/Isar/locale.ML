(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.  Draws basic ideas from Florian
Kammüller's original version of locales, but uses the rich
infrastructure of Isar instead of the raw meta-logic.
*)

signature BASIC_LOCALE =
sig
  val print_locales: theory -> unit
  val print_locale: theory -> xstring -> unit
end;

signature LOCALE =
sig
  include BASIC_LOCALE
  type context
  datatype expression =
    Locale of string |
    Merge of expression list |
    Rename of expression * string option list
  datatype ('typ, 'term, 'fact, 'att) elem =
    Fixes of (string * 'typ option * mixfix option) list |
    Assumes of ((string * 'att list) * ('term * ('term list * 'term list)) list) list |
    Defines of ((string * 'att list) * ('term * 'term list)) list |
    Notes of ((string * 'att list) * ('fact * 'att list) list) list |
    Uses of expression
  type 'att element
  type 'att element_i
  type locale
  val intern: Sign.sg -> xstring -> string
  val cond_extern: Sign.sg -> string -> xstring
  val attribute: ('att -> context attribute) ->
    ('typ, 'term, 'thm, 'att) elem -> ('typ, 'term, 'thm, context attribute) elem
  val activate_elements: context attribute element list -> context -> context
  val activate_elements_i: context attribute element_i list -> context -> context
  val activate_locale: xstring -> context -> context
  val activate_locale_i: string -> context -> context
  val add_locale: bstring -> xstring list -> context attribute element list -> theory -> theory
  val add_locale_i: bstring -> xstring list -> context attribute element_i list -> theory -> theory
  val add_thmss: string -> ((string * thm list) * context attribute list) list
    -> theory -> theory
  val setup: (theory -> theory) list
end;

structure Locale: LOCALE =
struct


(** locale elements and locales **)

type context = ProofContext.context;

datatype expression =
  Locale of string |
  Merge of expression list |
  Rename of expression * string option list;

datatype ('typ, 'term, 'fact, 'att) elem =
  Fixes of (string * 'typ option * mixfix option) list |
  Assumes of ((string * 'att list) * ('term * ('term list * 'term list)) list) list |
  Defines of ((string * 'att list) * ('term * 'term list)) list |
  Notes of ((string * 'att list) * ('fact * 'att list) list) list |
  Uses of expression;

type 'att element = (string, string, string, 'att) elem;
type 'att element_i = (typ, term, thm list, 'att) elem;

type locale =
 {imports: string list,
  elements: context attribute element_i list,
  params: (string * typ) list,
  text: ((string * typ) list * term) option,
  closed: bool};

fun make_locale imports elements params text closed =
 {imports = imports, elements = elements, params = params,
  text = text, closed = closed}: locale;



(** theory data **)

(* data kind 'Pure/locales' *)

structure LocalesArgs =
struct
  val name = "Isar/locales";
  type T = NameSpace.T * locale Symtab.table;

  val empty = (NameSpace.empty, Symtab.empty);
  val copy = I;

  fun close {imports, elements, params, text, closed = _} =
    make_locale imports elements params text true;
  fun finish (space, locales) = (space, Symtab.map close locales);

  val prep_ext = I;
  fun merge ((space1, locales1), (space2, locales2)) =
      (NameSpace.merge (space1, space2), Symtab.merge (K true) (locales1, locales2));

  fun print _ (space, locales) =
    Pretty.strs ("locales:" :: map (NameSpace.cond_extern space o #1) (Symtab.dest locales))
    |> Pretty.writeln;
end;

structure LocalesData = TheoryDataFun(LocalesArgs);
val print_locales = LocalesData.print;

val intern = NameSpace.intern o #1 o LocalesData.get_sg;
val cond_extern = NameSpace.cond_extern o #1 o LocalesData.get_sg;


(* access locales *)

fun declare_locale name =
  LocalesData.map (apfst (fn space => (NameSpace.extend (space, [name]))));

fun put_locale name locale =
  LocalesData.map (apsnd (fn locales => Symtab.update ((name, locale), locales)));

fun get_locale thy name = Symtab.lookup (#2 (LocalesData.get thy), name);

fun the_locale thy name =
  (case get_locale thy name of
    Some loc => loc
  | None => error ("Unknown locale " ^ quote name));



(** internalize elements **)

(* read *)

fun read_expression ctxt (Locale xname) = Locale (intern (ProofContext.sign_of ctxt) xname)
  | read_expression ctxt (Merge exprs) = Merge (map (read_expression ctxt) exprs)
  | read_expression ctxt (Rename (expr, xs)) = Rename (read_expression ctxt expr, xs);

fun read_elem ctxt =
 fn Fixes fixes =>
      let val vars =
        #2 (foldl_map ProofContext.read_vars (ctxt, map (fn (x, T, _) => ([x], T)) fixes))
      in Fixes (map2 (fn (([x'], T'), (_, _, mx)) => (x', T', mx)) (vars, fixes)) end
  | Assumes asms =>
      Assumes (map #1 asms ~~ #2 (ProofContext.read_propp (ctxt, map #2 asms)))
  | Defines defs =>
      let val propps =
        #2 (ProofContext.read_propp (ctxt, map (fn (_, (t, ps)) => [(t, (ps, []))]) defs))
      in Defines (map #1 defs ~~ map (fn [(t', (ps', []))] => (t', ps')) propps) end
  | Notes facts =>
      Notes (map (apsnd (map (apfst (ProofContext.get_thms ctxt)))) facts)
  | Uses expr => Uses (read_expression ctxt expr);


(* prepare attributes *)

local fun int_att attrib (x, srcs) = (x, map attrib srcs) in

fun attribute _ (Fixes fixes) = Fixes fixes
  | attribute attrib (Assumes asms) = Assumes (map (apfst (int_att attrib)) asms)
  | attribute attrib (Defines defs) = Defines (map (apfst (int_att attrib)) defs)
  | attribute attrib (Notes facts) =
      Notes (map (apfst (int_att attrib) o apsnd (map (int_att attrib))) facts)
  | attribute _ (Uses expr) = Uses expr;

end;


(** renaming **)

fun rename ren x = if_none (assoc_string (ren, x)) x;

fun rename_term ren (Free (x, T)) = Free (rename ren x, T)
  | rename_term ren (t $ u) = rename_term ren t $ rename_term ren u
  | rename_term ren (Abs (x, T, t)) = Abs (x, T, rename_term ren t)
  | rename_term _ a = a;

fun rename_thm ren th =
  let
    val {sign, hyps, prop, maxidx, ...} = Thm.rep_thm th;
    val cert = Thm.cterm_of sign;
    val (xs, Ts) = Library.split_list (foldl Drule.add_frees ([], prop :: hyps));
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
      (rename ren x, T, if mx = None then mx else Some Syntax.NoSyn)) fixes)
  | rename_elem ren (Assumes asms) = Assumes (map (apsnd (map (fn (t, (ps, qs)) =>
      (rename_term ren t, (map (rename_term ren) ps, map (rename_term ren) qs))))) asms)
  | rename_elem ren (Defines defs) = Defines (map (apsnd (fn (t, ps) =>
      (rename_term ren t, map (rename_term ren) ps))) defs)
  | rename_elem ren (Notes facts) = Notes (map (apsnd (map (apfst (map (rename_thm ren))))) facts)
  | rename_elem ren (Uses expr) = sys_error "FIXME";



(** activate locales **)

fun activate (ctxt, Fixes fixes) =
      ctxt |> ProofContext.fix_direct (map (fn (x, T, mx) => ([x], T)) fixes)
      |> ProofContext.add_syntax fixes
  | activate (ctxt, Assumes asms) =
      ctxt |> ProofContext.fix_frees (flat (map (map #1 o #2) asms))
      |> ProofContext.assume_i ProofContext.export_assume asms |> #1
  | activate (ctxt, Defines defs) = #1 (ProofContext.assume_i ProofContext.export_def
      (map (fn ((name, atts), (t, ps)) =>
        let val (c, t') = ProofContext.cert_def ctxt t
        in ((if name = "" then Thm.def_name c else name, atts), [(t', (ps, []))]) end) defs) ctxt)
  | activate (ctxt, Notes facts) = #1 (ProofContext.have_thmss facts ctxt)
  | activate (ctxt, Uses expr) = activate_expression [] (ctxt, expr)

and activate_elements_i elems ctxt = foldl activate (ctxt, elems)

and activate_expression rs (ctxt, Locale name) = activate_loc rs name ctxt
  | activate_expression rs (ctxt, Merge exprs) = foldl (activate_expression rs) (ctxt, exprs)
  | activate_expression rs (ctxt, Rename (expr, xs)) = activate_expression (xs :: rs) (ctxt, expr)

and activate_locale_elements rs (ctxt, name) =
  let
    val thy = ProofContext.theory_of ctxt;
    val {elements, params, ...} = the_locale thy name;    (*exception ERROR*)
    val param_names = map #1 params;

    fun replace (opt_x :: xs, y :: ys) = if_none opt_x y :: replace (xs, ys)
      | replace ([], ys) = ys
      | replace (_ :: _, []) = raise ProofContext.CONTEXT
          ("Too many parameters in renaming of locale " ^ quote name, ctxt);

    val elements' =
      if null rs then elements
      else map (rename_elem (param_names ~~ foldr replace (rs, param_names))) elements;
  in
    activate_elements_i elements' ctxt handle ProofContext.CONTEXT (msg, c) =>
      raise ProofContext.CONTEXT (msg ^ "\nThe error(s) above occurred in locale " ^
        quote (cond_extern (Theory.sign_of thy) name), c)
  end

and activate_loc rs name ctxt =
  activate_locale_elements rs (foldl (activate_locale_elements rs)
    (ctxt, #imports (the_locale (ProofContext.theory_of ctxt) name)), name);


fun activate_elements elems ctxt =
  foldl ((fn (ctxt, elem) => activate (ctxt, read_elem ctxt elem))) (ctxt, elems);

val activate_locale_i = activate_loc [];

fun activate_locale xname ctxt =
  activate_locale_i (intern (ProofContext.sign_of ctxt) xname) ctxt;



(** print locale **)

fun pretty_locale thy xname =
  let
    val sg = Theory.sign_of thy;
    val name = intern sg xname;
    val {imports, elements, params = _, text = _, closed = _} = the_locale thy name;
    val locale_ctxt = ProofContext.init thy |> activate_locale_i name;

    val prt_typ = Pretty.quote o ProofContext.pretty_typ locale_ctxt;
    val prt_term = Pretty.quote o ProofContext.pretty_term locale_ctxt;
    val prt_thm = Pretty.quote o ProofContext.pretty_thm locale_ctxt;

    fun prt_syn syn =
      let val s = (case syn of None => "(structure)" | Some mx => Syntax.string_of_mixfix mx)
      in if s = "" then [] else [Pretty.brk 4, Pretty.str s] end;
    fun prt_fix (x, Some T, syn) = Pretty.block (Pretty.str (x ^ " ::") :: Pretty.brk 1 ::
          prt_typ T :: Pretty.brk 1 :: prt_syn syn)
      | prt_fix (x, None, syn) = Pretty.block (Pretty.str x :: Pretty.brk 1 :: prt_syn syn);

    fun prt_asm (("", _), ts) = Pretty.block (Pretty.breaks (map (prt_term o fst) ts))
      | prt_asm ((a, _), ts) = Pretty.block
          (Pretty.breaks (Pretty.str (a ^ ":") :: map (prt_term o fst) ts));
    fun prt_asms asms = Pretty.block
      (flat (separate [Pretty.fbrk, Pretty.str "and"] (map (single o prt_asm) asms)));

    fun prt_def (("", _), (t, _)) = Pretty.block [Pretty.brk 1, prt_term t]
      | prt_def ((a, _), (t, _)) = Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1, prt_term t];

    fun prt_fact (("", _), ths) = Pretty.block (Pretty.breaks (map prt_thm (flat (map fst ths))))
      | prt_fact ((a, _), ths) = Pretty.block
          (Pretty.breaks (Pretty.str (a ^ ":") :: map prt_thm (flat (map fst ths))));

    fun prt_expr (Locale name) = Pretty.str (cond_extern sg name)
      | prt_expr (Merge exprs) = Pretty.enclose "(" ")"
          (flat (separate [Pretty.str " +", Pretty.brk 1]
            (map (single o prt_expr) exprs)))
      | prt_expr (Rename (expr, xs)) = Pretty.enclose "(" ")"
          (Pretty.breaks (prt_expr expr :: map (fn x => Pretty.str (if_none x "_")) xs));

    fun prt_elem (Fixes fixes) = Pretty.big_list "fixes" (map prt_fix fixes)
      | prt_elem (Assumes asms) = Pretty.big_list "assumes" (map prt_asm asms)
      | prt_elem (Defines defs) = Pretty.big_list "defines" (map prt_def defs)
      | prt_elem (Notes facts) = Pretty.big_list "notes" (map prt_fact facts)
      | prt_elem (Uses expr) = Pretty.block [Pretty.str "uses", Pretty.brk 1, prt_expr expr];

    val prt_header = Pretty.block (Pretty.str ("locale " ^ cond_extern sg name ^ " =") ::
       (if null imports then [] else
       (Pretty.str " " :: flat (separate [Pretty.str " +", Pretty.brk 1]
           (map (single o Pretty.str o cond_extern sg) imports)) @ [Pretty.str " +"])));
  in Pretty.block (Pretty.fbreaks (prt_header :: map prt_elem elements)) end;

val print_locale = Pretty.writeln oo pretty_locale;



(** define locales **)

(* closeup dangling frees *)

fun close_frees_wrt ctxt t =
  let val frees = rev (filter_out (ProofContext.is_fixed ctxt o #1) (Drule.add_frees ([], t)))
  in curry Term.list_all_free frees end;

fun closeup ctxt (Assumes asms) = Assumes (asms |> map (fn (a, propps) =>
      (a, propps |> map (fn (t, (ps1, ps2)) =>
        let val close = close_frees_wrt ctxt t in (close t, (map close ps1, map close ps2)) end))))
  | closeup ctxt (Defines defs) = Defines (defs |> map (fn (a, (t, ps)) =>
      let
        val (_, t') = ProofContext.cert_def ctxt t;
        val close = close_frees_wrt ctxt t';
      in (a, (close t', map close ps)) end))
  | closeup ctxt elem = elem;


(* add_locale(_i) *)

fun gen_add_locale prep_locale prep_elem bname raw_imports raw_elems thy =
  let
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;
    val _ =
      if is_none (get_locale thy name) then () else
      error ("Duplicate definition of locale " ^ quote name);

    val imports = map (prep_locale sign) raw_imports;
    val imports_ctxt = foldl (activate_locale_elements []) (ProofContext.init thy, imports);
    fun prep (ctxt, raw_elem) =
      let val elem = closeup ctxt (prep_elem ctxt raw_elem)
      in (activate (ctxt, elem), elem) end;
    val (locale_ctxt, elems) = foldl_map prep (imports_ctxt, raw_elems);
    val params = [];  (* FIXME *)
    val text = None;  (* FIXME *)
  in
    thy
    |> declare_locale name
    |> put_locale name (make_locale imports elems params text false)
  end;

val add_locale = gen_add_locale intern read_elem;
val add_locale_i = gen_add_locale (K I) (K I);



(** store results **)

fun add_thmss name args thy =
  let
    val {imports, elements, params, text, closed} = the_locale thy name;
    val _ = conditional closed (fn () =>
      error ("Cannot store results in closed locale: " ^ quote name));
    val note = Notes (map (fn ((a, ths), atts) =>
      ((a, atts), [(map (curry Thm.name_thm a) ths, [])])) args);
  in
    activate (thy |> ProofContext.init |> activate_locale_i name, note);    (*test attributes!*)
    thy |> put_locale name (make_locale imports (elements @ [note]) params text closed)
  end;



(** locale theory setup **)

val setup =
 [LocalesData.init];

end;

structure BasicLocale: BASIC_LOCALE = Locale;
open BasicLocale;
