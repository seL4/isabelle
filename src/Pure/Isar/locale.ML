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
  val the_locale: theory -> string -> locale  (* FIXME *)
  val intern: Sign.sg -> xstring -> string
  val cond_extern: Sign.sg -> string -> xstring
  val attribute: ('att -> context attribute) -> ('typ, 'term, 'thm, 'att) elem_expr
    -> ('typ, 'term, 'thm, context attribute) elem_expr
  val activate_elements: context attribute element list -> context -> context
  val activate_elements_i: context attribute element_i list -> context -> context
  val activate_locale: xstring -> context -> context
  val activate_locale_i: string -> context -> context
  val add_locale: bstring -> expr -> context attribute element list -> theory -> theory
  val add_locale_i: bstring -> expr -> context attribute element_i list -> theory -> theory
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
 {import: expr,                                                     (*dynamic import*)
  elems: (typ, term, thm list, context attribute) elem list,        (*static content*)
  params: (string * typ option) list * (string * typ option) list,  (*all vs. local params*)
  text: (string * typ) list * term list,                            (*logical representation*)
  closed: bool};                                                    (*disallow further notes*)

fun make_locale import elems params text closed =
 {import = import, elems = elems, params = params, text = text, closed = closed}: locale;



(** theory data **)

structure LocalesArgs =
struct
  val name = "Isar/locales";
  type T = NameSpace.T * locale Symtab.table;

  val empty = (NameSpace.empty, Symtab.empty);
  val copy = I;
  val prep_ext = I;
  fun merge ((space1, locs1), (space2, locs2)) =
    (NameSpace.merge (space1, space2), Symtab.merge (K true) (locs1, locs2));
  fun finish (space, locs) = (space, Symtab.map (fn {import, elems, params, text, closed = _} =>
    make_locale import elems params text true) locs);
  fun print _ (space, locs) =
    Pretty.strs ("locales:" :: map (NameSpace.cond_extern space o #1) (Symtab.dest locs))
    |> Pretty.writeln;
end;

structure LocalesData = TheoryDataFun(LocalesArgs);
val print_locales = LocalesData.print;

fun declare_locale name =
  LocalesData.map (apfst (fn space => (NameSpace.extend (space, [name]))));

fun put_locale name loc = LocalesData.map (apsnd (fn locs => Symtab.update ((name, loc), locs)));
fun get_locale thy name = Symtab.lookup (#2 (LocalesData.get thy), name);

fun the_locale thy name =
  (case get_locale thy name of
    Some loc => loc
  | None => error ("Unknown locale " ^ quote name));



(** internalization **)

(* names *)

val intern = NameSpace.intern o #1 o LocalesData.get_sg;
val cond_extern = NameSpace.cond_extern o #1 o LocalesData.get_sg;


(* read *)

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
      Notes (map (apsnd (map (apfst (ProofContext.get_thms ctxt)))) facts);

fun read_expr ctxt (Locale xname) = Locale (intern (ProofContext.sign_of ctxt) xname)
  | read_expr ctxt (Merge exprs) = Merge (map (read_expr ctxt) exprs)
  | read_expr ctxt (Rename (expr, xs)) =
      (case duplicates (mapfilter I xs) of [] => Rename (read_expr ctxt expr, xs)
      | ds => raise ProofContext.CONTEXT ("Duplicates in renaming: " ^ commas_quote ds, ctxt));;

fun read_element ctxt (Elem e) = Elem (read_elem ctxt e)
  | read_element ctxt (Expr e) = Expr (read_expr ctxt e);


(* attribute *)

local fun int_att attrib (x, srcs) = (x, map attrib srcs) in

fun attribute _ (Elem (Fixes fixes)) = Elem (Fixes fixes)
  | attribute attrib (Elem (Assumes asms)) = Elem (Assumes (map (apfst (int_att attrib)) asms))
  | attribute attrib (Elem (Defines defs)) = Elem (Defines (map (apfst (int_att attrib)) defs))
  | attribute attrib (Elem (Notes facts)) =
      Elem (Notes (map (apfst (int_att attrib) o apsnd (map (int_att attrib))) facts))
  | attribute _ (Expr expr) = Expr expr;

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
      (rename ren x, T, if mx = None then mx else Some Syntax.NoSyn)) fixes)    (*drops syntax!*)
  | rename_elem ren (Assumes asms) = Assumes (map (apsnd (map (fn (t, (ps, qs)) =>
      (rename_term ren t, (map (rename_term ren) ps, map (rename_term ren) qs))))) asms)
  | rename_elem ren (Defines defs) = Defines (map (apsnd (fn (t, ps) =>
      (rename_term ren t, map (rename_term ren) ps))) defs)
  | rename_elem ren (Notes facts) = Notes (map (apsnd (map (apfst (map (rename_thm ren))))) facts);



(** evaluation **)

fun eval_expr ctxt expr =
  let
    val thy = ProofContext.theory_of ctxt;

    fun renaming (Some x :: xs) (y :: ys) = (y, x) :: renaming xs ys
      | renaming (None :: xs) (y :: ys) = renaming xs ys
      | renaming [] _ = []
      | renaming xs [] = raise ProofContext.CONTEXT ("Extraneous arguments in renaming: " ^
          commas (map (fn None => "_" | Some x => quote x) xs), ctxt);

    fun identify ((ids, parms), Locale name) =
          let
            val {import, params, ...} = the_locale thy name;
            val ps = map #1 (#1 params);
          in
            if (name, ps) mem ids then (ids, parms)
            else identify (((name, ps) :: ids, merge_lists parms ps), import)
          end
      | identify ((ids, parms), Rename (e, xs)) =
          let
            val (ids', parms') = identify (([], []), e);
            val ren = renaming xs parms';
            val ids'' = map (apsnd (map (rename ren))) ids' \\ ids;
          in (ids'' @ ids, merge_lists parms (map (rename ren) parms')) end
      | identify (arg, Merge es) = foldl identify (arg, es);

    val idents = rev (#1 (identify (([], []), expr)));
    val FIXME = PolyML.print idents;

    fun eval (name, ps') =
      let
        val {params = (ps, _), elems, ...} = the_locale thy name;
        val ren = filter_out (op =) (map #1 ps ~~ ps');
      in
        if null ren then ((name, ps), elems)
        else ((name, map (apfst (rename ren)) ps), map (rename_elem ren) elems)
      end;
    (* FIXME unify types; specific errors (name) *)

  in map eval idents end;

fun eval_elements ctxt =
  flat o map (fn Elem e => [e] | Expr e => flat (map #2 (eval_expr ctxt e)));



(** activation **)

fun activate_elem (Fixes fixes) = ProofContext.add_syntax fixes o
      ProofContext.fix_direct (map (fn (x, T, mx) => ([x], T)) fixes)
  | activate_elem (Assumes asms) =
      #1 o ProofContext.assume_i ProofContext.export_assume asms o
      ProofContext.fix_frees (flat (map (map #1 o #2) asms))
  | activate_elem (Defines defs) = (fn ctxt => #1 (ProofContext.assume_i ProofContext.export_def
      (map (fn ((name, atts), (t, ps)) =>
        let val (c, t') = ProofContext.cert_def ctxt t
        in ((if name = "" then Thm.def_name c else name, atts), [(t', (ps, []))]) end) defs) ctxt))
  | activate_elem (Notes facts) = #1 o ProofContext.have_thmss facts;

fun activate_elems es ctxt = foldl (fn (c, e) => activate_elem e c) (ctxt, es);

fun activate_elements_i elements ctxt = activate_elems (eval_elements ctxt elements) ctxt;
fun activate_elements elements ctxt = activate_elements_i (map (read_element ctxt) elements) ctxt;

fun activate_locale_i name = activate_elements_i [Expr (Locale name)];
fun activate_locale xname = activate_elements [Expr (Locale xname)];



(** print locale **)

fun pretty_locale thy xname =
  let
    val sg = Theory.sign_of thy;
    val name = intern sg xname;
    val {import, elems, params = _, text = _, closed = _} = the_locale thy name;
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
      | prt_elem (Notes facts) = Pretty.big_list "notes" (map prt_fact facts);

    val prt_header = Pretty.block (Pretty.str ("locale " ^ cond_extern sg name ^ " =") ::
       (if import = empty then [] else [Pretty.str " ", prt_expr import] @
         (if null elems then [] else [Pretty.str " +"]) @ [Pretty.brk 1]));
  in Pretty.block (Pretty.fbreaks (prt_header :: map prt_elem elems)) end;

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

fun gen_add_locale prep_expr prep_element bname raw_import raw_elements thy =
  let
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;
    val _ =
      if is_none (get_locale thy name) then () else
      error ("Duplicate definition of locale " ^ quote name);

    val thy_ctxt = ProofContext.init thy;

    val import = prep_expr thy_ctxt raw_import;
    val (import_ids, import_elemss) = split_list (eval_expr thy_ctxt import);
    val import_ctxt = activate_elems (flat import_elemss) thy_ctxt;

    fun prep (ctxt, raw_element) =
      let val elems = map (closeup ctxt) (eval_elements ctxt [prep_element ctxt raw_element]);
      in (activate_elems elems ctxt, elems) end;
    val (locale_ctxt, elemss) = foldl_map prep (import_ctxt, raw_elements);

    val elems = flat elemss;
    val local_ps =  (* FIXME proper types *)
      flat (map (fn Fixes fixes => map (fn (x, T, _) => (x, T)) fixes | _ => []) elems);
    val all_ps = distinct (flat (map #2 import_ids)) @ local_ps;
    val text = ([], []);  (* FIXME *)
  in
    thy
    |> declare_locale name
    |> put_locale name (make_locale import elems (all_ps, local_ps) text false)
  end;

val add_locale = gen_add_locale read_expr read_element;
val add_locale_i = gen_add_locale (K I) (K I);



(** store results **)

fun add_thmss name args thy =
  let
    val {import, params, elems, text, closed} = the_locale thy name;
    val _ = conditional closed (fn () =>
      error ("Cannot store results in closed locale: " ^ quote name));
    val note = Notes (map (fn ((a, ths), atts) =>
      ((a, atts), [(map (curry Thm.name_thm a) ths, [])])) args);
  in
    thy |> ProofContext.init |> activate_locale_i name |> activate_elem note;  (*test attributes!*)
    thy |> put_locale name (make_locale import (elems @ [note]) params text closed)
  end;



(** locale theory setup **)

val setup =
 [LocalesData.init];

end;

structure BasicLocale: BASIC_LOCALE = Locale;
open BasicLocale;
