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
  val attribute: ('att -> context attribute) -> ('typ, 'term, 'thm, 'att) elem_expr
    -> ('typ, 'term, 'thm, context attribute) elem_expr
  val activate_elements: context attribute element list -> context -> context
  val activate_elements_i: context attribute element_i list -> context -> context
  val activate_locale: xstring -> context -> context
  val activate_locale_i: string -> context -> context
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
  params: (string * typ option) list * (string * typ option) list,      (*all vs. local params*)
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
  in
    if null ids then raise ProofContext.CONTEXT (msg, ctxt)
    else raise ProofContext.CONTEXT (msg ^ "\n" ^ Pretty.string_of (Pretty.block
      (Pretty.str "The error(s) above occurred in locale:" :: Pretty.brk 1 :: prt_ids)), ctxt)
  end;



(** operations on locale elements **)

(* prepare elements *)

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

fun read_elem x = prep_elem ProofContext.read_vars ProofContext.read_propp ProofContext.get_thms x;
fun cert_elem x = prep_elem ProofContext.cert_vars ProofContext.cert_propp (K I) x;

fun read_att attrib (x, srcs) = (x, map attrib srcs);

in

fun read_expr ctxt (Locale xname) = Locale (intern (ProofContext.sign_of ctxt) xname)
  | read_expr ctxt (Merge exprs) = Merge (map (read_expr ctxt) exprs)
  | read_expr ctxt (Rename (expr, xs)) = Rename (read_expr ctxt expr, xs);

fun read_element ctxt (Elem e) = Elem (read_elem ctxt e)
  | read_element ctxt (Expr e) = Expr (read_expr ctxt e);

fun cert_element ctxt (Elem e) = Elem (cert_elem ctxt e)
  | cert_element ctxt (Expr e) = Expr e;

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

fun qualify_elem prfx elem =
  let
    fun qualify ((name, atts), x) =
      ((NameSpace.pack (filter_out (equal "") (prfx @ [name])), atts), x);
  in
    (case elem of
      Fixes fixes => Fixes fixes
    | Assumes asms => Assumes (map qualify asms)
    | Defines defs => Defines (map qualify defs)
    | Notes facts => Notes (map qualify facts))
  end;


(* evaluation *)

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
        val {params = (ps, _), elems, ...} = the_locale thy name;
        val ren = filter_out (op =) (map #1 ps ~~ xs);
        val (ps', elems') =
          if null ren then (ps, map #1 elems)
          else (map (apfst (rename ren)) ps, map (rename_elem ren o #1) elems);
      in ((name, ps'), map (qualify_elem [NameSpace.base name, space_implode "_" xs]) elems') end;

    (* FIXME unify types *)

    val (idents, parms) = identify (([], []), expr);
  in (map eval idents, parms) end;

fun eval_element _ (Elem e) = [(("", []), [e])]
  | eval_element ctxt (Expr e) = #1 (eval_expr ctxt e);



(** activation **)

(* internal elems *)

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

fun activate_locale_elems named_elems = ProofContext.qualified (fn context =>
  foldl (fn (ctxt, ((name, ps), es)) =>    (* FIXME type inst *)
    activate_elems es ctxt handle ProofContext.CONTEXT (msg, ctxt) =>
      err_in_locale ctxt msg [(name, map fst ps)]) (context, named_elems));


(* external elements and locales *)

fun gen_activate_elements prep_element raw_elements context =
  foldl (fn (ctxt, e) => activate_locale_elems (eval_element ctxt (prep_element ctxt e)) ctxt)
    (context, raw_elements);

val activate_elements = gen_activate_elements read_element;
val activate_elements_i = gen_activate_elements cert_element;
val activate_locale_i = activate_elements_i o single o Expr o Locale;
val activate_locale = activate_elements o single o Expr o Locale;



(** print locale **)

fun print_locale thy raw_expr =
  let
    val sg = Theory.sign_of thy;
    val thy_ctxt = ProofContext.init thy;

    val expr = read_expr thy_ctxt raw_expr;
    val elems = #1 (eval_expr thy_ctxt expr);
    val ctxt = activate_locale_elems elems thy_ctxt;

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
    Pretty.big_list "locale elements:" (map (Pretty.chunks o prt_elem) (flat (map #2 elems)))
    |> Pretty.writeln
  end;



(** define locales **)

(* closeup -- quantify dangling frees *)

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
    val (import_elems, import_params) = eval_expr thy_ctxt import;
    val import_ctxt = activate_locale_elems import_elems thy_ctxt;

    fun prep (ctxt, raw_element) =
      let val elems = map (apsnd (map (closeup ctxt)))
        (eval_element ctxt (prep_element ctxt raw_element))
      in (activate_locale_elems elems ctxt, flat (map #2 elems)) end;
    val (locale_ctxt, elemss) = foldl_map prep (import_ctxt, raw_elements);

    val elems = flat elemss;
    val local_params =  (* FIXME lookup final types *)
      flat (map (fn Fixes fixes => map (fn (x, T, _) => (x, T)) fixes | _ => []) elems);
    val params = map (rpair None) import_params @ local_params;  (* FIXME *)
    val text = ([], []);  (* FIXME *)
  in
    thy
    |> declare_locale name
    |> put_locale name (make_locale import (map (fn e => (e, stamp ())) elems)
      (params, local_params) text)
  end;

val add_locale = gen_add_locale read_expr read_element;
val add_locale_i = gen_add_locale (K I) (K I);



(** store results **)

fun add_thmss name args thy =
  let
    val {import, params, elems, text} = the_locale thy name;
    val note = Notes (map (fn ((a, ths), atts) =>
      ((a, atts), [(map (curry Thm.name_thm a) ths, [])])) args);
  in
    thy |> ProofContext.init |> activate_locale_i name |> activate_elem note;  (*test attributes!*)
    thy |> put_locale name (make_locale import (elems @ [(note, stamp ())]) params text)
  end;



(** locale theory setup **)

val setup =
 [LocalesData.init];

end;
