(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.  Draws basic ideas from Florian
Kammueller's original version of locales, but uses the rich
infrastructure of Isar instead of the raw meta-logic.

TODO:
  - 'print_locales' command (also PG menu?);
  - cert_elem (do *not* cert_def, yet) (!?);
  - ensure unique defines;
  - local syntax (mostly in ProofContext);
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
  type expression
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
  val store_thm: string -> (string * thm) * context attribute list -> theory -> theory
  val setup: (theory -> theory) list
end;

structure Locale: LOCALE =
struct


(** locale elements and locales **)

type context = ProofContext.context;

type expression = unit;  (* FIXME *)

datatype ('typ, 'term, 'fact, 'att) elem =
  Fixes of (string * 'typ option * mixfix option) list |
  Assumes of ((string * 'att list) * ('term * ('term list * 'term list)) list) list |
  Defines of ((string * 'att list) * ('term * 'term list)) list |
  Notes of ((string * 'att list) * ('fact * 'att list) list) list |
  Uses of expression;

type 'att element = (string, string, string, 'att) elem;
type 'att element_i = (typ, term, thm list, 'att) elem;
type locale = {imports: string list, elements: context attribute element_i list, closed: bool};

fun make_locale imports elements closed =
  {imports = imports, elements = elements, closed = closed}: locale;


fun fixes_of_elem (Fixes fixes) = map #1 fixes
  | fixes_of_elem _ = [];

fun frees_of_elem _ = [];  (* FIXME *)

(*fun close_locale {imports, elements, closed = _} = make_locale imports elements true;*)
fun close_locale x = x;   (* FIXME tmp *)



(** theory data **)

(* data kind 'Pure/locales' *)

structure LocalesArgs =
struct
  val name = "Isar/locales";
  type T = NameSpace.T * locale Symtab.table;

  val empty = (NameSpace.empty, Symtab.empty);
  val copy = I;
  fun prep_ext (space, locales) = (space, Symtab.map close_locale locales);
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


(* print locales *)    (* FIXME activate local syntax *)

fun pretty_locale thy xname =
  let
    val sg = Theory.sign_of thy;
    val name = intern sg xname;
    val {imports, elements, closed = _} = the_locale thy name;

    val prt_typ = Pretty.quote o Sign.pretty_typ sg;
    val prt_term = Pretty.quote o Sign.pretty_term sg;

    fun prt_syn syn =
      let val s = (case syn of None => "(structure)" | Some mx => Syntax.string_of_mixfix mx)
      in if s = "" then [] else [Pretty.brk 4, Pretty.str s] end;
    fun prt_fix (x, Some T, syn) = Pretty.block (Pretty.str (x ^ " ::") :: Pretty.brk 1 ::
          prt_typ T :: Pretty.brk 1 :: prt_syn syn)
      | prt_fix (x, None, syn) = Pretty.block (Pretty.str x :: Pretty.brk 1 :: prt_syn syn);

    fun prt_asm ((a, _), ts) = Pretty.block
      (Pretty.breaks (Pretty.str (a ^ ":") :: map (prt_term o fst) ts));
    fun prt_asms asms = Pretty.block
      (flat (separate [Pretty.fbrk, Pretty.str "and"] (map (single o prt_asm) asms)));

    fun prt_def ((a, _), (t, _)) = Pretty.block
      [Pretty.str (a ^ ":"), Pretty.brk 1, prt_term t];

    fun prt_fact ((a, _), ths) = Pretty.block
      (Pretty.breaks (Pretty.str (a ^ ":") :: map Display.pretty_thm (flat (map fst ths))));

    fun prt_elem (Fixes fixes) = Pretty.big_list "fixes" (map prt_fix fixes)
      | prt_elem (Assumes asms) = Pretty.big_list "assumes" (map prt_asm asms)
      | prt_elem (Defines defs) = Pretty.big_list "defines" (map prt_def defs)
      | prt_elem (Notes facts) = Pretty.big_list "notes" (map prt_fact facts)
      | prt_elem (Uses _) = Pretty.str "FIXME";

    val prt_header = Pretty.block (Pretty.str ("locale " ^ cond_extern sg name ^ " =") ::
       (if null imports then [] else
       (flat (separate [Pretty.str "+", Pretty.brk 1] (map (single o Pretty.str) imports)) @
         [Pretty.str "+"])));
  in Pretty.block (Pretty.fbreaks (prt_header :: map prt_elem elements)) end;

val print_locale = Pretty.writeln oo pretty_locale;



(** internalize elements **)

(* read_elem *)

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
  | Uses FIXME => Uses FIXME;


(* prepare attributes *)

local fun int_att attrib (x, srcs) = (x, map attrib srcs) in

fun attribute _ (Fixes fixes) = Fixes fixes
  | attribute attrib (Assumes asms) = Assumes (map (apfst (int_att attrib)) asms)
  | attribute attrib (Defines defs) = Defines (map (apfst (int_att attrib)) defs)
  | attribute attrib (Notes facts) =
      Notes (map (apfst (int_att attrib) o apsnd (map (int_att attrib))) facts)
  | attribute _ (Uses FIXME) = Uses FIXME;

end;



(** activate locales **)

(* activatation primitive *)

fun activate (ctxt, Fixes fixes) =
      ProofContext.fix_direct (map (fn (x, T, FIXME) => ([x], T)) fixes) ctxt
  | activate (ctxt, Assumes asms) =
      ctxt |> ProofContext.fix_frees (flat (map (map #1 o #2) asms))
      |> ProofContext.assume_i ProofContext.export_assume asms |> #1
  | activate (ctxt, Defines defs) = #1 (ProofContext.assume_i ProofContext.export_def
      (map (fn (a, (t, ps)) => (a, [(ProofContext.cert_def ctxt t, (ps, []))])) defs) ctxt)
  | activate (ctxt, Notes facts) = #1 (ProofContext.have_thmss facts ctxt)
  | activate (ctxt, Uses FIXME) = ctxt;


(* activate operations *)

fun activate_elements_i elems ctxt = foldl activate (ctxt, elems);
fun activate_elements elems ctxt =
  foldl ((fn (ctxt, elem) => activate (ctxt, read_elem ctxt elem))) (ctxt, elems);

fun activate_locale_elements (ctxt, name) =
  let
    val thy = ProofContext.theory_of ctxt;
    val {elements, ...} = the_locale thy name;    (*exception ERROR*)
  in
    activate_elements_i elements ctxt handle ProofContext.CONTEXT (msg, c) =>
      raise ProofContext.CONTEXT (msg ^ "\nThe error(s) above occurred in locale " ^
        quote (cond_extern (Theory.sign_of thy) name), c)
  end;

fun activate_locale_i name ctxt =
  activate_locale_elements (foldl activate_locale_elements
    (ctxt, #imports (the_locale (ProofContext.theory_of ctxt) name)), name);

fun activate_locale xname ctxt =
  activate_locale_i (intern (ProofContext.sign_of ctxt) xname) ctxt;



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
        val t' = ProofContext.cert_def ctxt t;
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
    val imports_ctxt = foldl activate_locale_elements (ProofContext.init thy, imports);
    fun prep (ctxt, raw_elem) =
      let val elem = closeup ctxt (prep_elem ctxt raw_elem)
      in (activate (ctxt, elem), elem) end;
    val (locale_ctxt, elems) = foldl_map prep (imports_ctxt, raw_elems);
  in
    thy
    |> declare_locale name
    |> put_locale name (make_locale imports elems false)
  end;

val add_locale = gen_add_locale intern read_elem;
val add_locale_i = gen_add_locale (K I) (K I);



(** store results **)    (* FIXME test atts!? *)

fun store_thm name ((a, th), atts) thy =
  let
    val note = Notes [((a, atts), [([Thm.name_thm (a, th)], [])])];
    val {imports, elements, closed} = the_locale thy name;
  in
    if closed then error ("Cannot store results in closed locale: " ^ quote name)
    else thy |> put_locale name (make_locale imports (elements @ [note]) closed)
  end;


(* FIXME old

        val mx = Syntax.fix_mixfix raw_c raw_mx;
        val (envS', T) = prep_typ sign (envS, raw_T) handle ERROR =>
          error ("The error(s) above occured in locale constant " ^ quote c);
        val trfun = if mx = Syntax.NoSyn then None else Some (c_syn, mk_loc_tr c);
      in (envS', ((c, T), (c_syn, T, mx), trfun)) end;

    val (envS0, loc_fixes_syn) = foldl_map prep_const (envSb, raw_fixes);
    val loc_fixes = map #1 loc_fixes_syn;
    val loc_fixes = old_loc_fixes @ loc_fixes;
    val loc_syn = map #2 loc_fixes_syn;
    val nosyn = old_nosyn @ (map (#1 o #1) (filter (fn x => (#3(#2 x)) = NoSyn) loc_fixes_syn));
    val loc_trfuns = mapfilter #3 loc_fixes_syn;

    val syntax_thy =
      thy
      |> Theory.add_modesyntax_i ("", true) loc_syn
      |> Theory.add_trfuns ([], loc_trfuns, [], []);

    (* check if definientes are locale constants
       (in the same locale, so no redefining!) *)
    val err_def_head =
      let fun peal_appl t =
            case t of
                 t1 $ t2 => peal_appl t1
               | Free(t) => t
               | _ => locale_error ("Bad form of LHS in locale definition");
          fun lhs (_, Const ("==" , _) $  d1 $ d2) = peal_appl d1
            | lhs _ = locale_error ("Definitions must use the == relation");
          val defs = map lhs loc_defs;
          val check = defs subset loc_fixes
      in if check then []
         else ["defined item not declared fixed in locale " ^ quote name]
      end;

    (* check that variables on rhs of definitions are either fixed or on lhs *)
    val err_var_rhs =
      let fun compare_var_sides (t, (_, Const ("==", _) $ d1 $ d2)) =
                let val varl1 = difflist d1 all_loc_fixes;
                    val varl2 = difflist d2 all_loc_fixes
                in t andalso (varl2 subset varl1)
                end
            | compare_var_sides (_,_) =
                locale_error ("Definitions must use the == relation")
          val check = foldl compare_var_sides (true, loc_defs)
      in if check then []
         else ["nonfixed variable on right hand side of a locale definition in locale " ^ quote name]
      end;
*)


(** locale theory setup **)

val setup =
 [LocalesData.init];

end;

structure BasicLocale: BASIC_LOCALE = Locale;
open BasicLocale;
