(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.

TODO:
  - reset scope context on qed of legacy goal (!??);
  - implicit closure of ``loose'' free vars;
  - avoid dynamic scoping of facts/atts
    (use thms_closure for globals, even within att expressions);
  - scope of implicit fixed in elementents vs. locales (!??);
  - remove scope stuff;
*)

signature BASIC_LOCALE =
sig
  val print_locales: theory -> unit
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
  val intern_att: ('att -> context attribute) ->
    ('typ, 'term, 'thm, 'att) elem -> ('typ, 'term, 'thm, context attribute) elem
  val activate_elements: context attribute element list -> context -> context
  val activate_elements_i: context attribute element_i list -> context -> context
  val activate_locale: xstring -> context -> context
  val activate_locale_i: string -> context -> context
(*
  val add_locale: bstring -> xstring option -> (string * string * mixfix) list ->
    ((string * context attribute list) * string) list ->
    ((string * context attribute list) * string) list -> theory -> theory
  val add_locale_i: bstring -> xstring option -> (string * typ * mixfix) list ->
    ((string * context attribute list) * term) list ->
    ((string * context attribute list) * term) list -> theory -> theory
  val read_prop_schematic: Sign.sg -> string -> cterm
*)
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
type locale = (thm -> string) * string list * context attribute element_i list;


fun fixes_of_elem (Fixes fixes) = map #1 fixes
  | fixes_of_elem _ = [];

fun frees_of_elem _ = [];  (* FIXME *)



(** theory data **)

(* data kind 'Pure/locales' *)

type locale_data =
  {space: NameSpace.T,
    locales: locale Symtab.table,
    scope: ((string * locale) list * context option) ref};

fun make_locale_data space locales scope =
  {space = space, locales = locales, scope = scope}: locale_data;

val empty_scope = ([], None);

structure LocalesArgs =
struct
  val name = "Isar/locales";
  type T = locale_data;

  val empty = make_locale_data NameSpace.empty Symtab.empty (ref empty_scope);
  fun copy {space, locales, scope = ref r} = make_locale_data space locales (ref r);
  fun prep_ext {space, locales, scope = _} = make_locale_data space locales (ref empty_scope);
  fun merge ({space = space1, locales = locales1, scope = _},
    {space = space2, locales = locales2, scope = _}) =
      make_locale_data (NameSpace.merge (space1, space2))
        (Symtab.merge (K true) (locales1, locales2)) (ref empty_scope);

  fun print _ {space, locales, scope = _} =
    Pretty.strs ("locales:" :: map (NameSpace.cond_extern space o #1) (Symtab.dest locales))
    |> Pretty.writeln;
end;

structure LocalesData = TheoryDataFun(LocalesArgs);
val print_locales = LocalesData.print;

val intern = NameSpace.intern o #space o LocalesData.get_sg;
val cond_extern = NameSpace.cond_extern o #space o LocalesData.get_sg;


(* access locales *)

fun get_locale_sg sg name = Symtab.lookup (#locales (LocalesData.get_sg sg), name);
val get_locale = get_locale_sg o Theory.sign_of;

fun put_locale (name, locale) = LocalesData.map (fn {space, locales, scope} =>
  make_locale_data (NameSpace.extend (space, [name]))
    (Symtab.update ((name, locale), locales)) scope);

fun the_locale thy name =
  (case get_locale thy name of
    Some loc => loc
  | None => error ("Unknown locale " ^ quote name));


(* access scope *)

fun get_scope_sg sg =
  if Sign.eq_sg (sg, Theory.sign_of ProtoPure.thy) then empty_scope
  else ! (#scope (LocalesData.get_sg sg));

val get_scope = get_scope_sg o Theory.sign_of;
val nonempty_scope_sg = not o null o #1 o get_scope_sg;

fun change_scope f thy =
  let val {scope, ...} = LocalesData.get thy
  in scope := f (! scope); thy end;

fun print_scope thy =
  Pretty.writeln (Pretty.strs ("current scope:" ::
    rev (map (cond_extern (Theory.sign_of thy) o #1) (#1 (get_scope thy)))));


(* print locales *)    (* FIXME activate local syntax *)

fun pretty_locale thy xname =
  let
    val sg = Theory.sign_of thy;
    val name = intern sg xname;
    val (_, ancestors, elements) = the_locale thy name;

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
       (if null ancestors then [] else
       (flat (separate [Pretty.str "+", Pretty.brk 1] (map (single o Pretty.str) ancestors)) @
         [Pretty.str "+"])));
  in Pretty.block (Pretty.fbreaks (prt_header :: map prt_elem elements)) end;

val print_locale = Pretty.writeln oo pretty_locale;


(** internalization of theorems and attributes **)

fun int_att attrib (x, srcs) = (x, map attrib srcs);

fun intern_att _ (Fixes fixes) = Fixes fixes
  | intern_att attrib (Assumes asms) = Assumes (map (apfst (int_att attrib)) asms)
  | intern_att attrib (Defines defs) = Defines (map (apfst (int_att attrib)) defs)
  | intern_att attrib (Notes facts) =
      Notes (map (apfst (int_att attrib) o apsnd (map (int_att attrib))) facts)
  | intern_att _ (Uses FIXME) = Uses FIXME;



(** activate locales **)

fun close_frees ctxt t =
  let val frees = rev (filter_out (ProofContext.is_fixed ctxt o #1) (Drule.add_frees ([], t)))
  in Term.list_all_free (frees, t) end;

fun read_elem ctxt =
 fn (Fixes fixes) =>
      let val vars =
        #2 (foldl_map ProofContext.read_vars (ctxt, map (fn (x, T, _) => ([x], T)) fixes))
      in Fixes (map2 (fn (([x'], T'), (_, _, mx)) => (x', T', mx)) (vars, fixes)) end
  | (Assumes asms) =>
      Assumes (map #1 asms ~~ #2 (ProofContext.read_propp (ctxt, map #2 asms)))
  | (Defines defs) =>
      let val propps =
        #2 (ProofContext.read_propp (ctxt, map (fn (_, (t, ps)) => [(t, (ps, []))]) defs))
      in Defines (map #1 defs ~~ map (fn [(t', (ps', []))] => (t', ps')) propps) end
  | (Notes facts) =>
      Notes (map (apsnd (map (apfst (ProofContext.get_thms ctxt)))) facts)
  | (Uses FIXME) => Uses FIXME;


fun activate (ctxt, Fixes fixes) =
      ProofContext.fix_direct (map (fn (x, T, FIXME) => ([x], T)) fixes) ctxt
  | activate (ctxt, Assumes asms) =
      ctxt |> ProofContext.fix_frees (flat (map (map #1 o #2) asms))
      |> ProofContext.assume_i ProofContext.export_assume asms |> #1
  | activate (ctxt, Defines defs) = #1 (ProofContext.assume_i ProofContext.export_def
      (map (fn (a, (t, ps)) => (a, [(ProofContext.cert_def ctxt t, (ps, []))])) defs) ctxt)
  | activate (ctxt, Notes facts) = #1 (ProofContext.have_thmss facts ctxt)
  | activate (ctxt, Uses FIXME) = ctxt;

fun read_activate (ctxt, elem) =
  let val elem' = read_elem ctxt elem
  in (activate (ctxt, elem'), elem') end;

fun activate_elements_i elems ctxt = foldl activate (ctxt, elems);
fun activate_elements elems ctxt = foldl (#1 o read_activate) (ctxt, elems);

fun with_locale f name ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val locale = the_locale thy name;
  in
    f locale ctxt handle ProofContext.CONTEXT (msg, c) =>
      raise ProofContext.CONTEXT (msg ^ "\nThe error(s) above occurred in locale " ^
        quote (cond_extern (Theory.sign_of thy) name), c)
  end;

val activate_locale_elements = with_locale (activate_elements_i o #3);

fun activate_locale_ancestors name ctxt =
  foldl (fn (c, es) => activate_locale_elements es c)
    (ctxt, #2 (the_locale (ProofContext.theory_of ctxt) name));

fun activate_locale_i name ctxt =
  ctxt |> activate_locale_ancestors name |> activate_locale_elements name;

fun activate_locale xname ctxt =
  activate_locale_i (intern (ProofContext.sign_of ctxt) xname) ctxt;



(* FIXME
(** define locales **)

(* concrete syntax *)

fun mark_syn c = "\\<^locale>" ^ c;

fun mk_loc_tr c ts = list_comb (Free (c, dummyT), ts);


(* add_locale *)

fun gen_add_locale prep_typ prep_term bname bpar raw_fixes raw_assumes raw_defs thy =
  let val sign = Theory.sign_of thy;

    val name = Sign.full_name sign bname;

    val (envSb, old_loc_fixes, _) =
                    case bpar of
                       Some loc => (get_defaults thy loc)
                     | None      => ([],[],[]);

    val old_nosyn = case bpar of
                       Some loc => #nosyn(#2(the_locale thy loc))
                     | None      => [];

    (* Get the full name of the parent *)
    val parent = case bparent of
                       Some loc => Some(#1(the_locale thy loc))
                     | None      => None;

     (* prepare locale fixes *)

    fun prep_const (envS, (raw_c, raw_T, raw_mx)) =
      let
        val c = Syntax.const_name raw_c raw_mx;
        val c_syn = mark_syn c;
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


    (* 1st stage: syntax_thy *)

    val syntax_thy =
      thy
      |> Theory.add_modesyntax_i ("", true) loc_syn
      |> Theory.add_trfuns ([], loc_trfuns, [], []);

    val syntax_sign = Theory.sign_of syntax_thy;


    (* prepare assumes and defs *)

    fun prep_axiom (env, (a, raw_t)) =
      let
        val (env', t) = prep_term syntax_sign (env, (a, raw_t)) handle ERROR =>
          error ("The error(s) above occured in locale rule / definition " ^ quote a);
      in (env', (a, t)) end;

    val ((envS1, envT1, used1), loc_assumes) =
      foldl_map prep_axiom ((envS0, loc_fixes, map fst envS0), raw_assumes);
    val (defaults, loc_defs) =
        foldl_map prep_axiom ((envS1, envT1, used1), raw_defs);

    val old_loc_fixes = collect_fixes syntax_sign;
    val new_loc_fixes = (map #1 loc_fixes);
    val all_loc_fixes = old_loc_fixes @ new_loc_fixes;

    val (defaults, loc_defs_terms) =
        foldl_map (abs_over_free all_loc_fixes) (defaults, loc_defs);
    val loc_defs_thms =
        map (apsnd (prep_hyps (map #1 loc_fixes) syntax_sign)) loc_defs_terms;
    val (defaults, loc_thms_terms) =
        foldl_map (abs_over_free all_loc_fixes) (defaults, loc_assumes);
    val loc_thms = map (apsnd (prep_hyps (map #1 loc_fixes) syntax_sign))
                       (loc_thms_terms)
                   @ loc_defs_thms;


    (* error messages *)

    fun locale_error msg = error (msg ^ "\nFor locale " ^ quote name);

    val err_dup_locale =
      if is_none (get_locale thy name) then []
      else ["Duplicate definition of locale " ^ quote name];

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

    val errs = err_dup_locale @ err_def_head @ err_var_rhs;
  in
    if null errs then ()
    else error (cat_lines errs);

    syntax_thy
    |> put_locale (name,
                   make_locale parent loc_fixes nosyn loc_thms_terms
                                        loc_defs_terms   loc_thms defaults)
  end;


val add_locale = gen_add_locale read_typ read_axm;
val add_locale_i = gen_add_locale cert_typ cert_axm;



(*
(** support for legacy proof scripts (cf. goals.ML) **)     (* FIXME move to goals.ML (!?) *)

(* hyps_in_scope *)

fun hyps_in_scope sg hyps =
  let val locs = map #2 (#1 (get_scope_sg sg))
  in gen_subset Term.aconv (hyps, map #2 (flat (map #assumes locs @ map #defines locs))) end;


(* get theorems *)

fun thmx get_local get_global name =
  let val thy = Context.the_context () in
    (case #2 (get_scope thy) of
      None => get_global thy name
    | Some ctxt => get_local ctxt name)
  end;

val thm = thmx ProofContext.get_thm PureThy.get_thm;
val thms = thmx ProofContext.get_thms PureThy.get_thms;


(** scope operations -- for old-style goals **)  (* FIXME move to goals.ML (!?) *)

(* open *)

local

fun is_open thy name = exists (equal name o #1) (#1 (get_scope thy));

fun open_loc thy name =
  let
    val (ancestors, elements) = the_locale thy name;
  in
    (case #parent locale of None => thy
    | Some par =>
        if is_open thy par then thy
        else (writeln ("Opening locale " ^ quote par ^ "(required by " ^ quote name ^ ")");
          open_loc name thy))
    |> change_scope (fn (locs, _) => ((name, locale) :: locs, None))
  end;

in

fun open_locale xname thy =
  let val name = intern (Theory.sign_of thy) xname in
    if is_open thy name then (warning ("Locale " ^ quote name ^ " already open"); thy)
    else open_loc name thy
  end;

end;


(* close *)

fun close_locale xname thy =
  let val name = intern_locale (Theory.sign_of thy) xname in
    thy |> change_scope (fn ([], _) => error "Currently no open locales"
    | ((name', _) :: locs, _) =>
        if name <> name' then error ("Locale " ^ quote name ^ " not at top of scope")
        else (locs, None))
  end;


(* implicit context versions *)

fun Open_locale xname = (open_locale xname (Context.the_context ()); ());
fun Close_locale xname = (close_locale xname (Context.the_context ()); ());
fun Print_scope () = (print_scope (Context.the_context ()); ());
*)


(** locale theory setup **)
*)
val setup =
 [LocalesData.init];

end;

structure BasicLocale: BASIC_LOCALE = Locale;
open BasicLocale;
