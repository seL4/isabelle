(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Clemens Ballarin, TU Muenchen; Markus Wenzel, LMU/TU Muenchen

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.

Draws some basic ideas from Florian Kammueller's original version of
locales, but uses the richer infrastructure of Isar instead of the raw
meta-logic.  Furthermore, we provide structured import of contexts
(with merge and rename operations), as well as type-inference of the
signature parts, and predicate definitions of the specification text.

See also:

[1] Clemens Ballarin. Locales and Locale Expressions in Isabelle/Isar.
    In Stefano Berardi et al., Types for Proofs and Programs: International
    Workshop, TYPES 2003, Torino, Italy, LNCS 3085, pages 34-50, 2004.
*)

signature LOCALE =
sig
  type context
  datatype ('typ, 'term, 'fact) elem =
    Fixes of (string * 'typ option * mixfix option) list |
    Assumes of ((string * Attrib.src list) * ('term * ('term list * 'term list)) list) list |
    Defines of ((string * Attrib.src list) * ('term * 'term list)) list |
    Notes of ((string * Attrib.src list) * ('fact * Attrib.src list) list) list
  datatype expr =
    Locale of string |
    Rename of expr * string option list |
    Merge of expr list
  val empty: expr
  datatype 'a elem_expr = Elem of 'a | Expr of expr

  (* Abstract interface to locales *)
  type element
  type element_i
  type locale
  val intern: Sign.sg -> xstring -> string
  val cond_extern: Sign.sg -> string -> xstring
  val the_locale: theory -> string -> locale
  val intern_attrib_elem: theory ->
    ('typ, 'term, 'fact) elem -> ('typ, 'term, 'fact) elem
  val intern_attrib_elem_expr: theory ->
    ('typ, 'term, 'fact) elem elem_expr -> ('typ, 'term, 'fact) elem elem_expr

  (* Processing of locale statements *)
  val read_context_statement: xstring option -> element elem_expr list ->
    (string * (string list * string list)) list list -> context ->
    string option * (cterm list * cterm list) * context * context * 
      (term * (term list * term list)) list list
  val cert_context_statement: string option -> element_i elem_expr list ->
    (term * (term list * term list)) list list -> context ->
    string option * (cterm list * cterm list) * context * context *
      (term * (term list * term list)) list list

  (* Diagnostic functions *)
  val print_locales: theory -> unit
  val print_locale: theory -> expr -> element list -> unit
  val print_global_registrations: string -> theory -> unit
  val print_local_registrations': string -> context -> unit
  val print_local_registrations: string -> context -> unit

  (* Storing results *)
  val add_locale: bool -> bstring -> expr -> element list -> theory -> theory
  val add_locale_i: bool -> bstring -> expr -> element_i list -> theory -> theory
  val smart_note_thmss: string -> string option ->
    ((bstring * theory attribute list) * (thm list * theory attribute list) list) list ->
    theory -> theory * (bstring * thm list) list
  val note_thmss: string -> xstring ->
    ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list ->
    theory -> theory * (bstring * thm list) list
  val note_thmss_i: string -> string ->
    ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    theory -> theory * (bstring * thm list) list
  val add_thmss: string -> string -> ((string * thm list) * Attrib.src list) list ->
    theory * context -> (theory * context) * (string * thm list) list

  (* Locale interpretation *)
  val instantiate: string -> string * context attribute list
    -> thm list option -> context -> context
  val prep_global_registration:
    string * Attrib.src list -> expr -> string option list -> theory ->
    theory * ((string * term list) * term list) list * (theory -> theory)
  val prep_local_registration:
    string * Attrib.src list -> expr -> string option list -> context ->
    context * ((string * term list) * term list) list * (context -> context)
  val add_global_witness:
    string * term list -> thm -> theory -> theory
  val add_local_witness:
    string * term list -> thm -> context -> context
end;

structure Locale: LOCALE =
struct

(** locale elements and expressions **)

type context = ProofContext.context;

datatype ('typ, 'term, 'fact) elem =
  Fixes of (string * 'typ option * mixfix option) list |
  Assumes of ((string * Attrib.src list) * ('term * ('term list * 'term list)) list) list |
  Defines of ((string * Attrib.src list) * ('term * 'term list)) list |
  Notes of ((string * Attrib.src list) * ('fact * Attrib.src list) list) list;

datatype expr =
  Locale of string |
  Rename of expr * string option list |
  Merge of expr list;

val empty = Merge [];

datatype 'a elem_expr =
  Elem of 'a | Expr of expr;

type element = (string, string, thmref) elem;
type element_i = (typ, term, thm list) elem;

type locale =
 {predicate: cterm list * thm list,
    (* CB: For old-style locales with "(open)" this entry is ([], []).
       For new-style locales, which declare predicates, if the locale declares
       no predicates, this is also ([], []).
       If the locale declares predicates, the record field is
       ([statement], axioms), where statement is the locale predicate applied
       to the (assumed) locale parameters.  Axioms contains the projections
       from the locale predicate to the normalised assumptions of the locale
       (cf. [1], normalisation of locale expressions.)
    *)
  import: expr,                                       (*dynamic import*)
  elems: (element_i * stamp) list,                    (*static content*)
  params: (string * typ option) list * string list}   (*all/local params*)


(* CB: an internal (Int) locale element was either imported or included,
   an external (Ext) element appears directly in the locale text. *)

datatype ('a, 'b) int_ext = Int of 'a | Ext of 'b;



(** term and type instantiation, using symbol tables **)

(* instantiate TFrees *)

fun tinst_tab_type tinst T = if Symtab.is_empty tinst
      then T
      else Term.map_type_tfree
        (fn (v as (x, _)) => getOpt (Symtab.lookup (tinst, x), (TFree v))) T;

fun tinst_tab_term tinst t = if Symtab.is_empty tinst
      then t
      else Term.map_term_types (tinst_tab_type tinst) t;

fun tinst_tab_thm sg tinst thm = if Symtab.is_empty tinst
      then thm
      else let
          val cert = Thm.cterm_of sg;
          val certT = Thm.ctyp_of sg;
          val {hyps, prop, ...} = Thm.rep_thm thm;
          val tfrees = foldr Term.add_term_tfree_names [] (prop :: hyps);
          val tinst' = Symtab.dest tinst |>
                List.filter (fn (a, _) => a mem_string tfrees);
        in
          if null tinst' then thm
          else thm |> Drule.implies_intr_list (map cert hyps)
            |> Drule.tvars_intr_list (map #1 tinst')
            |> (fn (th, al) => th |> Thm.instantiate
                ((map (fn (a, T) => (certT (TVar (valOf (assoc (al, a)))), certT T)) tinst'),
                  []))
            |> (fn th => Drule.implies_elim_list th
                 (map (Thm.assume o cert o tinst_tab_term tinst) hyps))
        end;


(* instantiate TFrees and Frees *)

fun inst_tab_term (inst, tinst) = if Symtab.is_empty inst
      then tinst_tab_term tinst
      else (* instantiate terms and types simultaneously *)
        let
          fun instf (Const (x, T)) = Const (x, tinst_tab_type tinst T)
            | instf (Free (x, T)) = (case Symtab.lookup (inst, x) of
                 NONE => Free (x, tinst_tab_type tinst T)
               | SOME t => t)
            | instf (Var (xi, T)) = Var (xi, tinst_tab_type tinst T)
            | instf (b as Bound _) = b
            | instf (Abs (x, T, t)) = Abs (x, tinst_tab_type tinst T, instf t)
            | instf (s $ t) = instf s $ instf t
        in instf end;

fun inst_tab_thm sg (inst, tinst) thm = if Symtab.is_empty inst
      then tinst_tab_thm sg tinst thm
      else let
          val cert = Thm.cterm_of sg;
          val certT = Thm.ctyp_of sg;
          val {hyps, prop, ...} = Thm.rep_thm thm;
          (* type instantiations *)
          val tfrees = foldr Term.add_term_tfree_names [] (prop :: hyps);
          val tinst' = Symtab.dest tinst |>
                List.filter (fn (a, _) => a mem_string tfrees);
          (* term instantiations;
             note: lhss are type instantiated, because
                   type insts will be done first*)
          val frees = foldr Term.add_term_frees [] (prop :: hyps);
          val inst' = Symtab.dest inst |>
                List.mapPartial (fn (a, t) =>
                  get_first (fn (Free (x, T)) => 
                    if a = x then SOME (Free (x, tinst_tab_type tinst T), t)
                    else NONE) frees);
        in
          if null tinst' andalso null inst' then tinst_tab_thm sg tinst thm
          else thm |> Drule.implies_intr_list (map cert hyps)
            |> Drule.tvars_intr_list (map #1 tinst')
            |> (fn (th, al) => th |> Thm.instantiate
                ((map (fn (a, T) => (certT (TVar (valOf (assoc (al, a)))), certT T)) tinst'),
                  []))
            |> Drule.forall_intr_list (map (cert o #1) inst')
            |> Drule.forall_elim_list (map (cert o #2) inst') 
            |> (fn th => Drule.implies_elim_list th
                 (map (Thm.assume o cert o inst_tab_term (inst, tinst)) hyps))
        end;


(** registration management **)

structure Registrations :
  sig
    type T
    val empty: T
    val join: T * T -> T
    val dest: T -> (term list * ((string * Attrib.src list) * thm list)) list
    val lookup: Sign.sg -> T * term list ->
      ((string * Attrib.src list) * thm list) option
    val insert: Sign.sg -> term list * (string * Attrib.src list) -> T ->
      T * (term list * ((string * Attrib.src list) * thm list)) list
    val add_witness: term list -> thm -> T -> T
  end =
struct
  (* a registration consists of theorems instantiating locale assumptions
     and prefix and attributes, indexed by parameter instantiation *)
  type T = ((string * Attrib.src list) * thm list) Termtab.table;

  val empty = Termtab.empty;

  (* term list represented as single term, for simultaneous matching *)
  fun termify ts =
    Library.foldl (op $) (Const ("", map fastype_of ts ---> propT), ts);
  fun untermify t =
    let fun ut (Const _) ts = ts
          | ut (s $ t) ts = ut s (t::ts)
    in ut t [] end;

  (* joining of registrations: prefix and attributs of left theory,
     thms are equal, no attempt to subsumption testing *)
  fun join x = Termtab.join (fn (reg, _) => SOME reg) x;

  fun dest regs = map (apfst untermify) (Termtab.dest regs);

  (* registrations that subsume t *)
  fun subsumers tsig t regs =
    List.filter (fn (t', _) => Pattern.matches tsig (t', t)) (Termtab.dest regs);

  (* look up registration, pick one that subsumes the query *)
  fun lookup sign (regs, ts) =
    let
      val tsig = Sign.tsig_of sign;
      val t = termify ts;
      val subs = subsumers tsig t regs;
    in (case subs of
        [] => NONE
      | ((t', (attn, thms)) :: _) => let
            val (tinst, inst) = Pattern.match tsig (t', t);
            (* thms contain Frees, not Vars *)
            val tinst' = tinst |> Vartab.dest
                 |> map (fn ((x, 0), (_, T)) => (x, Type.unvarifyT T))
                 |> Symtab.make;
            val inst' = inst |> Vartab.dest
                 |> map (fn ((x, 0), (_, t)) => (x, Logic.unvarify t))
                 |> Symtab.make;
          in
            SOME (attn, map (inst_tab_thm sign (inst', tinst')) thms)
          end)
    end;

  (* add registration if not subsumed by ones already present,
     additionally returns registrations that are strictly subsumed *)
  fun insert sign (ts, attn) regs =
    let
      val tsig = Sign.tsig_of sign;
      val t = termify ts;
      val subs = subsumers tsig t regs ;
    in (case subs of
        [] => let
                val sups =
                  List.filter (fn (t', _) => Pattern.matches tsig (t, t')) (Termtab.dest regs);
                val sups' = map (apfst untermify) sups
              in (Termtab.update ((t, (attn, [])), regs), sups') end
      | _ => (regs, []))
    end;

  (* add witness theorem to registration,
     only if instantiation is exact, otherwise excpetion Option raised *)
  fun add_witness ts thm regs =
    let
      val t = termify ts;
      val (x, thms) = valOf (Termtab.lookup (regs, t));
    in
      Termtab.update ((t, (x, thm::thms)), regs)
    end;
end;

(** theory data **)

structure GlobalLocalesArgs =
struct
  val name = "Isar/locales";
  type T = NameSpace.T * locale Symtab.table * Registrations.T Symtab.table;
    (* 1st entry: locale namespace,
       2nd entry: locales of the theory,
       3rd entry: registrations, indexed by locale name *)

  val empty = (NameSpace.empty, Symtab.empty, Symtab.empty);
  val copy = I;
  val prep_ext = I;

  fun join_locs ({predicate, import, elems, params}: locale,
      {elems = elems', ...}: locale) =
    SOME {predicate = predicate, import = import,
      elems = gen_merge_lists eq_snd elems elems',
      params = params};
  fun merge ((space1, locs1, regs1), (space2, locs2, regs2)) =
    (NameSpace.merge (space1, space2), Symtab.join join_locs (locs1, locs2),
     Symtab.join (SOME o Registrations.join) (regs1, regs2));

  fun print _ (space, locs, _) =
    Pretty.strs ("locales:" :: map (NameSpace.cond_extern space o #1) (Symtab.dest locs))
    |> Pretty.writeln;
end;

structure GlobalLocalesData = TheoryDataFun(GlobalLocalesArgs);
val _ = Context.add_setup [GlobalLocalesData.init];



(** context data **)

structure LocalLocalesArgs =
struct
  val name = "Isar/locales";
  type T = Registrations.T Symtab.table;
    (* registrations, indexed by locale name *)
  fun init _ = Symtab.empty;
  fun print _ _ = ();
end;

structure LocalLocalesData = ProofDataFun(LocalLocalesArgs);
val _ = Context.add_setup [LocalLocalesData.init];


(* access locales *)

val print_locales = GlobalLocalesData.print;

val intern = NameSpace.intern o #1 o GlobalLocalesData.get_sg;
val cond_extern = NameSpace.cond_extern o #1 o GlobalLocalesData.get_sg;

fun declare_locale name =
  GlobalLocalesData.map (fn (space, locs, regs) =>
    (NameSpace.extend (space, [name]), locs, regs));

fun put_locale name loc =
  GlobalLocalesData.map (fn (space, locs, regs) =>
    (space, Symtab.update ((name, loc), locs), regs));

fun get_locale thy name = Symtab.lookup (#2 (GlobalLocalesData.get thy), name);

fun the_locale thy name =
  (case get_locale thy name of
    SOME loc => loc
  | NONE => error ("Unknown locale " ^ quote name));


(* access registrations *)

(* Ids of global registrations are varified,
   Ids of local registrations are not.
   Thms of registrations are never varified. *)

(* retrieve registration from theory or context *)

fun gen_get_registrations get thy_ctxt name =
  case Symtab.lookup (get thy_ctxt, name) of
      NONE => []
    | SOME reg => Registrations.dest reg;

val get_global_registrations =
     gen_get_registrations (#3 o GlobalLocalesData.get);
val get_local_registrations =
     gen_get_registrations LocalLocalesData.get;

fun gen_get_registration get get_sg thy_ctxt (name, ps) =
  case Symtab.lookup (get thy_ctxt, name) of
      NONE => NONE
    | SOME reg => Registrations.lookup (get_sg thy_ctxt) (reg, ps);

val get_global_registration =
     gen_get_registration (#3 o GlobalLocalesData.get) Theory.sign_of;
val get_local_registration =
     gen_get_registration LocalLocalesData.get ProofContext.sign_of;

val test_global_registration = isSome oo get_global_registration;
val test_local_registration = isSome oo get_local_registration;
fun smart_test_registration ctxt id =
  let
    val thy = ProofContext.theory_of ctxt;
  in
    test_global_registration thy id orelse test_local_registration ctxt id
  end;


(* add registration to theory or context, ignored if subsumed *)

fun gen_put_registration map_data get_sg (name, ps) attn thy_ctxt =
  map_data (fn regs =>
    let
      val sg = get_sg thy_ctxt;
      val reg = getOpt (Symtab.lookup (regs, name), Registrations.empty);
      val (reg', sups) = Registrations.insert sg (ps, attn) reg;
      val _ = if not (null sups) then warning
                ("Subsumed interpretation(s) of locale " ^
                 quote (cond_extern sg name) ^
                 "\nby interpretation(s) with the following prefix(es):\n" ^
                  commas_quote (map (fn (_, ((s, _), _)) => s) sups))
              else ();
    in Symtab.update ((name, reg'), regs) end) thy_ctxt;

val put_global_registration =
     gen_put_registration (fn f =>
       GlobalLocalesData.map (fn (space, locs, regs) =>
         (space, locs, f regs))) Theory.sign_of;
val put_local_registration =
     gen_put_registration LocalLocalesData.map ProofContext.sign_of;

(* TODO: needed? *)
(*
fun smart_put_registration id attn ctxt =
  (* ignore registration if already present in theory *)
     let
       val thy = ProofContext.theory_of ctxt;
     in case get_global_registration thy id of
          NONE => put_local_registration id attn ctxt
        | SOME _ => ctxt
     end;
*)

(* add witness theorem to registration in theory or context,
   ignored if registration not present *)

fun gen_add_witness map (name, ps) thm =
  map (fn regs =>
      let
        val reg = valOf (Symtab.lookup (regs, name));
      in
        Symtab.update ((name, Registrations.add_witness ps thm reg), regs)
      end handle Option => regs);

val add_global_witness =
     gen_add_witness (fn f =>
       GlobalLocalesData.map (fn (space, locs, regs) =>
         (space, locs, f regs)));
val add_local_witness = gen_add_witness LocalLocalesData.map;


(* import hierarchy
   implementation could be more efficient, eg. by maintaining a database
   of dependencies *)

fun imports thy (upper, lower) =
  let
    val sign = sign_of thy;
    fun imps (Locale name) low = (name = low) orelse
      (case get_locale thy name of
           NONE => false
         | SOME {import, ...} => imps import low)
      | imps (Rename (expr, _)) low = imps expr low
      | imps (Merge es) low = exists (fn e => imps e low) es;
  in
    imps (Locale (intern sign upper)) (intern sign lower)
  end;


(* printing of registrations *)

fun gen_print_registrations get_regs mk_ctxt msg loc thy_ctxt =
  let
    val ctxt = mk_ctxt thy_ctxt;
    val thy = ProofContext.theory_of ctxt;
    val sg = Theory.sign_of thy;

    val prt_term = Pretty.quote o ProofContext.pretty_term ctxt;
    val prt_atts = Args.pretty_attribs ctxt;
    fun prt_inst (ts, (("", []), thms)) =
          Pretty.enclose "(" ")" (Pretty.breaks (map prt_term ts))
      | prt_inst (ts, ((prfx, atts), thms)) =
          Pretty.block (
            (Pretty.breaks (Pretty.str prfx :: prt_atts atts) @
              [Pretty.str ":", Pretty.brk 1,
                Pretty.enclose "(" ")" (Pretty.breaks (map prt_term ts))]));

    val loc_int = intern sg loc;
    val regs = get_regs thy_ctxt;
    val loc_regs = Symtab.lookup (regs, loc_int);
  in
    (case loc_regs of
        NONE => Pretty.str ("No interpretations in " ^ msg ^ ".")
      | SOME r => let
            val r' = Registrations.dest r;
            val r'' = Library.sort_wrt (fn (_, ((prfx, _), _)) => prfx) r';
          in Pretty.big_list ("Interpretations in " ^ msg ^ ":")
            (map prt_inst r'')
          end)
    |> Pretty.writeln
  end;

val print_global_registrations =
     gen_print_registrations (#3 o GlobalLocalesData.get)
       ProofContext.init "theory";
val print_local_registrations' =
     gen_print_registrations LocalLocalesData.get
       I "context";
fun print_local_registrations loc ctxt =
  (print_global_registrations loc (ProofContext.theory_of ctxt);
   print_local_registrations' loc ctxt);


(* diagnostics *)

fun err_in_locale ctxt msg ids =
  let
    val sign = ProofContext.sign_of ctxt;
    fun prt_id (name, parms) =
      [Pretty.block (Pretty.breaks (map Pretty.str (cond_extern sign name :: parms)))];
    val prt_ids = List.concat (separate [Pretty.str " +", Pretty.brk 1] (map prt_id ids));
    val err_msg =
      if forall (equal "" o #1) ids then msg
      else msg ^ "\n" ^ Pretty.string_of (Pretty.block
        (Pretty.str "The error(s) above occurred in locale:" :: Pretty.brk 1 :: prt_ids));
  in raise ProofContext.CONTEXT (err_msg, ctxt) end;

(* Version for identifiers with axioms *)

fun err_in_locale' ctxt msg ids' = err_in_locale ctxt msg (map fst ids');


(** primitives **)

(* map elements *)

fun map_elem {name, var, typ, term, fact, attrib} =
  fn Fixes fixes => Fixes (fixes |> map (fn (x, T, mx) =>
       let val (x', mx') = var (x, mx) in (x', Option.map typ T, mx') end))
   | Assumes asms => Assumes (asms |> map (fn ((a, atts), propps) =>
      ((name a, map attrib atts), propps |> map (fn (t, (ps, qs)) =>
        (term t, (map term ps, map term qs))))))
   | Defines defs => Defines (defs |> map (fn ((a, atts), (t, ps)) =>
      ((name a, map attrib atts), (term t, map term ps))))
   | Notes facts => Notes (facts |> map (fn ((a, atts), bs) =>
      ((name a, map attrib atts), bs |> map (fn (ths, btts) => (fact ths, map attrib btts)))));

fun map_values typ term thm = map_elem
  {name = I, var = I, typ = typ, term = term, fact = map thm,
    attrib = Args.map_values I typ term thm};


(* map attributes *)

fun map_attrib_specs f = map (apfst (apsnd (map f)));
fun map_attrib_facts f = map (apfst (apsnd (map f)) o apsnd (map (apsnd (map f))));

fun map_attrib_elem f = map_elem {name = I, var = I, typ = I, term = I, fact = I, attrib = f};

fun intern_attrib_elem thy = map_attrib_elem (Attrib.intern_src (Theory.sign_of thy));

fun intern_attrib_elem_expr thy (Elem elem) = Elem (intern_attrib_elem thy elem)
  | intern_attrib_elem_expr _ (Expr expr) = Expr expr;


(* renaming *)

fun rename ren x = getOpt (assoc_string (ren, x), x);

fun rename_var ren (x, mx) =
  let val x' = rename ren x in
    if x = x' then (x, mx)
    else (x', if mx = NONE then mx else SOME Syntax.NoSyn)    (*drop syntax*)
  end;

fun rename_term ren (Free (x, T)) = Free (rename ren x, T)
  | rename_term ren (t $ u) = rename_term ren t $ rename_term ren u
  | rename_term ren (Abs (x, T, t)) = Abs (x, T, rename_term ren t)
  | rename_term _ a = a;

fun rename_thm ren th =
  let
    val {sign, hyps, prop, maxidx, ...} = Thm.rep_thm th;
    val cert = Thm.cterm_of sign;
    val (xs, Ts) = Library.split_list (Library.foldl Term.add_frees ([], prop :: hyps));
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

fun rename_elem ren =
  map_values I (rename_term ren) (rename_thm ren) o
  map_elem {name = I, typ = I, term = I, fact = I, attrib = I, var = rename_var ren};

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
  | inst_type env T = Term.map_type_tfree (fn v => getOpt (assoc (env, v), TFree v)) T;

fun inst_term [] t = t
  | inst_term env t = Term.map_term_types (inst_type env) t;

fun inst_thm _ [] th = th
  | inst_thm ctxt env th =
      let
        val sign = ProofContext.sign_of ctxt;
        val cert = Thm.cterm_of sign;
        val certT = Thm.ctyp_of sign;
        val {hyps, prop, maxidx, ...} = Thm.rep_thm th;
        val tfrees = foldr Term.add_term_tfree_names [] (prop :: hyps);
        val env' = List.filter (fn ((a, _), _) => a mem_string tfrees) env;
      in
        if null env' then th
        else
          th
          |> Drule.implies_intr_list (map cert hyps)
          |> Drule.tvars_intr_list (map (#1 o #1) env')
          |> (fn (th', al) => th' |>
            Thm.instantiate ((map (fn ((a, _), T) =>
              (certT (TVar (valOf (assoc (al, a)))), certT T)) env'), []))
          |> (fn th'' => Drule.implies_elim_list th''
              (map (Thm.assume o cert o inst_term env') hyps))
      end;

fun inst_elem ctxt env =
  map_values (inst_type env) (inst_term env) (inst_thm ctxt env);


(* term and type instantiation, variant using symbol tables *)

(* instantiate TFrees *)

fun tinst_tab_elem sg tinst =
  map_values (tinst_tab_type tinst) (tinst_tab_term tinst) (tinst_tab_thm sg tinst);

(* instantiate TFrees and Frees *)

fun inst_tab_elem sg (inst as (_, tinst)) =
  map_values (tinst_tab_type tinst) (inst_tab_term inst) (inst_tab_thm sg inst);

fun inst_tab_elems sign inst ((n, ps), elems) =
      ((n, map (inst_tab_term inst) ps), map (inst_tab_elem sign inst) elems);


(** structured contexts: rename + merge + implicit type instantiation **)

(* parameter types *)

(* CB: frozen_tvars has the following type:
  ProofContext.context -> Term.typ list -> (Term.indexname * (sort * Term.typ)) list *)

fun frozen_tvars ctxt Ts =
  let
    val tvars = rev (Library.foldl Term.add_tvarsT ([], Ts));
    val tfrees = map TFree
      (Term.invent_names (ProofContext.used_types ctxt) "'a" (length tvars) ~~ map #2 tvars);
  in map (fn ((x, S), y) => (x, (S, y))) (tvars ~~ tfrees) end;

fun unify_frozen ctxt maxidx Ts Us =
  let
    fun paramify (i, NONE) = (i, NONE)
      | paramify (i, SOME T) = apsnd SOME (TypeInfer.paramify_dummies (i, T));

    val (maxidx', Ts') = foldl_map paramify (maxidx, Ts);
    val (maxidx'', Us') = foldl_map paramify (maxidx', Us);
    val tsig = Sign.tsig_of (ProofContext.sign_of ctxt);

    fun unify (env, (SOME T, SOME U)) = (Type.unify tsig env (U, T)
          handle Type.TUNIFY =>
            raise TYPE ("unify_frozen: failed to unify types", [U, T], []))
      | unify (env, _) = env;
    val (unifier, _) = Library.foldl unify ((Vartab.empty, maxidx''), Ts' ~~ Us');
    val Vs = map (Option.map (Envir.norm_type unifier)) Us';
    val unifier' = Vartab.extend (unifier, frozen_tvars ctxt (List.mapPartial I Vs));
  in map (Option.map (Envir.norm_type unifier')) Vs end;

fun params_of elemss = gen_distinct eq_fst (List.concat (map (snd o fst) elemss));
fun params_of' elemss = gen_distinct eq_fst (List.concat (map (snd o fst o fst) elemss));

(* CB: param_types has the following type:
  ('a * 'b option) list -> ('a * 'b) list *)
fun param_types ps = List.mapPartial (fn (_, NONE) => NONE | (x, SOME T) => SOME (x, T)) ps;


(* flatten expressions *)

local

(* CB: OUTDATED unique_parms has the following type:
     'a ->
     (('b * (('c * 'd) list * Symtab.key list)) * 'e) list ->
     (('b * ('c * 'd) list) * 'e) list  *)

fun unique_parms ctxt elemss =
  let
    val param_decls =
      List.concat (map (fn (((name, (ps, qs)), _), _) => map (rpair (name, ps)) qs) elemss)
      |> Symtab.make_multi |> Symtab.dest;
  in
    (case find_first (fn (_, ids) => length ids > 1) param_decls of
      SOME (q, ids) => err_in_locale ctxt ("Multiple declaration of parameter " ^ quote q)
          (map (apsnd (map fst)) ids)
    | NONE => map (apfst (apfst (apsnd #1))) elemss)
  end;

(* CB: unify_parms has the following type:
     ProofContext.context ->
     (string * Term.typ) list ->
     (string * Term.typ option) list list ->
     ((string * Term.sort) * Term.typ) list list *)

fun unify_parms ctxt fixed_parms raw_parmss =
  let
    val sign = ProofContext.sign_of ctxt;
    val tsig = Sign.tsig_of sign;
    val maxidx = length raw_parmss;
    val idx_parmss = (0 upto maxidx - 1) ~~ raw_parmss;

    fun varify i = Term.map_type_tfree (fn (a, S) => TVar ((a, i), S));
    fun varify_parms (i, ps) = map (apsnd (varify i)) (param_types ps);
    val parms = fixed_parms @ List.concat (map varify_parms idx_parmss);

    fun unify T ((env, maxidx), U) =
      Type.unify tsig (env, maxidx) (U, T)
      handle Type.TUNIFY =>
        let val prt = Sign.string_of_typ sign
        in raise TYPE ("unify_parms: failed to unify types " ^
          prt U ^ " and " ^ prt T, [U, T], [])
        end
    fun unify_list (envir, T :: Us) = Library.foldl (unify T) (envir, Us)
      | unify_list (envir, []) = envir;
    val (unifier, _) = Library.foldl unify_list
      ((Vartab.empty, maxidx), map #2 (Symtab.dest (Symtab.make_multi parms)));

    val parms' = map (apsnd (Envir.norm_type unifier)) (gen_distinct eq_fst parms);
    val unifier' = Vartab.extend (unifier, frozen_tvars ctxt (map #2 parms'));

    fun inst_parms (i, ps) =
      foldr Term.add_typ_tfrees [] (List.mapPartial snd ps)
      |> List.mapPartial (fn (a, S) =>
          let val T = Envir.norm_type unifier' (TVar ((a, i), S))
          in if T = TFree (a, S) then NONE else SOME ((a, S), T) end)
  in map inst_parms idx_parmss end;

in

(* like unify_elemss, but does not touch axioms *)

fun unify_elemss' _ _ [] = []
  | unify_elemss' _ [] [elems] = [elems]
  | unify_elemss' ctxt fixed_parms elemss =
      let
        val envs = unify_parms ctxt fixed_parms (map (#2 o #1 o #1) elemss);
        fun inst ((((name, ps), axs), elems), env) =
          (((name, map (apsnd (Option.map (inst_type env))) ps),  axs),
           map (inst_elem ctxt env) elems);
      in map inst (elemss ~~ envs) end;

fun unify_elemss _ _ [] = []
  | unify_elemss _ [] [elems] = [elems]
  | unify_elemss ctxt fixed_parms elemss =
      let
        val envs = unify_parms ctxt fixed_parms (map (#2 o #1 o #1) elemss);
        fun inst ((((name, ps), axs), elems), env) =
          (((name, map (apsnd (Option.map (inst_type env))) ps), 
            map (inst_thm ctxt env) axs), map (inst_elem ctxt env) elems);
      in map inst (elemss ~~ envs) end;

(* flatten_expr:
   Extend list of identifiers by those new in locale expression expr.
   Compute corresponding list of lists of locale elements (one entry per
   identifier).

   Identifiers represent locale fragments and are in an extended form:
     ((name, ps), (ax_ps, axs))
   (name, ps) is the locale name with all its parameters.
   (ax_ps, axs) is the locale axioms with its parameters;
     axs are always taken from the top level of the locale hierarchy,
     hence axioms may contain additional parameters from later fragments:
     ps subset of ax_ps.  axs is either singleton or empty.

   Elements are enriched by identifier-like information:
     (((name, ax_ps), axs), elems)
   The parameters in ax_ps are the axiom parameters, but enriched by type
   info: now each entry is a pair of string and typ option.  Axioms are
   type-instantiated.

*)

fun flatten_expr ctxt (prev_idents, expr) =
  let
    val thy = ProofContext.theory_of ctxt;
    (* thy used for retrieval of locale info,
       ctxt for error messages, parameter unification and instantiation
       of axioms *)
    (* TODO: consider err_in_locale with thy argument *)

    fun renaming (SOME x :: xs) (y :: ys) = (y, x) :: renaming xs ys
      | renaming (NONE :: xs) (y :: ys) = renaming xs ys
      | renaming [] _ = []
      | renaming xs [] = raise ERROR_MESSAGE ("Too many arguments in renaming: " ^
          commas (map (fn NONE => "_" | SOME x => quote x) xs));

    fun rename_parms top ren ((name, ps), (parms, axs)) =
      let val ps' = map (rename ren) ps in
        (case duplicates ps' of [] => ((name, ps'),
          if top then (map (rename ren) parms, map (rename_thm ren) axs)
          else (parms, axs))
        | dups => err_in_locale ctxt ("Duplicate parameters: " ^ commas_quote dups) [(name, ps')])
      end;

    fun identify top (Locale name) =
    (* CB: ids_ax is a list of tuples of the form ((name, ps), axs),
       where name is a locale name, ps a list of parameter names and axs
       a list of axioms relating to the identifier, axs is empty unless
       identify at top level (top = true);
       parms is accumulated list of parameters *)
          let
            val {predicate = (_, axioms), import, params, ...} =
              the_locale thy name;
            val ps = map #1 (#1 params);
            val (ids', parms') = identify false import;
                (* acyclic import dependencies *)
            val ids'' = ids' @ [((name, ps), ([], []))];
            val ids_ax = if top then snd
                 (foldl_map (fn (axs, ((name, parms), _)) => let
                   val {elems, ...} = the_locale thy name;
                   val ts = List.concat (List.mapPartial (fn (Assumes asms, _) =>
                     SOME (List.concat (map (map #1 o #2) asms)) | _ => NONE) elems);
                   val (axs1, axs2) = splitAt (length ts, axs);
                 in (axs2, ((name, parms), (ps, axs1))) end) (axioms, ids''))
               else ids'';
          in (ids_ax, merge_lists parms' ps) end
      | identify top (Rename (e, xs)) =
          let
            val (ids', parms') = identify top e;
            val ren = renaming xs parms'
              handle ERROR_MESSAGE msg => err_in_locale' ctxt msg ids';
            val ids'' = gen_distinct eq_fst (map (rename_parms top ren) ids');
            val parms'' = distinct (List.concat (map (#2 o #1) ids''));
          in (ids'', parms'') end
      | identify top (Merge es) =
          Library.foldl (fn ((ids, parms), e) => let
                     val (ids', parms') = identify top e
                   in (gen_merge_lists eq_fst ids ids',
                       merge_lists parms parms') end)
            (([], []), es);

    (* CB: enrich identifiers by parameter types and 
       the corresponding elements (with renamed parameters) *)

    fun eval ((name, xs), axs) =
      let
        val {params = (ps, qs), elems, ...} = the_locale thy name;
        val ren = filter_out (op =) (map #1 ps ~~ xs);
        val (params', elems') =
          if null ren then ((ps, qs), map #1 elems)
          else ((map (apfst (rename ren)) ps, map (rename ren) qs),
            map (rename_elem ren o #1) elems);
        val elems'' = map (rename_facts (space_implode "_" xs)) elems';
      in (((name, params'), axs), elems'') end;

    (* compute identifiers, merge with previous ones *)
    val idents = gen_rems eq_fst (#1 (identify true expr), prev_idents);
    (* add types to params, check for unique params and unify them *)
    val raw_elemss = unique_parms ctxt (map eval idents);
    val elemss = unify_elemss' ctxt [] raw_elemss;
    (* replace params in ids by params from axioms,
       adjust types in axioms *)
    val all_params' = params_of' elemss;
    val all_params = param_types all_params';
    val elemss' = map (fn (((name, _), (ps, axs)), elems) =>
         (((name, map (fn p => (p, assoc (all_params, p))) ps), axs), elems))
         elemss;
    fun inst_ax th = let
         val {hyps, prop, ...} = Thm.rep_thm th;
         val ps = map (apsnd SOME) (Library.foldl Term.add_frees ([], prop :: hyps));
         val [env] = unify_parms ctxt all_params [ps];
         val th' = inst_thm ctxt env th;
       in th' end;
    val final_elemss = map (fn ((id, axs), elems) =>
         ((id, map inst_ax axs), elems)) elemss';
  in (prev_idents @ idents, final_elemss) end;

end;


(* activate elements *)

local

fun export_axioms axs _ hyps th =
  th |> Drule.satisfy_hyps axs
     (* CB: replace meta-hyps, using axs, by a single meta-hyp. *)
  |> Drule.implies_intr_list (Library.drop (length axs, hyps))
     (* CB: turn remaining hyps into assumptions. *)
  |> Seq.single

fun activate_elem _ ((ctxt, axs), Fixes fixes) =
      ((ctxt |> ProofContext.add_fixes fixes, axs), [])
  | activate_elem _ ((ctxt, axs), Assumes asms) =
      let
        val asms' = map_attrib_specs (Attrib.context_attribute_i ctxt) asms;
        val ts = List.concat (map (map #1 o #2) asms');
        val (ps, qs) = splitAt (length ts, axs);
        val (ctxt', _) =
          ctxt |> ProofContext.fix_frees ts
          |> ProofContext.assume_i (export_axioms ps) asms';
      in ((ctxt', qs), []) end
  | activate_elem _ ((ctxt, axs), Defines defs) =
      let
        val defs' = map_attrib_specs (Attrib.context_attribute_i ctxt) defs;
        val (ctxt', _) =
        ctxt |> ProofContext.assume_i ProofContext.export_def
          (defs' |> map (fn ((name, atts), (t, ps)) =>
            let val (c, t') = ProofContext.cert_def ctxt t
            in ((if name = "" then Thm.def_name c else name, atts), [(t', (ps, []))]) end))
      in ((ctxt', axs), []) end
  | activate_elem is_ext ((ctxt, axs), Notes facts) =
      let
        val facts' = map_attrib_facts (Attrib.context_attribute_i ctxt) facts;
        val (ctxt', res) = ctxt |> ProofContext.note_thmss_i facts';
      in ((ctxt', axs), if is_ext then res else []) end;

fun activate_elems (((name, ps), axs), elems) ctxt =
  let val ((ctxt', _), res) =
    foldl_map (activate_elem (name = "")) ((ProofContext.qualified true ctxt, axs), elems)
      handle ProofContext.CONTEXT (msg, ctxt) => err_in_locale ctxt msg [(name, map fst ps)]
    val ctxt'' = if name = "" then ctxt'
          else let
              val ps' = map (fn (n, SOME T) => Free (n, T)) ps;
              val ctxt'' = put_local_registration (name, ps') ("", []) ctxt'
            in foldl (fn (ax, ctxt) =>
              add_local_witness (name, ps') (Thm.assume (Thm.cprop_of ax)) ctxt) ctxt'' axs
            end
  in (ProofContext.restore_qualified ctxt ctxt'', res) end;

fun activate_elemss prep_facts = foldl_map (fn (ctxt, (((name, ps), axs), raw_elems)) =>
  let
    val elems = map (prep_facts ctxt) raw_elems;
    val (ctxt', res) = apsnd List.concat (activate_elems (((name, ps), axs), elems) ctxt);
    val elems' = map (map_attrib_elem Args.closure) elems;
  in (ctxt', (((name, ps), elems'), res)) end);

in

(* CB: activate_facts prep_facts (ctxt, elemss),
   where elemss is a list of pairs consisting of identifiers and
   context elements, extends ctxt by the context elements yielding
   ctxt' and returns (ctxt', (elemss', facts)).
   Identifiers in the argument are of the form ((name, ps), axs) and
   assumptions use the axioms in the identifiers to set up exporters
   in ctxt'.  elemss' does not contain identifiers and is obtained
   from elemss and the intermediate context with prep_facts.
   If read_facts or cert_facts is used for prep_facts, these also remove
   the internal/external markers from elemss. *)

fun activate_facts prep_facts arg =
  apsnd (apsnd List.concat o Library.split_list) (activate_elemss prep_facts arg);

fun activate_note prep_facts (ctxt, args) =
  let
    val (ctxt', ([(_, [Notes args'])], facts)) =
      activate_facts prep_facts (ctxt, [((("", []), []), [Ext (Notes args)])]);
  in (ctxt', (args', facts)) end;

end;


(* register elements *)

fun register_elems (((_, ps), (((name, ax_ps), axs), _)), ctxt) =
  if name = "" then ctxt
      else let val ps' = map (fn (n, SOME T) => Free (n, T)) ax_ps
          val ctxt' = put_local_registration (name, ps') ("", []) ctxt
        in foldl (fn (ax, ctxt) =>
          add_local_witness (name, ps') ax ctxt) ctxt' axs
        end;

fun register_elemss id_elemss ctxt = 
  foldl register_elems ctxt id_elemss;


(** prepare context elements **)

(* expressions *)

fun intern_expr sg (Locale xname) = Locale (intern sg xname)
  | intern_expr sg (Merge exprs) = Merge (map (intern_expr sg) exprs)
  | intern_expr sg (Rename (expr, xs)) = Rename (intern_expr sg expr, xs);


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

(* flatten (ids, expr) normalises expr (which is either a locale
   expression or a single context element) wrt.
   to the list ids of already accumulated identifiers.
   It returns (ids', elemss) where ids' is an extension of ids
   with identifiers generated for expr, and elemss is the list of
   context elements generated from expr.  For details, see flatten_expr.
   Additionally, for a locale expression, the elems are grouped into a single
   Int; individual context elements are marked Ext.  In this case, the
   identifier-like information of the element is as follows:
   - for Fixes: (("", ps), []) where the ps have type info NONE
   - for other elements: (("", []), []).
   The implementation of activate_facts relies on identifier names being
   empty strings for external elements.
*)

fun flatten _ (ids, Elem (Fixes fixes)) =
      (ids @ [(("", map #1 fixes), ([], []))], [((("", map (rpair NONE o #1) fixes), []), Ext (Fixes fixes))])
  | flatten _ (ids, Elem elem) = (ids @ [(("", []), ([], []))], [((("", []), []), Ext elem)])
  | flatten (ctxt, prep_expr) (ids, Expr expr) =
      apsnd (map (apsnd Int)) (flatten_expr ctxt (ids, prep_expr expr));

local

local

fun declare_int_elem (ctxt, Fixes fixes) =
      (ctxt |> ProofContext.add_fixes (map (fn (x, T, mx) =>
        (x, Option.map (Term.map_type_tfree (TypeInfer.param 0)) T, mx)) fixes), [])
  | declare_int_elem (ctxt, _) = (ctxt, []);

fun declare_ext_elem prep_fixes (ctxt, Fixes fixes) =
      (ctxt |> ProofContext.add_fixes (prep_fixes ctxt fixes), [])
  | declare_ext_elem _ (ctxt, Assumes asms) = (ctxt, map #2 asms)
  | declare_ext_elem _ (ctxt, Defines defs) = (ctxt, map (fn (_, (t, ps)) => [(t, (ps, []))]) defs)
  | declare_ext_elem _ (ctxt, Notes facts) = (ctxt, []);

fun declare_elems prep_fixes (ctxt, (((name, ps), _), elems)) =
  let val (ctxt', propps) =
    (case elems of
      Int es => foldl_map declare_int_elem (ctxt, es)
    | Ext e => foldl_map (declare_ext_elem prep_fixes) (ctxt, [e]))
    handle ProofContext.CONTEXT (msg, ctxt) => err_in_locale ctxt msg [(name, map fst ps)]
  in (ctxt', propps) end;

in

(* CB: only called by prep_elemss. *)

fun declare_elemss prep_fixes fixed_params raw_elemss ctxt =
  let
    (* CB: fix of type bug of goal in target with context elements.
       Parameters new in context elements must receive types that are
       distinct from types of parameters in target (fixed_params).  *)
    val ctxt_with_fixed =
      fold ProofContext.declare_term (map Free fixed_params) ctxt;
    val int_elemss =
      raw_elemss
      |> List.mapPartial (fn (id, Int es) => SOME (id, es) | _ => NONE)
      |> unify_elemss ctxt_with_fixed fixed_params;
    val (_, raw_elemss') =
      foldl_map (fn ((_, es) :: elemss, (id, Int _)) => (elemss, (id, Int es)) | x => x)
        (int_elemss, raw_elemss);
  in foldl_map (declare_elems prep_fixes) (ctxt, raw_elemss') end;

end;

local

(* CB: normalise Assumes and Defines wrt. previous definitions *)

val norm_term = Envir.beta_norm oo Term.subst_atomic;

(* CB: following code (abstract_term, abstract_thm, bind_def)
   used in eval_text for Defines elements. *)

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

(* CB: for finish_elems (Int and Ext) *)

fun eval_text _ _ _ (text, Fixes _) = text
  | eval_text _ _ is_ext ((((exts, exts'), (ints, ints')), (xs, env, defs)), Assumes asms) =
      let
        val ts = List.concat (map (map #1 o #2) asms);
        val ts' = map (norm_term env) ts;
        val spec' =
          if is_ext then ((exts @ ts, exts' @ ts'), (ints, ints'))
          else ((exts, exts'), (ints @ ts, ints' @ ts'));
      in (spec', (Library.foldl Term.add_frees (xs, ts'), env, defs)) end
  | eval_text ctxt (id, _) _ ((spec, binds), Defines defs) =
      (spec, Library.foldl (bind_def ctxt id) (binds, map (#1 o #2) defs))
  | eval_text _ _ _ (text, Notes _) = text;

(* CB: for finish_elems (Ext) *)

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

(* CB: finish_parms introduces type info from parms to identifiers *)
(* CB: only needed for types that have been NONE so far???
   If so, which are these??? *)

fun finish_parms parms (((name, ps), axs), elems) =
  (((name, map (fn (x, _) => (x, assoc (parms, x))) ps), axs), elems);

fun finish_elems ctxt parms _ (text, ((id, Int e), _)) =
      let
        val [(id', es)] = unify_elemss ctxt parms [(id, e)];
        val text' = Library.foldl (eval_text ctxt id' false) (text, es);
      in (text', (id', map Int es)) end
  | finish_elems ctxt parms do_close (text, ((id, Ext e), [propp])) =
      let
        val e' = finish_ext_elem parms (closeup ctxt do_close) (e, propp);
        val text' = eval_text ctxt id true (text, e');
      in (text', (id, [Ext e'])) end;

in

(* CB: only called by prep_elemss *)

fun finish_elemss ctxt parms do_close =
  foldl_map (apsnd (finish_parms parms) o finish_elems ctxt parms do_close);

end;

(* CB: type inference and consistency checks for locales *)

fun prep_elemss prep_fixes prepp do_close context fixed_params raw_elemss raw_concl =
  let
    (* CB: contexts computed in the course of this function are discarded.
       They are used for type inference and consistency checks only. *)
    (* CB: fixed_params are the parameters (with types) of the target locale,
       empty list if there is no target. *)
    (* CB: raw_elemss are list of pairs consisting of identifiers and
       context elements, the latter marked as internal or external. *)
    val (raw_ctxt, raw_proppss) = declare_elemss prep_fixes fixed_params raw_elemss context;
    (* CB: raw_ctxt is context with additional fixed variables derived from
       the fixes elements in raw_elemss,
       raw_proppss contains assumptions and definitions from the
       external elements in raw_elemss. *)
    val raw_propps = map List.concat raw_proppss;
    val raw_propp = List.concat raw_propps;

    (* CB: add type information from fixed_params to context (declare_term) *)
    (* CB: process patterns (conclusion and external elements only) *)
    val (ctxt, all_propp) =
      prepp (fold ProofContext.declare_term (map Free fixed_params) raw_ctxt, raw_concl @ raw_propp);
    (* CB: add type information from conclusion and external elements
       to context *)
    val ctxt = fold ProofContext.declare_term (List.concat (map (map fst) all_propp)) ctxt;

    (* CB: resolve schematic variables (patterns) in conclusion and external
       elements. *)
    val all_propp' = map2 (op ~~)
      (#1 (#2 (ProofContext.bind_propp_schematic_i (ctxt, all_propp))), map (map snd) all_propp);
    val (concl, propp) = splitAt(length raw_concl, all_propp');
    val propps = unflat raw_propps propp;
    val proppss = map (uncurry unflat) (raw_proppss ~~ propps);

    (* CB: obtain all parameters from identifier part of raw_elemss *)
    val xs = map #1 (params_of' raw_elemss);
    val typing = unify_frozen ctxt 0
      (map (ProofContext.default_type raw_ctxt) xs)
      (map (ProofContext.default_type ctxt) xs);
    val parms = param_types (xs ~~ typing);
    (* CB: parms are the parameters from raw_elemss, with correct typing. *)

    (* CB: extract information from assumes and defines elements
       (fixes and notes in raw_elemss don't have an effect on text and elemss),
       compute final form of context elements. *)
    val (text, elemss) = finish_elemss ctxt parms do_close
      (((([], []), ([], [])), ([], [], [])), raw_elemss ~~ proppss);
    (* CB: text has the following structure:
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
       elemss is an updated version of raw_elemss:
         - type info added to Fixes
         - axiom and definition statement replaced by corresponding one
           from proppss in Assumes and Defines
         - Facts unchanged
       *)
  in ((parms, elemss, concl), text) end;

in

fun read_elemss x = prep_elemss read_fixes ProofContext.read_propp_schematic x;
fun cert_elemss x = prep_elemss cert_fixes ProofContext.cert_propp_schematic x;

end;


(* facts and attributes *)

local

fun prep_name ctxt name =
  (* CB: reject qualified theorem names in locale declarations *)
  if NameSpace.is_qualified name then
    raise ProofContext.CONTEXT ("Illegal qualified name: " ^ quote name, ctxt)
  else name;

fun prep_facts _ _ ctxt (Int elem) =
      map_values I I (Thm.transfer (ProofContext.theory_of ctxt)) elem
  | prep_facts get intern ctxt (Ext elem) = elem |> map_elem
     {var = I, typ = I, term = I,
      name = prep_name ctxt,
      fact = get ctxt,
      attrib = Args.assignable o intern (ProofContext.sign_of ctxt)};

in

fun read_facts x = prep_facts ProofContext.get_thms Attrib.intern_src x;
fun cert_facts x = prep_facts (K I) (K I) x;

end;


(* full context statements: import + elements + conclusion *)

local

fun prep_context_statement prep_expr prep_elemss prep_facts
    do_close fixed_params import elements raw_concl context =
  let
    val sign = ProofContext.sign_of context;

    val (import_ids, raw_import_elemss) = flatten (context, prep_expr sign) ([], Expr import);
    (* CB: normalise "includes" among elements *)
    val (ids, raw_elemsss) = foldl_map (flatten (context, prep_expr sign))
      (import_ids, elements);

    val raw_elemss = List.concat raw_elemsss;
    (* CB: raw_import_elemss @ raw_elemss is the normalised list of
       context elements obtained from import and elements. *)
    val ((parms, all_elemss, concl), (spec, (_, _, defs))) = prep_elemss do_close
      context fixed_params (raw_import_elemss @ raw_elemss) raw_concl;
    (* replace extended ids (for axioms) by ids *)
    val all_elemss' = map (fn (((_, ps), _), (((n, ps'), ax), elems)) =>
        (((n, List.filter (fn (p, _) => p mem ps) ps'), ax), elems))
      (ids ~~ all_elemss);

    (* CB: all_elemss and parms contain the correct parameter types *)
    val (ps,qs) = splitAt(length raw_import_elemss, all_elemss')
    val (import_ctxt, (import_elemss, _)) =
      activate_facts prep_facts (context, ps);

    val (ctxt, (elemss, _)) =
      activate_facts prep_facts (import_ctxt, qs);
    val stmt = gen_distinct Term.aconv
       (List.concat (map (fn ((_, axs), _) =>
         List.concat (map (#hyps o Thm.rep_thm) axs)) qs));
    val cstmt = map (cterm_of sign) stmt;
  in
    ((((import_ctxt, import_elemss), (ctxt, elemss)), (parms, spec, defs)), (cstmt, concl))
  end;

val gen_context = prep_context_statement intern_expr read_elemss read_facts;
val gen_context_i = prep_context_statement (K I) cert_elemss cert_facts;

fun gen_statement prep_locale prep_ctxt raw_locale elems concl ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val locale = Option.map (prep_locale (Theory.sign_of thy)) raw_locale;
    val (target_stmt, fixed_params, import) =
      (case locale of NONE => ([], [], empty)
      | SOME name =>
          let val {predicate = (stmt, _), params = (ps, _), ...} =
            the_locale thy name
          in (stmt, param_types ps, Locale name) end);
    val ((((locale_ctxt, locale_elemss), (elems_ctxt, _)), _), (elems_stmt, concl')) =
      prep_ctxt false fixed_params import elems concl ctxt;
  in (locale, (target_stmt, elems_stmt), locale_ctxt, elems_ctxt, concl') end;

in

(* CB: processing of locales for add_locale(_i) and print_locale *)
  (* CB: arguments are: x->import, y->body (elements), z->context *)
fun read_context x y z = #1 (gen_context true [] x (map Elem y) [] z);
fun cert_context x y z = #1 (gen_context_i true [] x (map Elem y) [] z);

(* CB: processing of locales for note_thmss(_i),
   Proof.multi_theorem(_i) and antiquotations with option "locale" *)
val read_context_statement = gen_statement intern gen_context;
val cert_context_statement = gen_statement (K I) gen_context_i;

end;


(** CB: experimental instantiation mechanism **)

fun instantiate loc_name (prfx, attribs) raw_inst ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val sign = Theory.sign_of thy;
    val tsig = Sign.tsig_of sign;
    val cert = cterm_of sign;

    (** process the locale **)

    val {predicate = (_, axioms), params = (ps, _), ...} =
      the_locale thy (intern sign loc_name);
    val fixed_params = param_types ps;
    val init = ProofContext.init thy;
    val (_, raw_elemss) =
          flatten (init, intern_expr sign) ([], Expr (Locale loc_name));
    val ((parms, all_elemss, concl),
         (spec as (_, (ints, _)), (xs, env, defs))) =
      read_elemss false (* do_close *) init
        fixed_params (* could also put [] here??? *) raw_elemss
        [] (* concl *);

    (** analyse the instantiation theorem inst **)

    val inst = case raw_inst of
        NONE => if null ints
	  then NONE
	  else error "Locale has assumptions but no chained fact was found"
      | SOME [] => if null ints
	  then NONE
	  else error "Locale has assumptions but no chained fact was found"
      | SOME [thm] => if null ints
	  then (warning "Locale has no assumptions: fact ignored"; NONE)
	  else SOME thm
      | SOME _ => error "Multiple facts are not allowed";

    val args = case inst of
            NONE => []
          | SOME thm => thm |> prop_of |> ObjectLogic.drop_judgment sign
              |> Term.strip_comb
              |>> (fn t as (Const (s, _)) => if (intern sign loc_name = s)
                        then t
                        else error ("Constant " ^ quote loc_name ^
                          " expected but constant " ^ quote s ^ " was found")
                    | t => error ("Constant " ^ quote loc_name ^ " expected \
                          \but term " ^ quote (Sign.string_of_term sign t) ^
                          " was found"))
              |> snd;
    val cargs = map cert args;

    (* process parameters: match their types with those of arguments *)

    val def_names = map (fn (Free (s, _), _) => s) env;
    val (defined, assumed) = List.partition
          (fn (s, _) => s mem def_names) fixed_params;
    val cassumed = map (cert o Free) assumed;
    val cdefined = map (cert o Free) defined;

    val param_types = map snd assumed;
    val v_param_types = map Type.varifyT param_types;
    val arg_types = map Term.fastype_of args;
    val Tenv = Library.foldl (Type.typ_match tsig)
          (Vartab.empty, v_param_types ~~ arg_types)
          handle UnequalLengths => error "Number of parameters does not \
            \match number of arguments of chained fact";
    (* get their sorts *)
    val tfrees = foldr Term.add_typ_tfrees [] param_types
    val Tenv' = map
          (fn ((a, i), (S, T)) => ((a, S), T))
          (Vartab.dest Tenv);

    (* process (internal) elements *)

    fun inst_type [] T = T
      | inst_type env T =
          Term.map_type_tfree (fn v => getOpt (assoc (env, v), TFree v)) T;

    fun inst_term [] t = t
      | inst_term env t = Term.map_term_types (inst_type env) t;

    (* parameters with argument types *)

    val cparams' = map (cterm_of sign o inst_term Tenv' o term_of) cassumed;
    val cdefined' = map (cert o inst_term Tenv' o term_of) cdefined;
    val cdefining = map (cert o inst_term Tenv' o snd) env;

    fun inst_thm _ [] th = th
      | inst_thm ctxt Tenv th =
	  let
	    val sign = ProofContext.sign_of ctxt;
	    val cert = Thm.cterm_of sign;
	    val certT = Thm.ctyp_of sign;
	    val {hyps, prop, maxidx, ...} = Thm.rep_thm th;
	    val tfrees = foldr Term.add_term_tfree_names [] (prop :: hyps);
	    val Tenv' = List.filter (fn ((a, _), _) => a mem_string tfrees) Tenv;
	  in
	    if null Tenv' then th
	    else
	      th
	      |> Drule.implies_intr_list (map cert hyps)
	      |> Drule.tvars_intr_list (map (#1 o #1) Tenv')
	      |> (fn (th', al) => th' |>
		Thm.instantiate ((map (fn ((a, _), T) =>
                  (certT (TVar (valOf (assoc (al, a)))), certT T)) Tenv'), []))
	      |> (fn th'' => Drule.implies_elim_list th''
		  (map (Thm.assume o cert o inst_term Tenv') hyps))
	  end;

    val inst_type' = inst_type Tenv';

    val inst_term' = Term.subst_atomic
        (map (pairself term_of) ((cparams' @ cdefined') ~~ (cargs @ cdefining)))
      o inst_term Tenv';

    fun inst_thm' thm =
      let
        (* not all axs are normally applicable *)
        val hyps = #hyps (rep_thm thm);
        val ass = map (fn ax => (prop_of ax, ax)) axioms;
        val axs' = Library.foldl (fn (axs, hyp) => 
              (case gen_assoc (op aconv) (ass, hyp) of NONE => axs
                 | SOME ax => axs @ [ax])) ([], hyps);
        val thm' = Drule.satisfy_hyps axs' thm;
        (* instantiate types *)
        val thm'' = inst_thm ctxt Tenv' thm';
        (* substitute arguments and discharge hypotheses *)
        val thm''' = case inst of
                NONE => thm''
              | SOME inst_thm => let
		    val hyps = #hyps (rep_thm thm'');
		    val th = thm'' |> implies_intr_hyps
		      |> forall_intr_list (cparams' @ cdefined')
		      |> forall_elim_list (cargs @ cdefining)
		    (* th has premises of the form either inst_thm or x==x *)
		    fun mk hyp = if Logic.is_equals hyp
			  then hyp |> Logic.dest_equals |> snd |> cert
				 |> reflexive
			  else inst_thm
                  in implies_elim_list th (map mk hyps)
                  end;
      in thm''' end
      handle THM (msg, n, thms) => error ("Exception THM " ^
        string_of_int n ^ " raised\n" ^
	  "Note: instantiate does not support old-style locales \
          \declared with (open)\n" ^ msg ^ "\n" ^
	cat_lines (map string_of_thm thms));

    val prefix_fact =
      if prfx = "" then I
      else (fn "" => ""
             | s => NameSpace.append prfx s);

    fun inst_elem (ctxt, (Ext _)) = ctxt
      | inst_elem (ctxt, (Int (Notes facts))) =
              (* instantiate fact *)
          let
              val facts = facts |> map_attrib_facts
                (Attrib.context_attribute_i ctxt o
                  Args.map_values I inst_type' inst_term' inst_thm');
              val facts' =
                map (apsnd (map (apfst (map inst_thm')))) facts
              (* rename fact *)
              val facts'' = map (apfst (apfst prefix_fact)) facts'
              (* add attributes *)
              val facts''' = map (apfst (apsnd (fn atts => atts @ attribs))) facts''
          in fst (ProofContext.note_thmss_i facts''' ctxt)
          end
      | inst_elem (ctxt, (Int _)) = ctxt;

    fun inst_elems (ctxt, (id, elems)) = Library.foldl inst_elem (ctxt, elems);

    fun inst_elemss ctxt elemss = Library.foldl inst_elems (ctxt, elemss);

    (* main part *)

    val ctxt' = ProofContext.qualified true ctxt;
  in ProofContext.restore_qualified ctxt (inst_elemss ctxt' all_elemss)
  end;


(** define locales **)

(* print locale *)

fun print_locale thy import body =
  let
    val thy_ctxt = ProofContext.init thy;
    val (((_, import_elemss), (ctxt, elemss)), _) = read_context import body thy_ctxt;
    val all_elems = List.concat (map #2 (import_elemss @ elemss));

    val prt_typ = Pretty.quote o ProofContext.pretty_typ ctxt;
    val prt_term = Pretty.quote o ProofContext.pretty_term ctxt;
    val prt_thm = Pretty.quote o ProofContext.pretty_thm ctxt;
    val prt_atts = Args.pretty_attribs ctxt;

    fun prt_syn syn =
      let val s = (case syn of NONE => "(structure)" | SOME mx => Syntax.string_of_mixfix mx)
      in if s = "" then [] else [Pretty.brk 2, Pretty.str s] end;
    fun prt_fix (x, SOME T, syn) = Pretty.block (Pretty.str (x ^ " ::") :: Pretty.brk 1 ::
          prt_typ T :: Pretty.brk 1 :: prt_syn syn)
      | prt_fix (x, NONE, syn) = Pretty.block (Pretty.str x :: Pretty.brk 1 :: prt_syn syn);

    fun prt_name name = Pretty.str (ProofContext.cond_extern ctxt name);
    fun prt_name_atts (name, atts) =
      if name = "" andalso null atts then []
      else [Pretty.block (Pretty.breaks (prt_name name :: prt_atts atts @ [Pretty.str ":"]))];

    fun prt_asm (a, ts) =
      Pretty.block (Pretty.breaks (prt_name_atts a @ map (prt_term o fst) ts));
    fun prt_def (a, (t, _)) =
      Pretty.block (Pretty.breaks (prt_name_atts a @ [prt_term t]));

    fun prt_fact (ths, []) = map prt_thm ths
      | prt_fact (ths, atts) =
          Pretty.enclose "(" ")" (Pretty.breaks (map prt_thm ths)) :: prt_atts atts;
    fun prt_note (a, ths) =
      Pretty.block (Pretty.breaks (List.concat (prt_name_atts a :: map prt_fact ths)));

    fun items _ [] = []
      | items prfx (x :: xs) = Pretty.block [Pretty.str prfx, Pretty.brk 1, x] :: items "  and" xs;
    fun prt_elem (Fixes fixes) = items "fixes" (map prt_fix fixes)
      | prt_elem (Assumes asms) = items "assumes" (map prt_asm asms)
      | prt_elem (Defines defs) = items "defines" (map prt_def defs)
      | prt_elem (Notes facts) = items "notes" (map prt_note facts);
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

(* store exported theorem in theory *)

fun note_thmss_qualified kind name args thy =
  thy
  |> Theory.add_path (Sign.base_name name)
  |> PureThy.note_thmss_i (Drule.kind kind) args
  |>> hide_bound_names (map (#1 o #1) args)
  |>> Theory.parent_path;

(* accesses of interpreted theorems *)

(* fully qualified name in theory is T.p.r.n where
   T: theory name, p: interpretation prefix, r: renaming prefix, n: name *)

fun global_accesses prfx name =
     if prfx = "" then
       case NameSpace.unpack name of
	   [] => [""]
	 | [T, n] => map NameSpace.pack [[T, n], [n]]
	 | [T, r, n] => map NameSpace.pack [[T, r, n], [T, n], [r, n], [n]]
	 | _ => error ("Locale accesses: illegal name " ^ quote name)
     else case NameSpace.unpack name of
           [] => [""]
         | [T, p, n] => map NameSpace.pack [[T, p, n], [p, n]]
         | [T, p, r, n] => map NameSpace.pack
             [[T, p, r, n], [T, p, n], [p, r, n], [p, n]]
         | _ => error ("Locale accesses: illegal name " ^ quote name);

(* fully qualified name in context is p.r.n where
   p: interpretation prefix, r: renaming prefix, n: name *)

fun local_accesses prfx name =
     if prfx = "" then
       case NameSpace.unpack name of
	   [] => [""]
	 | [n] => map NameSpace.pack [[n]]
	 | [r, n] => map NameSpace.pack [[r, n], [n]]
	 | _ => error ("Locale accesses: illegal name " ^ quote name)
     else case NameSpace.unpack name of
           [] => [""]
         | [p, n] => map NameSpace.pack [[p, n]]
         | [p, r, n] => map NameSpace.pack [[p, r, n], [p, n]]
         | _ => error ("Locale accesses: illegal name " ^ quote name);


(* store instantiations of args for all registered interpretations
   of the theory *)

fun note_thmss_registrations kind target args thy =
  let
    val ctxt = ProofContext.init thy;
    val sign = Theory.sign_of thy;

    val (parms, parmTs_o) =
          the_locale thy target |> #params |> fst |> split_list;
    val parmvTs = map (Type.varifyT o valOf) parmTs_o;
    val ids = flatten (ctxt, intern_expr sign) ([], Expr (Locale target))
          |> fst |> map fst;

    val regs = get_global_registrations thy target;

    (* add args to thy for all registrations *)

    fun activate (thy, (vts, ((prfx, atts2), _))) =
      let
        val ts = map Logic.unvarify vts;
        (* type instantiation *)
        val vtinst = Library.foldl (Type.typ_match (Sign.tsig_of sign))
             (Vartab.empty, (parmvTs ~~ map Term.fastype_of ts));
        val tinst = Vartab.dest vtinst |> map (fn ((x, 0), (_, T)) => (x, T))
             |> Symtab.make;            
        (* replace parameter names in ids by instantiations *)
        val vinst = Symtab.make (parms ~~ vts);
        fun vinst_names ps = map (fn p => Symtab.lookup (vinst, p) |> valOf) ps;
        val inst = Symtab.make (parms ~~ ts);
        val ids' = map (apsnd vinst_names) ids;
        val prems = List.concat (map (snd o valOf o get_global_registration thy) ids');
        val args' = map (fn ((n, atts), [(ths, [])]) =>
            ((if prfx = "" orelse n = "" then "" else NameSpace.pack [prfx, n],
              map (Attrib.global_attribute_i thy) (atts @ atts2)),
             [(map (Drule.standard o Drule.satisfy_hyps prems o inst_tab_thm sign (inst, tinst)) ths, [])]))
          args;
      in
        PureThy.note_thmss_accesses_i (global_accesses prfx) (Drule.kind kind) args' thy |> fst
      end;
  in Library.foldl activate (thy, regs) end;


fun smart_note_thmss kind NONE = PureThy.note_thmss_i (Drule.kind kind)
  | smart_note_thmss kind (SOME loc) = note_thmss_qualified kind loc;

end;

local

(* add facts to locale in theory *)

fun put_facts loc args thy =
  let
    val {predicate, import, elems, params} = the_locale thy loc;
    val note = Notes (map (fn ((a, atts), bs) =>
      ((a, atts), map (apfst (map (curry Thm.name_thm a))) bs)) args);
  in
    thy |> put_locale loc {predicate = predicate, import = import,
      elems = elems @ [(note, stamp ())], params = params}
  end;

(* add theorem to locale and theory,
   base for theorems (in loc) and declare (in loc) *)

fun gen_note_thmss prep_locale prep_facts kind raw_loc args thy =
  let
    val thy_ctxt = ProofContext.init thy;
    val loc = prep_locale (Theory.sign_of thy) raw_loc;
    val (_, (stmt, _), loc_ctxt, _, _) = cert_context_statement (SOME loc) [] [] thy_ctxt;
    val export = ProofContext.export_standard stmt loc_ctxt thy_ctxt;

    val (args', facts) = #2 (activate_note prep_facts (loc_ctxt, args));
    val facts' =
      map (rpair [] o #1 o #1) args' ~~
      map (single o Thm.no_attributes o map export o #2) facts;
  in
    thy
    |> put_facts loc args'
    |> note_thmss_registrations kind loc args'
    |> note_thmss_qualified kind loc facts'
  end;

in

val note_thmss = gen_note_thmss intern read_facts;
val note_thmss_i = gen_note_thmss (K I) cert_facts;

fun add_thmss kind loc args (thy, ctxt) =
  let
    val (ctxt', (args', facts)) = activate_note cert_facts
      (ctxt, args |> map (fn ((a, ths), atts) => ((a, atts), [(ths, [])])));
    val thy' =
      thy
      |> put_facts loc args'
      |> note_thmss_registrations kind loc args';
  in ((thy', ctxt'), facts) end;

end;


(* predicate text *)
(* CB: generate locale predicates and delta predicates *)

local

(* introN: name of theorems for introduction rules of locale and
     delta predicates;
   axiomsN: name of theorem set with destruct rules for locale predicates,
     also name suffix of delta predicates. *)

val introN = "intro";
val axiomsN = "axioms";

fun atomize_spec sign ts =
  let
    val t = foldr1 Logic.mk_conjunction ts;
    val body = ObjectLogic.atomize_term sign t;
    val bodyT = Term.fastype_of body;
  in
    if bodyT = propT then (t, propT, Thm.reflexive (Thm.cterm_of sign t))
    else (body, bodyT, ObjectLogic.atomize_rule sign (Thm.cterm_of sign t))
  end;

fun aprop_tr' n c = (c, fn args =>
  if length args = n then Syntax.const "_aprop" $ Term.list_comb (Syntax.free c, args)
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
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;

    val (body, bodyT, body_eq) = atomize_spec sign norm_ts;
    val env = Term.add_term_free_names (body, []);
    val xs = List.filter (fn (x, _) => x mem_string env) parms;
    val Ts = map #2 xs;
    val extraTs = (Term.term_tfrees body \\ foldr Term.add_typ_tfrees [] Ts)
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

(* CB: modify the locale elements:
   - assumes elements become notes elements,
   - notes elements are lifted
*)

fun change_elem (axms, Assumes asms) =
      apsnd Notes ((axms, asms) |> foldl_map (fn (axs, (a, spec)) =>
        let val (ps,qs) = splitAt(length spec, axs)
        in (qs, (a, [(ps, [])])) end))
  | change_elem e = e;

(* CB: changes only "new" elems, these have identifier ("", _). *)

fun change_elemss axioms elemss = (axioms, elemss) |> foldl_map
  (fn (axms, (id as ("", _), es)) =>
    foldl_map change_elem (axms, map (map_values I I (Drule.satisfy_hyps axioms)) es)
    |> apsnd (pair id)
  | x => x) |> #2;

in

(* CB: main predicate definition function *)

fun define_preds bname (parms, ((exts, exts'), (ints, ints')), defs) elemss thy =
  let
    val (thy', (elemss', more_ts)) =
      if null exts then (thy, (elemss, []))
      else
        let
          val aname = if null ints then bname else bname ^ "_" ^ axiomsN;
          val (def_thy, (statement, intro, axioms)) =
            thy |> def_pred aname parms defs exts exts';
          val elemss' = change_elemss axioms elemss @
            [(("", []), [Assumes [((bname ^ "_" ^ axiomsN, []), [(statement, ([], []))])]])];
        in
          def_thy |> note_thmss_qualified "" aname
            [((introN, []), [([intro], [])])]
          |> #1 |> rpair (elemss', [statement])
        end;
    val (thy'', predicate) =
      if null ints then (thy', ([], []))
      else
        let
          val (def_thy, (statement, intro, axioms)) =
            thy' |> def_pred bname parms defs (ints @ more_ts) (ints' @ more_ts);
          val cstatement = Thm.cterm_of (Theory.sign_of def_thy) statement;
        in
          def_thy |> note_thmss_qualified "" bname
            [((introN, []), [([intro], [])]),
             ((axiomsN, []), [(map Drule.standard axioms, [])])]
          |> #1 |> rpair ([cstatement], axioms)
        end;
  in (thy'', (elemss', predicate)) end;

end;


(* add_locale(_i) *)

local

fun gen_add_locale prep_ctxt prep_expr do_pred bname raw_import raw_body thy =
  (* CB: do_pred controls generation of predicates.
         true -> with, false -> without predicates. *)
  let
    val sign = Theory.sign_of thy;
    val name = Sign.full_name sign bname;
    val _ = conditional (isSome (get_locale thy name)) (fn () =>
      error ("Duplicate definition of locale " ^ quote name));

    val thy_ctxt = ProofContext.init thy;
    val (((import_ctxt, import_elemss), (body_ctxt, body_elemss)), text) =
      prep_ctxt raw_import raw_body thy_ctxt;
    val elemss = import_elemss @ body_elemss;

    val (pred_thy, (elemss', predicate as (predicate_statement, predicate_axioms))) =
      if do_pred then thy |> define_preds bname text elemss
      else (thy, (elemss, ([], [])));
    val pred_ctxt = ProofContext.init pred_thy;

    fun axiomify axioms elemss = 
      (axioms, elemss) |> foldl_map (fn (axs, (id, elems)) => let
                   val ts = List.concat (List.mapPartial (fn (Assumes asms) =>
                     SOME (List.concat (map (map #1 o #2) asms)) | _ => NONE) elems);
                   val (axs1, axs2) = splitAt (length ts, axs);
                 in (axs2, ((id, axs1), elems)) end)
        |> snd;
    val (ctxt, (_, facts)) = activate_facts (K I)
      (pred_ctxt, axiomify predicate_axioms elemss');
    val export = ProofContext.export_standard predicate_statement ctxt pred_ctxt;
    val facts' = facts |> map (fn (a, ths) => ((a, []), [(map export ths, [])]));
  in
    pred_thy
    |> note_thmss_qualified "" name facts' |> #1
    |> declare_locale name
    |> put_locale name {predicate = predicate, import = prep_expr sign raw_import,
        elems = map (fn e => (e, stamp ())) (List.concat (map #2 (List.filter (equal "" o #1 o #1) elemss'))),
        params = (params_of elemss', map #1 (params_of body_elemss))}
  end;

in

val add_locale = gen_add_locale read_context intern_expr;
val add_locale_i = gen_add_locale cert_context (K I);

end;

val _ = Context.add_setup
 [add_locale_i true "var" empty [Fixes [(Syntax.internal "x", NONE, SOME Syntax.NoSyn)]],
  add_locale_i true "struct" empty [Fixes [(Syntax.internal "S", NONE, NONE)]]];



(** Interpretation commands **)

local

(* extract proof obligations (assms and defs) from elements *)

(* check if defining equation has become t == t, these are dropped
   in extract_asms_elem, as they lead to trivial proof obligations *)
(* currently disabled *)
fun check_def (_, (def, _)) = SOME def;
(*
fun check_def (_, (def, _)) =
      if def |> Logic.dest_equals |> op aconv
      then NONE else SOME def;
*)

fun extract_asms_elem (ts, Fixes _) = ts
  | extract_asms_elem (ts, Assumes asms) =
      ts @ List.concat (map (fn (_, ams) => map (fn (t, _) => t) ams) asms)
  | extract_asms_elem (ts, Defines defs) =
      ts @ List.mapPartial check_def defs
  | extract_asms_elem (ts, Notes _) = ts;

fun extract_asms_elems (id, elems) =
      (id, Library.foldl extract_asms_elem ([], elems));

fun extract_asms_elemss elemss =
      map extract_asms_elems elemss;

(* activate instantiated facts in theory or context *)

fun activate_facts_elem _ _ _ _ (thy_ctxt, Fixes _) = thy_ctxt
  | activate_facts_elem _ _ _ _ (thy_ctxt, Assumes _) = thy_ctxt
  | activate_facts_elem _ _ _ _ (thy_ctxt, Defines _) = thy_ctxt
  | activate_facts_elem note_thmss attrib
        disch (prfx, atts) (thy_ctxt, Notes facts) =
      let
        val reg_atts = map (attrib thy_ctxt) atts;
        (* discharge hyps in attributes *)
        val facts = map_attrib_facts (attrib thy_ctxt o Args.map_values I I I disch) facts;
        val facts' = map (apfst (apsnd (fn a => a @ reg_atts))) facts;
        (* discharge hyps *)
        val facts'' = map (apsnd (map (apfst (map disch)))) facts';
        (* prefix names *)
        val facts''' = map (apfst (apfst (fn name =>
          if prfx = "" orelse name = "" then name
          else NameSpace.pack [prfx, name]))) facts'';
      in
        fst (note_thmss prfx facts''' thy_ctxt)
      end;

fun activate_facts_elems get_reg note_thmss attrib
        disch (thy_ctxt, (id, elems)) =
      let
        val ((prfx, atts2), _) = valOf (get_reg thy_ctxt id)
          handle Option => error ("(internal) unknown registration of " ^
            quote (fst id) ^ " while activating facts.");
      in
        Library.foldl (activate_facts_elem note_thmss attrib
          disch (prfx, atts2)) (thy_ctxt, elems)
      end;

fun gen_activate_facts_elemss get_reg note_thmss attrib standard
        all_elemss new_elemss thy_ctxt =
      let
        val prems = List.concat (List.mapPartial (fn (id, _) =>
              Option.map snd (get_reg thy_ctxt id)
                handle Option => error ("(internal) unknown registration of " ^
                  quote (fst id) ^ " while activating facts.")) all_elemss);
      in Library.foldl (activate_facts_elems get_reg note_thmss attrib
        (standard o Drule.fconv_rule (Thm.beta_conversion true) o
          Drule.satisfy_hyps prems)) (thy_ctxt, new_elemss) end;

val global_activate_facts_elemss = gen_activate_facts_elemss
      (fn thy => fn (name, ps) =>
        get_global_registration thy (name, map Logic.varify ps))
      (fn prfx => PureThy.note_thmss_accesses_i (global_accesses prfx)
        (Drule.kind ""))
      Attrib.global_attribute_i Drule.standard;
val local_activate_facts_elemss = gen_activate_facts_elemss
      get_local_registration
      (fn prfx => ProofContext.note_thmss_accesses_i (local_accesses prfx))
      Attrib.context_attribute_i I;

fun gen_prep_registration mk_ctxt is_local read_terms test_reg put_reg activate
    attn expr insts thy_ctxt =
  let
    val ctxt = mk_ctxt thy_ctxt;
    val sign = ProofContext.sign_of ctxt;

    val ctxt' = ctxt |> ProofContext.theory_of |> ProofContext.init;
    val (ids, raw_elemss) = flatten (ctxt', intern_expr sign) ([], Expr expr);
    val do_close = false;  (* effect unknown *)
    val ((parms, all_elemss, _), (spec, (xs, defs, _))) =
          read_elemss do_close ctxt' [] raw_elemss [];


    (** compute instantiation **)

    (* user input *)
    val insts = if length parms < length insts
         then error "More arguments than parameters in instantiation."
         else insts @ replicate (length parms - length insts) NONE;
    val (ps, pTs) = split_list parms;
    val pvTs = map Type.varifyT pTs;

    (* instantiations given by user *)
    val given = List.mapPartial (fn (_, (NONE, _)) => NONE
         | (x, (SOME inst, T)) => SOME (x, (inst, T))) (ps ~~ (insts ~~ pvTs));
    val (given_ps, given_insts) = split_list given;
    val tvars = foldr Term.add_typ_tvars [] pvTs;
    val used = foldr Term.add_typ_varnames [] pvTs;
    fun sorts (a, i) = assoc (tvars, (a, i));
    val (vs, vinst) = read_terms thy_ctxt sorts used given_insts;
    val vars = foldl Term.add_term_tvar_ixns [] vs \\ map fst tvars;
    val vars' = Library.foldl Term.add_term_varnames (vars, vs);
    val _ = if null vars' then ()
         else error ("Illegal schematic variable(s) in instantiation: " ^
           commas_quote (map Syntax.string_of_vname vars'));
    (* replace new types (which are TFrees) by ones with new names *)
    val new_Tnames = foldr Term.add_term_tfree_names [] vs;
    val new_Tnames' = Term.invent_names used "'a" (length new_Tnames);
    val renameT =
          if is_local then I
          else Type.unvarifyT o Term.map_type_tfree (fn (a, s) =>
            TFree (valOf (assoc (new_Tnames ~~ new_Tnames', a)), s));
    val rename =
          if is_local then I
          else Term.map_term_types renameT;

    val tinst = Symtab.make (map
                (fn ((x, 0), T) => (x, T |> renameT)
                  | ((_, n), _) => error "Internal error var in prep_registration") vinst);
    val inst = Symtab.make (given_ps ~~ map rename vs);

    (* defined params without user input *)
    val not_given = List.mapPartial (fn (x, (NONE, T)) => SOME (x, T)
         | (_, (SOME _, _)) => NONE) (ps ~~ (insts ~~ pTs));
    fun add_def ((inst, tinst), (p, pT)) =
      let
        val (t, T) = case find_first (fn (Free (a, _), _) => a = p) defs of
               NONE => error ("Instance missing for parameter " ^ quote p)
             | SOME (Free (_, T), t) => (t, T);
        val d = t |> inst_tab_term (inst, tinst) |> Envir.beta_norm;
      in (Symtab.update_new ((p, d), inst), tinst) end;
    val (inst, tinst) = Library.foldl add_def ((inst, tinst), not_given);
    (* Note: inst and tinst contain no vars. *)

    (** compute proof obligations **)

    (* restore "small" ids *)
    val ids' = map (fn ((n, ps), _) =>
          (n, map (fn p => Free (p, valOf (assoc (parms, p)))) ps)) ids;

    (* instantiate ids and elements *)
    val inst_elemss = map
          (fn (id, (_, elems)) => inst_tab_elems sign (inst, tinst) (id, 
            map (fn Int e => e) elems)) 
          (ids' ~~ all_elemss);

    (* remove fragments already registered with theory or context *)
    val new_inst_elemss = List.filter (fn (id, _) =>
          not (test_reg thy_ctxt id)) inst_elemss;
    val new_ids = map #1 new_inst_elemss;

    val propss = extract_asms_elemss new_inst_elemss;

    val bind_attrib = Attrib.crude_closure ctxt o Args.assignable;
    val attn' = apsnd (map (bind_attrib o Attrib.intern_src sign)) attn;

    (** add registrations to theory or context,
        without theorems, these are added after the proof **)
    (* TODO: this is potentially problematic, since a proof of the
       interpretation might contain a reference to the incomplete
       registration. *)

    val thy_ctxt' = Library.foldl (fn (thy_ctxt, (id, _)) =>
          put_reg id attn' thy_ctxt) (thy_ctxt, new_inst_elemss);

  in (thy_ctxt', propss, activate inst_elemss new_inst_elemss) end;

in

val prep_global_registration = gen_prep_registration
     ProofContext.init false
     (fn thy => fn sorts => fn used =>
       Sign.read_def_terms (Theory.sign_of thy, K NONE, sorts) used true)
     (fn thy => fn (name, ps) =>
       test_global_registration thy (name, map Logic.varify ps))
     (fn (name, ps) => put_global_registration (name, map Logic.varify ps))
     global_activate_facts_elemss;

val prep_local_registration = gen_prep_registration
     I true
     (fn ctxt => ProofContext.read_termTs ctxt (K false) (K NONE))
     smart_test_registration
     put_local_registration
     local_activate_facts_elemss;

end;  (* local *)


end;
