(*  Title:      Pure/locale.ML
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Locales. The theory section 'locale' declarings constants, assumptions and
definitions that have local scope.  Typical form is

    locale Locale_name =
      fixes   (*variables that are fixed in the locale's scope*)
	v :: T
      assumes (*meta-hypothesis that hold in the locale*)
	Asm_name "meta-formula"  
      defines (*local definitions of fixed variables in terms of others*)
	v_def "v x == ...x..."

TODO:
  - operations on locales: renaming.
*)

signature BASIC_LOCALE =
sig
  val print_locales: theory -> unit
  val print_goals: int -> thm -> unit
  val print_goals_marker: string -> int -> thm -> unit
  val thm: xstring -> thm
  val thms: xstring -> thm list
  val Open_locale: xstring -> unit
  val Close_locale: xstring -> unit
  val Print_scope: unit -> unit
end;

signature LOCALE =
sig
  include BASIC_LOCALE
  val get_thm: theory -> xstring -> thm
  val get_thms: theory -> xstring -> thm list
  type locale
  val add_locale: bstring -> (bstring option) -> (string * string * mixfix) list ->
    (string * string) list -> (string * string) list -> theory -> theory
  val add_locale_i: bstring -> (bstring option) -> (string * typ * mixfix) list ->
    (string * term) list -> (string * term) list -> theory -> theory
  val open_locale: xstring -> theory -> theory
  val close_locale: xstring -> theory -> theory
  val print_scope: theory -> unit
  val in_locale: term list -> Sign.sg -> bool
  val is_open_loc_sg: Sign.sg -> bool
  val is_open_loc: theory -> bool
  val read_cterm: Sign.sg -> string * typ -> cterm
  val get_scope: theory -> (string * locale) list
  val get_scope_sg: Sign.sg -> (string * locale) list
  val collect_consts: Sign.sg -> string list
  val setup: (theory -> theory) list
end;

structure Locale: LOCALE =
struct


(** type locale **)

type locale =
 {ancestor: string option,
  consts: (string * typ) list,
  nosyn: string list,
  rules: (string * term) list,
  defs: (string * term) list,
  thms: (string * thm) list,
  defaults: (string * sort) list * (string * typ) list * string list};

fun make_locale ancestor consts nosyn rules defs thms defaults =
  {ancestor = ancestor, consts = consts, nosyn = nosyn, rules = rules, 
   defs = defs, thms = thms, defaults = defaults}: locale;

fun pretty_locale sg (name, {ancestor, consts, rules, defs, nosyn = _, thms = _, defaults = _}) =
  let
    val prt_typ = Pretty.quote o Sign.pretty_typ sg;
    val prt_term = Pretty.quote o Sign.pretty_term sg;

    fun pretty_const (c, T) = Pretty.block
      [Pretty.str (c ^ " ::"), Pretty.brk 1, prt_typ T];

    fun pretty_axiom (a, t) = Pretty.block
      [Pretty.str (a ^ ":"), Pretty.brk 1, prt_term t];

    val anc = case ancestor of
                  None => ""
                | Some(loc) => ((Sign.base_name loc) ^ " +")
  in
    Pretty.big_list (name ^ " = " ^ anc)
     [Pretty.big_list "consts:" (map pretty_const consts),
      Pretty.big_list "rules:" (map pretty_axiom rules),
      Pretty.big_list "defs:" (map pretty_axiom defs)]
  end;



(** theory data **)

(* data kind 'Pure/locales' *)

type locale_data =
  {space: NameSpace.T,
    locales: locale Symtab.table,
    scope: (string * locale) list ref};

fun make_locale_data space locales scope =
  {space = space, locales = locales, scope = scope}: locale_data;

structure LocalesArgs =
struct
  val name = "Pure/locales";
  type T = locale_data;

  val empty = make_locale_data NameSpace.empty Symtab.empty (ref []);
  fun copy {space, locales, scope = ref locs} = make_locale_data space locales (ref locs);
  fun prep_ext {space, locales, scope = _} = make_locale_data space locales (ref []);
  fun merge ({space = space1, locales = locales1, scope = _},
    {space = space2, locales = locales2, scope = _}) =
      make_locale_data (NameSpace.merge (space1, space2))
        (Symtab.merge (K true) (locales1, locales2))
        (ref []);

  fun print sg {space, locales, scope} =
    let
      fun extrn name =
        if ! long_names then name else NameSpace.extern space name;
      val locs = map (apfst extrn) (Symtab.dest locales);
      val scope_names = rev (map (extrn o fst) (! scope));
    in
      Pretty.writeln (Display.pretty_name_space ("locale name space", space));
      Pretty.writeln (Pretty.big_list "locales:" (map (pretty_locale sg) locs));
      Pretty.writeln (Pretty.strs ("current scope:" :: scope_names))
    end;
end;


structure LocalesData = TheoryDataFun(LocalesArgs);
val print_locales = LocalesData.print;


(* access locales *)

fun get_locale_sg sg name = Symtab.lookup (#locales (LocalesData.get_sg sg), name);

val get_locale = get_locale_sg o Theory.sign_of;

fun put_locale (name, locale) thy =
  let
    val {space, locales, scope} = LocalesData.get thy;
    val space' = NameSpace.extend (space, [name]);
    val locales' = Symtab.update ((name, locale), locales);
  in thy |> LocalesData.put (make_locale_data space' locales' scope) end;

fun lookup_locale thy xname =
  let
    val {space, locales, ...} = LocalesData.get thy;
    val name = NameSpace.intern space xname;
  in apsome (pair name) (get_locale thy name) end;


(* access scope *)

val get_scope_sg = ! o #scope o LocalesData.get_sg;

val get_scope = get_scope_sg o Theory.sign_of;

fun change_scope f thy =
  let val {scope, ...} = LocalesData.get thy
  in scope := f (! scope) end;



(** scope operations **)

(* change scope *)

fun the_locale thy xname =
  (case lookup_locale thy xname of
    Some loc => loc
  | None => error ("Unknown locale " ^ quote xname));

fun open_locale xname thy =
  let val loc = the_locale thy xname;
      val anc = #ancestor(#2(loc));
      val cur_sc = get_scope thy;
      fun opn lc th = (change_scope (cons lc) th; th)
  in case anc of
         None => opn loc thy
       | Some(loc') => 
           if loc' mem (map fst cur_sc) 
           then opn loc thy
           else (Pretty.writeln(Pretty.str 
                   ("Opening locale " ^ quote loc' ^ ", required by " ^ quote xname));
                 opn loc (open_locale (Sign.base_name loc') thy))
  end;

fun pop_locale [] = error "Currently no open locales"
  | pop_locale (_ :: locs) = locs;

fun close_locale name thy = 
   let val cur_sc = get_scope thy;
       val lname = if null(cur_sc) then "" else (fst (hd cur_sc));
       val bname = Sign.base_name lname
   in if (name = bname) then (change_scope pop_locale thy; thy)
      else (Pretty.writeln(Pretty.str ("locale " ^ name ^ " is not top of scope"));
            Pretty.writeln(Pretty.str ("Command has no effect, top is " ^ lname)); thy)
   end;

fun print_scope thy = 
Pretty.writeln (Pretty.strs ("current scope:" :: rev(map (Sign.base_name o fst) (get_scope thy))));

(*implicit context versions*)
fun Open_locale xname = (open_locale xname (Context.the_context ()); ());
fun Close_locale xname = (close_locale xname (Context.the_context ()); ());
fun Print_scope () = (print_scope (Context.the_context ()); ());


(** functions for goals.ML **)

(* in_locale: check if hyps (: term list) of a proof are contained in the
   (current) scope. This function is needed in prepare_proof. It needs to
   refer to the signature, because theory is not available in prepare_proof. *)

fun in_locale hyps sg =
    let val cur_sc = get_scope_sg sg;
        val rule_lists = map (#rules o snd) cur_sc;
        val def_lists = map (#defs o snd) cur_sc;
        val rules = map snd (foldr (op union) (rule_lists, []));
        val defs = map snd (foldr (op union) (def_lists, []));
        val defnrules = rules @ defs;
    in
        hyps subset defnrules
    end;


(* is_open_loc: check if any locale is open, i.e. in the scope of the current thy *)
fun is_open_loc_sg sign =
    let val cur_sc = get_scope_sg sign
    in not(null(cur_sc)) end;

val is_open_loc = is_open_loc_sg o Theory.sign_of;


(* get theorems *)

fun get_thm_locale name ((_, {thms, ...}: locale)) = assoc (thms, name);

fun get_thmx f get thy name =
  (case get_first (get_thm_locale name) (get_scope thy) of
    Some thm => f thm
  | None => get thy name);

val get_thm = get_thmx I PureThy.get_thm;
val get_thms = get_thmx (fn x => [x]) PureThy.get_thms;

fun thm name = get_thm (Context.the_context ()) name;
fun thms name = get_thms (Context.the_context ()) name;


(* get the defaults of a locale, for extension *)

fun get_defaults thy name = 
  let val (lname, loc) = the_locale thy name;
  in #defaults(loc)
  end;


(** define locales **)

(* prepare types *)

fun read_typ sg (envT, s) =
  let
    fun def_sort (x, ~1) = assoc (envT, x)
      | def_sort _ = None;
    val T = Type.no_tvars (Sign.read_typ (sg, def_sort) s) handle TYPE (msg, _, _) => error msg;
  in (Term.add_typ_tfrees (T, envT), T) end;

fun cert_typ sg (envT, raw_T) =
  let val T = Type.no_tvars (Sign.certify_typ sg raw_T) handle TYPE (msg, _, _) => error msg
  in (Term.add_typ_tfrees (T, envT), T) end;


(* prepare props *)

val add_frees = foldl_aterms (fn (vs, Free v) => v ins vs | (vs, _) => vs);

fun enter_term t (envS, envT, used) =
  (Term.add_term_tfrees (t, envS), add_frees (envT, t), Term.add_term_tfree_names (t, used));

fun read_axm sg ((envS, envT, used), (name, s)) =
  let
    fun def_sort (x, ~1) = assoc (envS, x)
      | def_sort _ = None;
    fun def_type (x, ~1) = assoc (envT, x)
      | def_type _ = None;
    val (_, t) = Theory.read_def_axm (sg, def_type, def_sort) used (name, s);
  in
    (enter_term t (envS, envT, used), t)
  end;


fun cert_axm sg ((envS, envT, used), (name, raw_t)) =
  let val (_, t) = Theory.cert_axm sg (name, raw_t)
  in (enter_term t (envS, envT, used), t) end;


(* Locale.read_cterm: read in a string as a certified term, and respect the bindings
   that already exist for subterms. If no locale is open, this function is equal to
   Thm.read_cterm  *)

fun read_cterm sign =
    let val cur_sc = get_scope_sg sign;
        val defaults = map (#defaults o snd) cur_sc;
        val envS = flat (map #1 defaults);
        val envT = flat (map #2 defaults);
        val used = flat (map #3 defaults);
        fun def_sort (x, ~1) = assoc (envS, x)
          | def_sort _ = None;
        fun def_type (x, ~1) = assoc (envT, x)
          | def_type _ = None;
    in (if (is_open_loc_sg sign)
        then (#1 o read_def_cterm (sign, def_type, def_sort) used true)
        else Thm.read_cterm sign)
    end;

(* basic functions needed for definitions and display *)
(* collect all locale constants of a scope, i.e. a list of locales *)
fun collect_consts sg =
    let val cur_sc = get_scope_sg sg;
        val locale_list = map snd cur_sc;
        val const_list = flat (map #consts locale_list)
    in map fst const_list end;

(* filter out the Free's in a term *)
fun list_frees t =
    case t of Const(c,T) => []
  | Var(v,T) => []
  | Free(v,T)=> [Free(v,T)]
  | Bound x  => []
  | Abs(a,T,u) => list_frees u
  | t1 $ t2  => (list_frees t1)  @ (list_frees t2);

(* filter out all Free's in a term that are not contained
   in a list of strings. Used to prepare definitions. The list of strings
   will be the consts of the scope. We filter out the "free" Free's to be
   able to bind them *)
fun difflist term clist =
    let val flist = list_frees term;
        fun builddiff [] sl = []
          | builddiff (t :: tl) sl =
            let val Free(v,T) = t
            in
                if (v mem sl)
                then builddiff tl sl
                else t :: (builddiff tl sl)
            end;
    in distinct(builddiff flist clist) end;

(* Bind a term with !! over a list of "free" Free's.
   To enable definitions like x + y == .... (without quantifier).
   Complications, because x and y have to be removed from defaults *)
fun abs_over_free clist ((defaults: (string * sort) list * (string * typ) list * string list), (s, term)) =
    let val diffl = rev(difflist term clist);
        fun abs_o (t, (x as Free(v,T))) = all(T) $ Abs(v, T, abstract_over (x,t))
          | abs_o (_ , _) = error ("Can't be: abs_over_free");
        val diffl' = map (fn (Free (s, T)) => s) diffl;
        val defaults' = (#1 defaults, filter (fn x => not((fst x) mem diffl')) (#2 defaults), #3 defaults)
    in (defaults', (s, foldl abs_o (term, diffl))) end;

(* assume a definition, i.e assume the cterm of a definiton term and then eliminate
   the binding !!, so that the def can be applied as rewrite. The meta hyp will still contain !! *)
fun prep_hyps clist sg = forall_elim_vars(0) o Thm.assume o (Thm.cterm_of sg);


(* concrete syntax *)

fun mark_syn c = "\\<^locale>" ^ c;

fun mk_loc_tr c ts = list_comb (Free (c, dummyT), ts);


(* add_locale *)

fun gen_add_locale prep_typ prep_term bname bancestor raw_consts raw_rules raw_defs thy =
  let val sign = Theory.sign_of thy;

    val name = Sign.full_name sign bname;

    val (envSb, old_loc_consts, _) = 
                    case bancestor of
                       Some(loc) => (get_defaults thy loc)
                     | None      => ([],[],[]);

    val old_nosyn = case bancestor of 
                       Some(loc) => #nosyn(#2(the_locale thy loc))
                     | None      => [];

    (* Get the full name of the ancestor *)
    val ancestor = case bancestor of 
                       Some(loc) => Some(#1(the_locale thy loc))
                     | None      => None;

     (* prepare locale consts *)

    fun prep_const (envS, (raw_c, raw_T, raw_mx)) =
      let
        val c = Syntax.const_name raw_c raw_mx;
        val c_syn = mark_syn c;
        val mx = Syntax.fix_mixfix raw_c raw_mx;
        val (envS', T) = prep_typ sign (envS, raw_T) handle ERROR =>
          error ("The error(s) above occured in locale constant " ^ quote c);
        val trfun = if mx = Syntax.NoSyn then None else Some (c_syn, mk_loc_tr c);
      in (envS', ((c, T), (c_syn, T, mx), trfun)) end;

    val (envS0, loc_consts_syn) = foldl_map prep_const (envSb, raw_consts);
    val loc_consts = map #1 loc_consts_syn;
    val loc_consts = old_loc_consts @ loc_consts;
    val loc_syn = map #2 loc_consts_syn;
    val nosyn = old_nosyn @ (map (#1 o #1) (filter (fn x => (#3(#2 x)) = NoSyn) loc_consts_syn));
    val loc_trfuns = mapfilter #3 loc_consts_syn;


    (* 1st stage: syntax_thy *)

    val syntax_thy =
      thy
      |> Theory.add_modesyntax_i ("", true) loc_syn
      |> Theory.add_trfuns ([], loc_trfuns, [], []);

    val syntax_sign = Theory.sign_of syntax_thy;


    (* prepare rules and defs *)

    fun prep_axiom (env, (a, raw_t)) =
      let
        val (env', t) = prep_term syntax_sign (env, (a, raw_t)) handle ERROR =>
          error ("The error(s) above occured in locale rule / definition " ^ quote a);
      in (env', (a, t)) end;

    val ((envS1, envT1, used1), loc_rules) =
      foldl_map prep_axiom ((envS0, loc_consts, map fst envS0), raw_rules);
    val (defaults, loc_defs) = 
	foldl_map prep_axiom ((envS1, envT1, used1), raw_defs);

    val old_loc_consts = collect_consts syntax_sign;
    val new_loc_consts = (map #1 loc_consts);
    val all_loc_consts = old_loc_consts @ new_loc_consts;

    val (defaults, loc_defs_terms) = 
	foldl_map (abs_over_free all_loc_consts) (defaults, loc_defs);
    val loc_defs_thms = 
	map (apsnd (prep_hyps (map #1 loc_consts) syntax_sign)) loc_defs_terms;
    val (defaults, loc_thms_terms) = 
	foldl_map (abs_over_free all_loc_consts) (defaults, loc_rules);
    val loc_thms = map (apsnd (prep_hyps (map #1 loc_consts) syntax_sign))
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
          val check = defs subset loc_consts
      in if check then [] 
         else ["defined item not declared fixed in locale " ^ quote name]
      end; 

    (* check that variables on rhs of definitions are either fixed or on lhs *)
    val err_var_rhs = 
      let fun compare_var_sides (t, (_, Const ("==", _) $ d1 $ d2)) = 
		let val varl1 = difflist d1 all_loc_consts;
		    val varl2 = difflist d2 all_loc_consts
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
		   make_locale ancestor loc_consts nosyn loc_thms_terms 
                                        loc_defs_terms   loc_thms defaults)
  end;


val add_locale = gen_add_locale read_typ read_axm;
val add_locale_i = gen_add_locale cert_typ cert_axm;

(** print functions **)
(* idea: substitute all locale contants (Free's) that are syntactical by their
         "real" constant representation (i.e. \\<^locale>constname).
   - function const_ssubst does this substitution
   - function Locale.pretty_term:
             if locale is open then do this substitution & then call Sign.pretty_term
             else call Sign.pretty_term
*)
(* substitutes all Free variables s in t by Const's s *)
fun const_ssubst t s =
    case t  of
        Free(v,T) => if v = s then Const("\\<^locale>" ^ s,T) else Free(v,T)
      | Const(c,T) => Const(c,T)
      | Var(v,T) => Var(v,T)
      | Bound x  => Bound x
      | Abs(a,T,u) => Abs(a,T, const_ssubst u s)
      | t1 $ t2  => const_ssubst t1 s $ const_ssubst t2 s;

(* FIXME: improve: can be expressed with foldl *)
fun const_ssubst_list [] t = t
  | const_ssubst_list (s :: l) t = const_ssubst_list l (const_ssubst t s);

(* Locale.pretty_term *)
fun pretty_term sign =
    if (is_open_loc_sg sign) then
        let val locale_list = map snd(get_scope_sg sign);
            val nosyn = flat (map #nosyn locale_list);
            val str_list = (collect_consts sign) \\ nosyn
        in Sign.pretty_term sign o (const_ssubst_list str_list)
        end
    else Sign.pretty_term sign;



(** print_goals **)

(*print thm A1,...,An/B in "goal style" -- premises as numbered subgoals*)

local

  (* utils *)

  fun ins_entry (x, y) [] = [(x, [y])]
    | ins_entry (x, y) ((pair as (x', ys')) :: pairs) =
        if x = x' then (x', y ins ys') :: pairs
        else pair :: ins_entry (x, y) pairs;

  fun add_consts (Const (c, T), env) = ins_entry (T, (c, T)) env
    | add_consts (t $ u, env) = add_consts (u, add_consts (t, env))
    | add_consts (Abs (_, _, t), env) = add_consts (t, env)
    | add_consts (_, env) = env;

  fun add_vars (Free (x, T), env) = ins_entry (T, (x, ~1)) env
    | add_vars (Var (xi, T), env) = ins_entry (T, xi) env
    | add_vars (Abs (_, _, t), env) = add_vars (t, env)
    | add_vars (t $ u, env) = add_vars (u, add_vars (t, env))
    | add_vars (_, env) = env;

  fun add_varsT (Type (_, Ts), env) = foldr add_varsT (Ts, env)
    | add_varsT (TFree (x, S), env) = ins_entry (S, (x, ~1)) env
    | add_varsT (TVar (xi, S), env) = ins_entry (S, xi) env;

  fun sort_idxs vs = map (apsnd (sort (prod_ord string_ord int_ord))) vs;
  fun sort_cnsts cs = map (apsnd (sort_wrt fst)) cs;


  (* prepare atoms *)

  fun consts_of t = sort_cnsts (add_consts (t, []));
  fun vars_of t = sort_idxs (add_vars (t, []));
  fun varsT_of t = rev (sort_idxs (it_term_types add_varsT (t, [])));

in

  fun print_goals_marker begin_goal maxgoals state =
    let
      val {sign, ...} = rep_thm state;

      val prt_term = pretty_term sign;
      val prt_typ = Sign.pretty_typ sign;
      val prt_sort = Sign.pretty_sort sign;

      fun prt_atoms prt prtT (X, xs) = Pretty.block
        [Pretty.block (Pretty.commas (map prt xs)), Pretty.str " ::",
          Pretty.brk 1, prtT X];

      fun prt_var (x, ~1) = prt_term (Syntax.free x)
        | prt_var xi = prt_term (Syntax.var xi);

      fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
        | prt_varT xi = prt_typ (TVar (xi, []));

      val prt_consts = prt_atoms (prt_term o Const) prt_typ;
      val prt_vars = prt_atoms prt_var prt_typ;
      val prt_varsT = prt_atoms prt_varT prt_sort;


      fun print_list _ _ [] = ()
        | print_list name prt lst = (writeln "";
            Pretty.writeln (Pretty.big_list name (map prt lst)));

      fun print_subgoals (_, []) = ()
        | print_subgoals (n, A :: As) = (Pretty.writeln (Pretty.blk (0,
            [Pretty.str (begin_goal ^ " " ^ string_of_int n ^ ". "), prt_term A]));
              print_subgoals (n + 1, As));

      val print_ffpairs =
        print_list "Flex-flex pairs:" (prt_term o Logic.mk_flexpair);

      val print_consts = print_list "Constants:" prt_consts o consts_of;
      val print_vars = print_list "Variables:" prt_vars o vars_of;
      val print_varsT = print_list "Type variables:" prt_varsT o varsT_of;


      val {prop, ...} = rep_thm state;
      val (tpairs, As, B) = Logic.strip_horn prop;
      val ngoals = length As;

      fun print_gs (types, sorts) =
       (Pretty.writeln (prt_term B);
        if ngoals = 0 then writeln "No subgoals!"
        else if ngoals > maxgoals then
          (print_subgoals (1, take (maxgoals, As));
            writeln ("A total of " ^ string_of_int ngoals ^ " subgoals..."))
        else print_subgoals (1, As);

        print_ffpairs tpairs;

        if types andalso ! show_consts then print_consts prop else ();
        if types then print_vars prop else ();
        if sorts then print_varsT prop else ());
    in
      setmp show_no_free_types true
        (setmp show_types (! show_types orelse ! show_sorts)
          (setmp show_sorts false print_gs))
     (! show_types orelse ! show_sorts, ! show_sorts)
  end;

  val print_goals = print_goals_marker "";

end;



(** locale theory setup **)

val setup =
 [LocalesData.init];

end;

structure BasicLocale: BASIC_LOCALE = Locale;
open BasicLocale;
