(*  Title: 	Pure/goals.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson and Florian Kammueller, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Old-style locales and goal stack package.  The goal stack initially
holds a dummy proof, and can never become empty.  Each goal stack
consists of a list of levels.  The undo list is a list of goal stacks.
Finally, there may be a stack of pending proofs.  Additional support
for locales.
*)

signature BASIC_GOALS =
sig
  val Open_locale: xstring -> unit
  val Close_locale: xstring -> unit
  val Print_scope: unit -> unit
  val thm: xstring -> thm
  val thms: xstring -> thm list
  type proof
  val reset_goals       : unit -> unit
  val atomic_goal	: theory -> string -> thm list
  val atomic_goalw	: theory -> thm list -> string -> thm list
  val Goal		: string -> thm list
  val Goalw		: thm list -> string -> thm list
  val ba		: int -> unit
  val back		: unit -> unit
  val bd		: thm -> int -> unit
  val bds		: thm list -> int -> unit
  val be		: thm -> int -> unit
  val bes		: thm list -> int -> unit
  val br		: thm -> int -> unit
  val brs		: thm list -> int -> unit
  val bw		: thm -> unit
  val bws		: thm list -> unit
  val by		: tactic -> unit
  val byev		: tactic list -> unit
  val chop		: unit -> unit
  val choplev		: int -> unit
  val export_thy        : theory -> thm -> thm
  val export            : thm -> thm
  val Export		: thm -> thm
  val fa		: unit -> unit
  val fd		: thm -> unit
  val fds		: thm list -> unit
  val fe		: thm -> unit
  val fes		: thm list -> unit
  val filter_goal	: (term*term->bool) -> thm list -> int -> thm list
  val fr		: thm -> unit
  val frs		: thm list -> unit
  val getgoal		: int -> term
  val gethyps		: int -> thm list
  val goal		: theory -> string -> thm list
  val goalw		: theory -> thm list -> string -> thm list
  val goalw_cterm	: thm list -> cterm -> thm list
  val pop_proof		: unit -> thm list
  val pr		: unit -> unit
  val disable_pr        : unit -> unit
  val enable_pr         : unit -> unit
  val prlev		: int -> unit
  val prlim		: int -> unit
  val premises		: unit -> thm list
  val prin		: term -> unit
  val printyp		: typ -> unit
  val pprint_term	: term -> pprint_args -> unit
  val pprint_typ	: typ -> pprint_args -> unit
  val print_exn		: exn -> 'a
  val print_sign_exn	: Sign.sg -> exn -> 'a
  val prove_goal	: theory -> string -> (thm list -> tactic list) -> thm
  val prove_goalw      : theory->thm list->string->(thm list->tactic list)->thm
  val prove_goalw_cterm	: thm list->cterm->(thm list->tactic list)->thm
  val prove_goalw_cterm_nocheck	: thm list->cterm->(thm list->tactic list)->thm
  val quick_and_dirty_prove_goalw_cterm: theory -> thm list -> cterm
    -> (thm list -> tactic list) -> thm
  val push_proof	: unit -> unit
  val read		: string -> term
  val ren		: string -> int -> unit
  val restore_proof	: proof -> thm list
  val result		: unit -> thm  
  val result_error_fn   : (thm -> string -> thm) ref
  val rotate_proof	: unit -> thm list
  val uresult		: unit -> thm  
  val save_proof	: unit -> proof
  val topthm		: unit -> thm
  val undo		: unit -> unit
  val bind_thm          : string * thm -> unit
  val bind_thms         : string * thm list -> unit
  val qed               : string -> unit
  val qed_goal          : string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw         : string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val qed_spec_mp       : string -> unit
  val qed_goal_spec_mp  : string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw_spec_mp : string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val no_qed: unit -> unit
  val thms_containing   : xstring list -> (string * thm) list
  val findI             : int -> (string * thm) list
  val findEs            : int -> (string * thm) list
  val findE             : int -> int -> (string * thm) list
end;

signature GOALS =
sig
  include BASIC_GOALS
  type locale
  val print_locales: theory -> unit
  val get_thm: theory -> xstring -> thm
  val get_thms: theory -> xstring -> thm list
  val add_locale: bstring -> (bstring option) -> (string * string * mixfix) list ->
    (string * string) list -> (string * string) list -> theory -> theory
  val add_locale_i: bstring -> (bstring option) -> (string * typ * mixfix) list ->
    (string * term) list -> (string * term) list -> theory -> theory
  val open_locale: xstring -> theory -> theory
  val close_locale: xstring -> theory -> theory
  val print_scope: theory -> unit
  val read_cterm: Sign.sg -> string * typ -> cterm
  val setup: (theory -> theory) list
end;

structure Goals: GOALS =
struct

(*** Old-style locales ***)

(* Locales. The theory section 'locale' declarings constants,
assumptions and definitions that have local scope.  Typical form is

    locale Locale_name =
      fixes   (*variables that are fixed in the locale's scope*)
	v :: T
      assumes (*meta-hypothesis that hold in the locale*)
	Asm_name "meta-formula"  
      defines (*local definitions of fixed variables in terms of others*)
	v_def "v x == ...x..."
*)

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

(* data kind 'Pure/old-locales' *)

type locale_data =
  {space: NameSpace.T,
    locales: locale Symtab.table,
    scope: (string * locale) list ref};

fun make_locale_data space locales scope =
  {space = space, locales = locales, scope = scope}: locale_data;

structure LocalesArgs =
struct
  val name = "Pure/old-locales";
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
      [Display.pretty_name_space ("locale name space", space),
        Pretty.big_list "locales:" (map (pretty_locale sg) locs),
        Pretty.strs ("current scope:" :: scope_names)]
      |> Pretty.chunks |> Pretty.writeln
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

fun get_scope_sg sg =
  if Sign.eq_sg (sg, Theory.sign_of ProtoPure.thy) then []
  else ! (#scope (LocalesData.get_sg sg));

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
           else (warning ("Opening locale " ^ quote loc' ^ ", required by " ^ 
			  quote xname);
                 opn loc (open_locale (Sign.base_name loc') thy))
  end;

fun pop_locale [] = error "Currently no open locales"
  | pop_locale (_ :: locs) = locs;

fun close_locale name thy = 
   let val lname = (case get_scope thy of (ln,_)::_ => ln
                                        | _ => error "No locales are open!")
       val ok = (name = Sign.base_name lname) handle _ => false
   in if ok then (change_scope pop_locale thy; thy)
      else error ("locale " ^ name ^ " is not top of scope; top is " ^ lname)
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


(* read_cterm: read in a string as a certified term, and respect the bindings
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
   - function pretty_term:
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

(* pretty_term *)
fun pretty_term sign =
    if (is_open_loc_sg sign) then
        let val locale_list = map snd(get_scope_sg sign);
            val nosyn = flat (map #nosyn locale_list);
            val str_list = (collect_consts sign) \\ nosyn
        in Sign.pretty_term sign o (const_ssubst_list str_list)
        end
    else Sign.pretty_term sign;


(** locale theory setup **)

val setup =
 [LocalesData.init];



(*** Goal package ***)

(*Each level of goal stack includes a proof state and alternative states,
  the output of the tactic applied to the preceeding level.  *)
type gstack = (thm * thm Seq.seq) list;

datatype proof = Proof of gstack list * thm list * (bool*thm->thm);


(*** References ***)

(*Current assumption list -- set by "goal".*)
val curr_prems = ref([] : thm list);

(*Return assumption list -- useful if you didn't save "goal"'s result. *)
fun premises() = !curr_prems;

(*Current result maker -- set by "goal", used by "result".  *)
fun init_mkresult _ = error "No goal has been supplied in subgoal module";
val curr_mkresult = ref (init_mkresult: bool*thm->thm);

val dummy = trivial(read_cterm (Theory.sign_of ProtoPure.thy)
    ("PROP No_goal_has_been_supplied",propT));

(*List of previous goal stacks, for the undo operation.  Set by setstate. 
  A list of lists!*)
val undo_list = ref([[(dummy, Seq.empty)]] : gstack list);

(* Stack of proof attempts *)
val proofstack = ref([]: proof list);

(*reset all refs*)
fun reset_goals () =
  (curr_prems := []; curr_mkresult := init_mkresult;
    undo_list := [[(dummy, Seq.empty)]]);


(*** Setting up goal-directed proof ***)

(*Generates the list of new theories when the proof state's signature changes*)
fun sign_error (sign,sign') =
  let val names = Sign.stamp_names_of sign' \\ Sign.stamp_names_of sign
  in  case names of
        [name] => "\nNew theory: " ^ name
      | _       => "\nNew theories: " ^ space_implode ", " names
  end;

(*Default action is to print an error message; could be suppressed for
  special applications.*)
fun result_error_default state msg : thm =
  Pretty.str "Bad final proof state:" :: Display.pretty_goals (!goals_limit) state @
    [Pretty.str msg, Pretty.str "Proof failed!"] |> Pretty.chunks |> Pretty.string_of |> error;

val result_error_fn = ref result_error_default;

(* alternative to standard: this function does not discharge the hypotheses
   first. Is used for locales, in the following function prepare_proof *)
fun varify th =
  let val {maxidx,...} = rep_thm th
  in
    th |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
       |> Drule.strip_shyps_warning
       |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;

(** exporting a theorem out of a locale means turning all meta-hyps into assumptions
    and expand and cancel the locale definitions. 
    export goes through all levels in case of nested locales, whereas
    export_thy just goes one up. **)

fun get_top_scope_thms thy = 
   let val sc = (get_scope_sg (Theory.sign_of thy))
   in if (null sc) then (warning "No locale in theory"; [])
      else map (#prop o rep_thm) (map #2 (#thms(snd(hd sc))))
   end;

fun implies_intr_some_hyps thy A_set th = 
   let 
       val sign = Theory.sign_of thy;
       val used_As = A_set inter #hyps(rep_thm(th));
       val ctl = map (cterm_of sign) used_As
   in foldl (fn (x, y) => Thm.implies_intr y x) (th, ctl)
   end; 

fun standard_some thy A_set th =
  let val {maxidx,...} = rep_thm th
  in
    th |> implies_intr_some_hyps thy A_set
       |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
       |> Drule.strip_shyps_warning
       |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;

fun export_thy thy th = 
  let val A_set = get_top_scope_thms thy
  in
     standard_some thy [] (Seq.hd ((REPEAT (FIRSTGOAL (rtac reflexive_thm))) (standard_some thy A_set th)))
  end;

val export = standard o Seq.hd o (REPEAT (FIRSTGOAL (rtac reflexive_thm))) o standard;

fun Export th = export_thy (the_context ()) th;


(*Common treatment of "goal" and "prove_goal":
  Return assumptions, initial proof state, and function to make result.
  "atomic" indicates if the goal should be wrapped up in the function
  "Goal::prop=>prop" to avoid assumptions being returned separately.
*)
fun prepare_proof atomic rths chorn =
  let val {sign, t=horn,...} = rep_cterm chorn;
      val _ = Term.no_dummy_patterns horn handle TERM (msg, _) => error msg;
      val (_,As,B) = Logic.strip_horn(horn);
      val atoms = atomic andalso
            forall (fn t => not(Logic.is_implies t orelse Logic.is_all t)) As;
      val (As,B) = if atoms then ([],horn) else (As,B);
      val cAs = map (cterm_of sign) As;
      val prems = map (rewrite_rule rths o forall_elim_vars 0 o Thm.assume) cAs;
      val cB = cterm_of sign B;
      val st0 = let val st = Drule.impose_hyps cAs (Drule.mk_triv_goal cB)
                in  rewrite_goals_rule rths st end
      (*discharges assumptions from state in the order they appear in goal;
	checks (if requested) that resulting theorem is equivalent to goal. *)
      fun mkresult (check,state) =
        let val state = Seq.hd (flexflex_rule state)
	    		handle THM _ => state   (*smash flexflex pairs*)
	    val ngoals = nprems_of state
            val ath = implies_intr_list cAs state
            val th = ath RS Drule.rev_triv_goal
            val {hyps,prop,sign=sign',...} = rep_thm th
            val final_th = if (null(hyps)) then standard th else varify th
        in  if not check then final_th
	    else if not (Sign.eq_sg(sign,sign')) then !result_error_fn state
		("Signature of proof state has changed!" ^
		 sign_error (sign,sign'))
            else if ngoals>0 then !result_error_fn state
		(string_of_int ngoals ^ " unsolved goals!")
            else if (not (null hyps) andalso (not (in_locale hyps sign)))
		 then !result_error_fn state
                  ("Additional hypotheses:\n" ^ 
		   cat_lines 
		    (map (Sign.string_of_term sign) 
		     (filter (fn x => (not (in_locale [x] sign))) 
		      hyps)))
	    else if Pattern.matches (#tsig(Sign.rep_sg sign)) 
			            (Envir.beta_norm (term_of chorn), Envir.beta_norm prop)
		 then final_th
	    else  !result_error_fn state "proved a different theorem"
        end
  in
     if Sign.eq_sg(sign, #sign(rep_thm st0))
     then (prems, st0, mkresult)
     else error ("Definitions would change the proof state's signature" ^
		 sign_error (sign, #sign(rep_thm st0)))
  end
  handle THM(s,_,_) => error("prepare_proof: exception THM was raised!\n" ^ s);

(*Prints exceptions readably to users*)
fun print_sign_exn_unit sign e = 
  case e of
     THM (msg,i,thms) =>
	 (writeln ("Exception THM " ^ string_of_int i ^ " raised:\n" ^ msg);
	  seq print_thm thms)
   | THEORY (msg,thys) =>
	 (writeln ("Exception THEORY raised:\n" ^ msg);
	  seq (Pretty.writeln o Display.pretty_theory) thys)
   | TERM (msg,ts) =>
	 (writeln ("Exception TERM raised:\n" ^ msg);
	  seq (writeln o Sign.string_of_term sign) ts)
   | TYPE (msg,Ts,ts) =>
	 (writeln ("Exception TYPE raised:\n" ^ msg);
	  seq (writeln o Sign.string_of_typ sign) Ts;
	  seq (writeln o Sign.string_of_term sign) ts)
   | e => raise e;

(*Prints an exception, then fails*)
fun print_sign_exn sign e = (print_sign_exn_unit sign e; raise ERROR);

(** the prove_goal.... commands
    Prove theorem using the listed tactics; check it has the specified form.
    Augment signature with all type assignments of goal.
    Syntax is similar to "goal" command for easy keyboard use. **)

(*Version taking the goal as a cterm*)
fun prove_goalw_cterm_general check rths chorn tacsf =
  let val (prems, st0, mkresult) = prepare_proof false rths chorn
      val tac = EVERY (tacsf prems)
      fun statef() = 
	  (case Seq.pull (tac st0) of 
	       Some(st,_) => st
	     | _ => error ("prove_goal: tactic failed"))
  in  mkresult (check, cond_timeit (!Library.timing) statef)  end
  handle e => (print_sign_exn_unit (#sign (rep_cterm chorn)) e;
	       writeln ("The exception above was raised for\n" ^ 
		      Display.string_of_cterm chorn); raise e);

(*Two variants: one checking the result, one not.  
  Neither prints runtime messages: they are for internal packages.*)
fun prove_goalw_cterm rths chorn = 
	setmp Library.timing false (prove_goalw_cterm_general true rths chorn)
and prove_goalw_cterm_nocheck rths chorn = 
	setmp Library.timing false (prove_goalw_cterm_general false rths chorn);


(*Version taking the goal as a string*)
fun prove_goalw thy rths agoal tacsf =
  let val sign = Theory.sign_of thy
      val chorn = read_cterm sign (agoal,propT)
  in  prove_goalw_cterm_general true rths chorn tacsf end
  handle ERROR => error (*from read_cterm?*)
		("The error(s) above occurred for " ^ quote agoal);

(*String version with no meta-rewrite-rules*)
fun prove_goal thy = prove_goalw thy [];

(*quick and dirty version (conditional)*)
fun quick_and_dirty_prove_goalw_cterm thy rews ct tacs =
  prove_goalw_cterm rews ct
    (if ! quick_and_dirty then (K [SkipProof.cheat_tac thy]) else tacs);


(*** Commands etc ***)

(*Return the current goal stack, if any, from undo_list*)
fun getstate() : gstack = case !undo_list of 
      []   => error"No current state in subgoal module"
    | x::_ => x;

(*Pops the given goal stack*)
fun pop [] = error"Cannot go back past the beginning of the proof!"
  | pop (pair::pairs) = (pair,pairs);


(* Print a level of the goal stack -- subject to quiet mode *)

val quiet = ref false;
fun disable_pr () = quiet := true;
fun enable_pr () = quiet := false;

fun print_top ((th, _), pairs) =
  if ! quiet then ()
  else ! Display.print_current_goals_fn (length pairs) (! goals_limit) th;

(*Printing can raise exceptions, so the assignment occurs last.
  Can do   setstate[(st,Seq.empty)]  to set st as the state.  *)
fun setstate newgoals = 
  (print_top (pop newgoals);  undo_list := newgoals :: !undo_list);

(*Given a proof state transformation, return a command that updates
    the goal stack*)
fun make_command com = setstate (com (pop (getstate())));

(*Apply a function on proof states to the current goal stack*)
fun apply_fun f = f (pop(getstate()));

(*Return the top theorem, representing the proof state*)
fun topthm () = apply_fun  (fn ((th,_), _) => th);

(*Return the final result.  *)
fun result () = !curr_mkresult (true, topthm());

(*Return the result UNCHECKED that it equals the goal -- for synthesis,
  answer extraction, or other instantiation of Vars *)
fun uresult () = !curr_mkresult (false, topthm());

(*Get subgoal i from goal stack*)
fun getgoal i = List.nth (prems_of (topthm()), i-1)
                handle Subscript => error"getgoal: Goal number out of range";

(*Return subgoal i's hypotheses as meta-level assumptions.
  For debugging uses of METAHYPS*)
local exception GETHYPS of thm list
in
fun gethyps i = 
    (METAHYPS (fn hyps => raise (GETHYPS hyps)) i (topthm());  [])
    handle GETHYPS hyps => hyps
end;

(*Which thms could apply to goal i? (debugs tactics involving filter_thms) *)
fun filter_goal could ths i = filter_thms could (999, getgoal i, ths);

(*For inspecting earlier levels of the backward proof*)
fun chop_level n (pair,pairs) = 
  let val level = length pairs
  in  if n<0 andalso ~n <= level
      then  List.drop (pair::pairs, ~n) 
      else if 0<=n andalso n<= level
      then  List.drop (pair::pairs, level - n) 
      else  error ("Level number must lie between 0 and " ^ 
		   string_of_int level)
  end;

(*Print the given level of the proof; prlev ~1 prints previous level*)
fun prlev n = (enable_pr (); apply_fun (print_top o pop o (chop_level n)));
fun pr () = (enable_pr (); apply_fun print_top);

(*Set goals_limit and print again*)
fun prlim n = (goals_limit:=n; pr());

(** the goal.... commands
    Read main goal.  Set global variables curr_prems, curr_mkresult. 
    Initial subgoal and premises are rewritten using rths. **)

(*Version taking the goal as a cterm; if you have a term t and theory thy, use
    goalw_cterm rths (cterm_of (Theory.sign_of thy) t);      *)
fun agoalw_cterm atomic rths chorn = 
  let val (prems, st0, mkresult) = prepare_proof atomic rths chorn
  in  undo_list := [];
      setstate [ (st0, Seq.empty) ];  
      curr_prems := prems;
      curr_mkresult := mkresult;
      prems
  end;

val goalw_cterm = agoalw_cterm false;

(*Version taking the goal as a string*)
fun agoalw atomic thy rths agoal = 
    agoalw_cterm atomic rths (read_cterm(Theory.sign_of thy)(agoal,propT))
    handle ERROR => error (*from type_assign, etc via prepare_proof*)
	("The error(s) above occurred for " ^ quote agoal);

val goalw = agoalw false;

(*String version with no meta-rewrite-rules*)
fun agoal atomic thy = agoalw atomic thy [];
val goal = agoal false;

(*now the versions that wrap the goal up in `Goal' to make it atomic*)
val atomic_goalw = agoalw true;
val atomic_goal = agoal true;

(*implicit context versions*)
fun Goal s = atomic_goal (Context.the_context ()) s;
fun Goalw thms s = atomic_goalw (Context.the_context ()) thms s;


(*Proof step "by" the given tactic -- apply tactic to the proof state*)
fun by_com tac ((th,ths), pairs) : gstack =
  (case  Seq.pull(tac th)  of
     None      => error"by: tactic failed"
   | Some(th2,ths2) => 
       (if eq_thm(th,th2) 
	  then warning "Warning: same as previous level"
	  else if eq_thm_sg(th,th2) then ()
	  else warning ("Warning: signature of proof state has changed" ^
		       sign_error (#sign(rep_thm th), #sign(rep_thm th2)));
       ((th2,ths2)::(th,ths)::pairs)));

fun by tac = cond_timeit (!Library.timing) 
    (fn() => make_command (by_com tac));

(* byev[tac1,...,tacn] applies tac1 THEN ... THEN tacn.
   Good for debugging proofs involving prove_goal.*)
val byev = by o EVERY;


(*Backtracking means find an alternative result from a tactic.
  If none at this level, try earlier levels*)
fun backtrack [] = error"back: no alternatives"
  | backtrack ((th,thstr) :: pairs) =
     (case Seq.pull thstr of
	  None      => (writeln"Going back a level..."; backtrack pairs)
	| Some(th2,thstr2) =>  
	   (if eq_thm(th,th2) 
	      then warning "Warning: same as previous choice at this level"
	      else if eq_thm_sg(th,th2) then ()
	      else warning "Warning: signature of proof state has changed";
	    (th2,thstr2)::pairs));

fun back() = setstate (backtrack (getstate()));

(*Chop back to previous level of the proof*)
fun choplev n = make_command (chop_level n);

(*Chopping back the goal stack*)
fun chop () = make_command (fn (_,pairs) => pairs);

(*Restore the previous proof state;  discard current state. *)
fun undo() = case !undo_list of
      [] => error"No proof state"
    | [_] => error"Already at initial state"
    | _::newundo =>  (undo_list := newundo;  pr()) ;


(*** Managing the proof stack ***)

fun save_proof() = Proof(!undo_list, !curr_prems, !curr_mkresult);

fun restore_proof(Proof(ul,prems,mk)) =
 (undo_list:= ul;  curr_prems:= prems;  curr_mkresult := mk;  prems);


fun top_proof() = case !proofstack of
	[] => error("Stack of proof attempts is empty!")
    | p::ps => (p,ps);

(*  push a copy of the current proof state on to the stack *)
fun push_proof() = (proofstack := (save_proof() :: !proofstack));

(* discard the top proof state of the stack *)
fun pop_proof() = 
  let val (p,ps) = top_proof()
      val prems = restore_proof p
  in proofstack := ps;  pr();  prems end;

(* rotate the stack so that the top element goes to the bottom *)
fun rotate_proof() = let val (p,ps) = top_proof()
		    in proofstack := ps@[save_proof()];
		       restore_proof p;
		       pr();
		       !curr_prems
		    end;


(** Shortcuts for commonly-used tactics **)

fun bws rls = by (rewrite_goals_tac rls);
fun bw rl = bws [rl];

fun brs rls i = by (resolve_tac rls i);
fun br rl = brs [rl];

fun bes rls i = by (eresolve_tac rls i);
fun be rl = bes [rl];

fun bds rls i = by (dresolve_tac rls i);
fun bd rl = bds [rl];

fun ba i = by (assume_tac i);

fun ren str i = by (rename_tac str i);

(** Shortcuts to work on the first applicable subgoal **)

fun frs rls = by (FIRSTGOAL (trace_goalno_tac (resolve_tac rls)));
fun fr rl = frs [rl];

fun fes rls = by (FIRSTGOAL (trace_goalno_tac (eresolve_tac rls)));
fun fe rl = fes [rl];

fun fds rls = by (FIRSTGOAL (trace_goalno_tac (dresolve_tac rls)));
fun fd rl = fds [rl];

fun fa() = by (FIRSTGOAL (trace_goalno_tac assume_tac));

(** Reading and printing terms wrt the current theory **)

fun top_sg() = #sign(rep_thm(topthm()));

fun read s = term_of (read_cterm (top_sg()) (s, TypeInfer.logicT));

(*Print a term under the current signature of the proof state*)
fun prin t = writeln (Sign.string_of_term (top_sg()) t);

fun printyp T = writeln (Sign.string_of_typ (top_sg()) T);

fun pprint_term t = Sign.pprint_term (top_sg()) t;

fun pprint_typ T = Sign.pprint_typ (top_sg()) T;


(*Prints exceptions nicely at top level; 
  raises the exception in order to have a polymorphic type!*)
fun print_exn e = (print_sign_exn_unit (top_sg()) e;  raise e);



(** theorem database operations **)

(* storing *)

fun bind_thm (name, thm) = ThmDatabase.ml_store_thm (name, standard thm);
fun bind_thms (name, thms) = ThmDatabase.ml_store_thms (name, map standard thms);

fun qed name = ThmDatabase.ml_store_thm (name, result ());
fun qed_goal name thy goal tacsf = ThmDatabase.ml_store_thm (name, prove_goal thy goal tacsf);
fun qed_goalw name thy rews goal tacsf =
  ThmDatabase.ml_store_thm (name, prove_goalw thy rews goal tacsf);
fun qed_spec_mp name =
  ThmDatabase.ml_store_thm (name, ObjectLogic.rulify_no_asm (result ()));
fun qed_goal_spec_mp name thy s p =
  bind_thm (name, ObjectLogic.rulify_no_asm (prove_goal thy s p));
fun qed_goalw_spec_mp name thy defs s p =
  bind_thm (name, ObjectLogic.rulify_no_asm (prove_goalw thy defs s p));

fun no_qed () = ();


(* retrieval *)

fun theory_of_goal () = ThyInfo.theory_of_sign (Thm.sign_of_thm (topthm ()));

fun thms_containing raw_consts =
  let
    val thy = theory_of_goal ();
    val consts = map (Sign.intern_const (Theory.sign_of thy)) raw_consts;
  in
    (case filter (is_none o Sign.const_type (Theory.sign_of thy)) consts of
      [] => ()
    | cs => error ("thms_containing: undeclared consts " ^ commas_quote cs));
    PureThy.thms_containing thy (consts, [])
    |> map #2 |> flat
    |> map (fn th => (Thm.name_of_thm th, th))
  end;

(*top_const: main constant, ignoring Trueprop*)
fun top_const (_ $ t) = (case head_of t of Const (c, _) => Some c | _ => None)
  | top_const _ = None;

val intro_const = top_const o concl_of;
fun elim_const thm = case prems_of thm of [] => None | p::_ => top_const p;

fun index_intros c = thms_containing [c] |> filter (fn (_, thm) => intro_const thm = Some c);
fun index_elims c = thms_containing [c] |> filter (fn (_, thm) => elim_const thm = Some c);

(*assume that parameters have unique names; reverse them for substitution*)
fun goal_params i =
  let val gi = getgoal i
      val rfrees = rev(map Free (Logic.strip_params gi))
  in (gi,rfrees) end;

fun concl_of_goal i =
  let val (gi,rfrees) = goal_params i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(rfrees,B) end;

fun prems_of_goal i =
  let val (gi,rfrees) = goal_params i
      val As = Logic.strip_assums_hyp gi
  in map (fn A => subst_bounds(rfrees,A)) As end;

(*returns all those named_thms whose subterm extracted by extract can be
  instantiated to obj; the list is sorted according to the number of premises
  and the size of the required substitution.*)
fun select_match(obj, signobj, named_thms, extract) =
  let fun matches(prop, tsig) =
            case extract prop of
              None => false
            | Some pat => Pattern.matches tsig (pat, obj);

      fun substsize(prop, tsig) =
            let val Some pat = extract prop
                val (_,subst) = Pattern.match tsig (pat,obj)
            in foldl op+
                (0, map (fn (_,t) => size_of_term t) subst)
            end

      fun thm_ord ((p0,s0,_),(p1,s1,_)) =
            prod_ord (int_ord o pairself (fn 0 => 0 | x => 1)) int_ord ((p0,s0),(p1,s1));

      fun select((p as (_,thm))::named_thms, sels) =
            let val {prop, sign, ...} = rep_thm thm
            in select(named_thms,
                      if Sign.subsig(sign, signobj) andalso
                         matches(prop,#tsig(Sign.rep_sg signobj))
                      then
                        (nprems_of thm,substsize(prop,#tsig(Sign.rep_sg signobj)),p)::sels
                      else sels)
            end
        | select([],sels) = sels

  in map (fn (_,_,t) => t) (sort thm_ord (select(named_thms, []))) end;

fun find_matching(prop,sign,index,extract) =
  (case top_const prop of
     Some c => select_match(prop,sign,index c,extract)
   | _      => []);

fun find_intros(prop,sign) =
  find_matching(prop,sign,index_intros,Some o Logic.strip_imp_concl);

fun find_elims sign prop =
  let fun major prop = case Logic.strip_imp_prems prop of
                         [] => None | p::_ => Some p
  in find_matching(prop,sign,index_elims,major) end;

fun findI i = find_intros(concl_of_goal i,#sign(rep_thm(topthm())));

fun findEs i =
  let fun eq_nth((n1,th1),(n2,th2)) = n1=n2 andalso eq_thm(th1,th2);
      val sign = #sign(rep_thm(topthm()))
      val thmss = map (find_elims sign) (prems_of_goal i)
  in foldl (gen_union eq_nth) ([],thmss) end;

fun findE i j =
  let val sign = #sign(rep_thm(topthm()))
  in find_elims sign (nth_elem(j-1, prems_of_goal i)) end;

end;

structure BasicGoals: BASIC_GOALS = Goals;
open BasicGoals;
