(*  Title:      Pure/sign.ML
    Author:     Lawrence C Paulson and Markus Wenzel

Logical signature content: naming conventions, concrete syntax, type
signature, polymorphic constants.
*)

signature SIGN =
sig
  val rep_sg: theory ->
   {naming: NameSpace.naming,
    syn: Syntax.syntax,
    tsig: Type.tsig,
    consts: Consts.T}
  val naming_of: theory -> NameSpace.naming
  val full_name: theory -> binding -> string
  val base_name: string -> bstring
  val full_bname: theory -> bstring -> string
  val full_bname_path: theory -> string -> bstring -> string
  val syn_of: theory -> Syntax.syntax
  val tsig_of: theory -> Type.tsig
  val classes_of: theory -> Sorts.algebra
  val all_classes: theory -> class list
  val super_classes: theory -> class -> class list
  val minimize_sort: theory -> sort -> sort
  val complete_sort: theory -> sort -> sort
  val defaultS: theory -> sort
  val subsort: theory -> sort * sort -> bool
  val of_sort: theory -> typ * sort -> bool
  val witness_sorts: theory -> sort list -> sort list -> (typ * sort) list
  val is_logtype: theory -> string -> bool
  val typ_instance: theory -> typ * typ -> bool
  val typ_equiv: theory -> typ * typ -> bool
  val typ_match: theory -> typ * typ -> Type.tyenv -> Type.tyenv
  val typ_unify: theory -> typ * typ -> Type.tyenv * int -> Type.tyenv * int
  val consts_of: theory -> Consts.T
  val the_const_constraint: theory -> string -> typ
  val const_type: theory -> string -> typ option
  val the_const_type: theory -> string -> typ
  val declared_tyname: theory -> string -> bool
  val declared_const: theory -> string -> bool
  val const_monomorphic: theory -> string -> bool
  val const_syntax_name: theory -> string -> string
  val const_typargs: theory -> string * typ -> typ list
  val const_instance: theory -> string * typ list -> typ
  val mk_const: theory -> string * typ list -> term
  val class_space: theory -> NameSpace.T
  val type_space: theory -> NameSpace.T
  val const_space: theory -> NameSpace.T
  val intern_class: theory -> xstring -> string
  val extern_class: theory -> string -> xstring
  val intern_type: theory -> xstring -> string
  val extern_type: theory -> string -> xstring
  val intern_const: theory -> xstring -> string
  val extern_const: theory -> string -> xstring
  val intern_sort: theory -> sort -> sort
  val extern_sort: theory -> sort -> sort
  val intern_typ: theory -> typ -> typ
  val extern_typ: theory -> typ -> typ
  val intern_term: theory -> term -> term
  val extern_term: (string -> xstring) -> theory -> term -> term
  val intern_tycons: theory -> typ -> typ
  val arity_number: theory -> string -> int
  val arity_sorts: theory -> string -> sort -> sort list
  val certify_class: theory -> class -> class
  val certify_sort: theory -> sort -> sort
  val certify_typ: theory -> typ -> typ
  val certify_typ_mode: Type.mode -> theory -> typ -> typ
  val certify': bool -> Pretty.pp -> bool -> Consts.T -> theory -> term -> term * typ * int
  val certify_term: theory -> term -> term * typ * int
  val certify_prop: theory -> term -> term * typ * int
  val cert_term: theory -> term -> term
  val cert_prop: theory -> term -> term
  val no_frees: Pretty.pp -> term -> term
  val no_vars: Pretty.pp -> term -> term
  val cert_def: Proof.context -> term -> (string * typ) * term
  val read_class: theory -> xstring -> class
  val read_arity: theory -> xstring * string list * string -> arity
  val cert_arity: theory -> arity -> arity
  val add_defsort: string -> theory -> theory
  val add_defsort_i: sort -> theory -> theory
  val add_types: (bstring * int * mixfix) list -> theory -> theory
  val add_nonterminals: bstring list -> theory -> theory
  val add_tyabbrs: (bstring * string list * string * mixfix) list -> theory -> theory
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list -> theory -> theory
  val add_syntax: (bstring * string * mixfix) list -> theory -> theory
  val add_syntax_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_modesyntax: Syntax.mode -> (bstring * string * mixfix) list -> theory -> theory
  val add_modesyntax_i: Syntax.mode -> (bstring * typ * mixfix) list -> theory -> theory
  val del_modesyntax: Syntax.mode -> (bstring * string * mixfix) list -> theory -> theory
  val del_modesyntax_i: Syntax.mode -> (bstring * typ * mixfix) list -> theory -> theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> theory -> theory
  val declare_const: Properties.T -> (binding * typ) * mixfix -> theory -> term * theory
  val add_consts: (bstring * string * mixfix) list -> theory -> theory
  val add_consts_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_abbrev: string -> Properties.T -> binding * term -> theory -> (term * term) * theory
  val revert_abbrev: string -> string -> theory -> theory
  val add_const_constraint: string * typ option -> theory -> theory
  val primitive_class: string * class list -> theory -> theory
  val primitive_classrel: class * class -> theory -> theory
  val primitive_arity: arity -> theory -> theory
  val add_trfuns:
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (ast list -> ast)) list -> theory -> theory
  val add_trfunsT:
    (string * (bool -> typ -> term list -> term)) list -> theory -> theory
  val add_advanced_trfuns:
    (string * (Proof.context -> ast list -> ast)) list *
    (string * (Proof.context -> term list -> term)) list *
    (string * (Proof.context -> term list -> term)) list *
    (string * (Proof.context -> ast list -> ast)) list -> theory -> theory
  val add_advanced_trfunsT:
    (string * (Proof.context -> bool -> typ -> term list -> term)) list -> theory -> theory
  val add_tokentrfuns:
    (string * string * (Proof.context -> string -> Pretty.T)) list -> theory -> theory
  val add_mode_tokentrfuns: string -> (string * (Proof.context -> string -> Pretty.T)) list
    -> theory -> theory
  val add_trrules: (xstring * string) Syntax.trrule list -> theory -> theory
  val del_trrules: (xstring * string) Syntax.trrule list -> theory -> theory
  val add_trrules_i: ast Syntax.trrule list -> theory -> theory
  val del_trrules_i: ast Syntax.trrule list -> theory -> theory
  val add_path: string -> theory -> theory
  val parent_path: theory -> theory
  val root_path: theory -> theory
  val absolute_path: theory -> theory
  val local_path: theory -> theory
  val no_base_names: theory -> theory
  val qualified_names: theory -> theory
  val sticky_prefix: string -> theory -> theory
  val restore_naming: theory -> theory -> theory
  val hide_class: bool -> string -> theory -> theory
  val hide_type: bool -> string -> theory -> theory
  val hide_const: bool -> string -> theory -> theory
end

structure Sign: SIGN =
struct

(** datatype sign **)

datatype sign = Sign of
 {naming: NameSpace.naming,     (*common naming conventions*)
  syn: Syntax.syntax,           (*concrete syntax for terms, types, sorts*)
  tsig: Type.tsig,              (*order-sorted signature of types*)
  consts: Consts.T};            (*polymorphic constants*)

fun make_sign (naming, syn, tsig, consts) =
  Sign {naming = naming, syn = syn, tsig = tsig, consts = consts};

structure SignData = TheoryDataFun
(
  type T = sign;
  val copy = I;
  fun extend (Sign {syn, tsig, consts, ...}) =
    make_sign (NameSpace.default_naming, syn, tsig, consts);

  val empty =
    make_sign (NameSpace.default_naming, Syntax.basic_syn, Type.empty_tsig, Consts.empty);

  fun merge pp (sign1, sign2) =
    let
      val Sign {naming = _, syn = syn1, tsig = tsig1, consts = consts1} = sign1;
      val Sign {naming = _, syn = syn2, tsig = tsig2, consts = consts2} = sign2;

      val naming = NameSpace.default_naming;
      val syn = Syntax.merge_syntaxes syn1 syn2;
      val tsig = Type.merge_tsigs pp (tsig1, tsig2);
      val consts = Consts.merge (consts1, consts2);
    in make_sign (naming, syn, tsig, consts) end;
);

fun rep_sg thy = SignData.get thy |> (fn Sign args => args);

fun map_sign f = SignData.map (fn Sign {naming, syn, tsig, consts} =>
  make_sign (f (naming, syn, tsig, consts)));

fun map_naming f = map_sign (fn (naming, syn, tsig, consts) => (f naming, syn, tsig, consts));
fun map_syn f = map_sign (fn (naming, syn, tsig, consts) => (naming, f syn, tsig, consts));
fun map_tsig f = map_sign (fn (naming, syn, tsig, consts) => (naming, syn, f tsig, consts));
fun map_consts f = map_sign (fn (naming, syn, tsig, consts) => (naming, syn, tsig, f consts));


(* naming *)

val naming_of = #naming o rep_sg;
val base_name = NameSpace.base;

val full_name = NameSpace.full_name o naming_of;
fun full_bname thy = NameSpace.full_name (naming_of thy) o Binding.name;
fun full_bname_path thy elems =
  NameSpace.full_name (NameSpace.add_path elems (naming_of thy)) o Binding.name;


(* syntax *)

val syn_of = #syn o rep_sg;


(* type signature *)

val tsig_of = #tsig o rep_sg;

val classes_of = #2 o #classes o Type.rep_tsig o tsig_of;
val all_classes = Sorts.all_classes o classes_of;
val super_classes = Sorts.super_classes o classes_of;
val minimize_sort = Sorts.minimize_sort o classes_of;
val complete_sort = Sorts.complete_sort o classes_of;

val defaultS = Type.defaultS o tsig_of;
val subsort = Type.subsort o tsig_of;
val of_sort = Type.of_sort o tsig_of;
val witness_sorts = Type.witness_sorts o tsig_of;
val is_logtype = member (op =) o Type.logical_types o tsig_of;

val typ_instance = Type.typ_instance o tsig_of;
fun typ_equiv thy (T, U) = typ_instance thy (T, U) andalso typ_instance thy (U, T);
val typ_match = Type.typ_match o tsig_of;
val typ_unify = Type.unify o tsig_of;


(* polymorphic constants *)

val consts_of = #consts o rep_sg;
val the_const_constraint = Consts.the_constraint o consts_of;
val the_const_type = Consts.the_type o consts_of;
val const_type = try o the_const_type;
val const_monomorphic = Consts.is_monomorphic o consts_of;
val const_syntax_name = Consts.syntax_name o consts_of;
val const_typargs = Consts.typargs o consts_of;
val const_instance = Consts.instance o consts_of;

fun mk_const thy (c, Ts) = Const (c, const_instance thy (c, Ts));

val declared_tyname = Symtab.defined o #2 o #types o Type.rep_tsig o tsig_of;
val declared_const = can o the_const_constraint;



(** intern / extern names **)

val class_space = #1 o #classes o Type.rep_tsig o tsig_of;
val type_space = #1 o #types o Type.rep_tsig o tsig_of;
val const_space = Consts.space_of o consts_of;

val intern_class = NameSpace.intern o class_space;
val extern_class = NameSpace.extern o class_space;
val intern_type = NameSpace.intern o type_space;
val extern_type = NameSpace.extern o type_space;
val intern_const = NameSpace.intern o const_space;
val extern_const = NameSpace.extern o const_space;

val intern_sort = map o intern_class;
val extern_sort = map o extern_class;

local

fun map_typ f g (Type (c, Ts)) = Type (g c, map (map_typ f g) Ts)
  | map_typ f _ (TFree (x, S)) = TFree (x, map f S)
  | map_typ f _ (TVar (xi, S)) = TVar (xi, map f S);

fun map_term f g h (Const (c, T)) = Const (h c, map_typ f g T)
  | map_term f g _ (Free (x, T)) = Free (x, map_typ f g T)
  | map_term f g _ (Var (xi, T)) = Var (xi, map_typ f g T)
  | map_term _ _ _ (t as Bound _) = t
  | map_term f g h (Abs (x, T, t)) = Abs (x, map_typ f g T, map_term f g h t)
  | map_term f g h (t $ u) = map_term f g h t $ map_term f g h u;

val add_classesT = Term.fold_atyps
  (fn TFree (_, S) => fold (insert (op =)) S
    | TVar (_, S) => fold (insert (op =)) S
    | _ => I);

fun add_tyconsT (Type (c, Ts)) = insert (op =) c #> fold add_tyconsT Ts
  | add_tyconsT _ = I;

val add_consts = Term.fold_aterms (fn Const (c, _) => insert (op =) c | _ => I);

fun mapping add_names f t =
  let
    fun f' (x: string) = let val y = f x in if x = y then NONE else SOME (x, y) end;
    val tab = map_filter f' (add_names t []);
    fun get x = the_default x (AList.lookup (op =) tab x);
  in get end;

fun typ_mapping f g thy T =
  T |> map_typ
    (mapping add_classesT (f thy) T)
    (mapping add_tyconsT (g thy) T);

fun term_mapping f g h thy t =
  t |> map_term
    (mapping (Term.fold_types add_classesT) (f thy) t)
    (mapping (Term.fold_types add_tyconsT) (g thy) t)
    (mapping add_consts (h thy) t);

in

val intern_typ = typ_mapping intern_class intern_type;
val extern_typ = typ_mapping extern_class extern_type;
val intern_term = term_mapping intern_class intern_type intern_const;
fun extern_term h = term_mapping extern_class extern_type (K h);
val intern_tycons = typ_mapping (K I) intern_type;

end;



(** certify entities **)    (*exception TYPE*)

(* certify wrt. type signature *)

val arity_number = Type.arity_number o tsig_of;
fun arity_sorts thy = Type.arity_sorts (Syntax.pp_global thy) (tsig_of thy);

val certify_class         = Type.cert_class o tsig_of;
val certify_sort          = Type.cert_sort o tsig_of;
val certify_typ           = Type.cert_typ o tsig_of;
fun certify_typ_mode mode = Type.cert_typ_mode mode o tsig_of;


(* certify term/prop *)

local

fun type_check pp tm =
  let
    fun err_appl why bs t T u U =
      let
        val xs = map Free bs;           (*we do not rename here*)
        val t' = subst_bounds (xs, t);
        val u' = subst_bounds (xs, u);
        val msg = cat_lines
          (TypeInfer.appl_error (Syntax.pp_show_brackets pp) why t' T u' U);
      in raise TYPE (msg, [T, U], [t', u']) end;

    fun typ_of (_, Const (_, T)) = T
      | typ_of (_, Free  (_, T)) = T
      | typ_of (_, Var (_, T)) = T
      | typ_of (bs, Bound i) = snd (nth bs i handle Subscript =>
          raise TYPE ("Loose bound variable: B." ^ string_of_int i, [], [Bound i]))
      | typ_of (bs, Abs (x, T, body)) = T --> typ_of ((x, T) :: bs, body)
      | typ_of (bs, t $ u) =
          let val T = typ_of (bs, t) and U = typ_of (bs, u) in
            (case T of
              Type ("fun", [T1, T2]) =>
                if T1 = U then T2 else err_appl "Incompatible operand type" bs t T u U
            | _ => err_appl "Operator not of function type" bs t T u U)
          end;
  in typ_of ([], tm) end;

fun err msg = raise TYPE (msg, [], []);

fun check_vars (t $ u) = (check_vars t; check_vars u)
  | check_vars (Abs (_, _, t)) = check_vars t
  | check_vars (Free (x, _)) =
      if NameSpace.is_qualified x then err ("Malformed variable: " ^ quote x) else ()
  | check_vars (Var (xi as (_, i), _)) =
      if i < 0 then err ("Malformed variable: " ^ quote (Term.string_of_vname xi)) else ()
  | check_vars _ = ();

in

fun certify' prop pp do_expand consts thy tm =
  let
    val _ = check_vars tm;
    val tm' = Term.map_types (certify_typ thy) tm;
    val T = type_check pp tm';
    val _ = if prop andalso T <> propT then err "Term not of type prop" else ();
    val tm'' = Consts.certify pp (tsig_of thy) do_expand consts tm';
  in (if tm = tm'' then tm else tm'', T, Term.maxidx_of_term tm'') end;

fun certify_term thy = certify' false (Syntax.pp_global thy) true (consts_of thy) thy;
fun certify_prop thy = certify' true (Syntax.pp_global thy) true (consts_of thy) thy;

fun cert_term_abbrev thy = #1 o certify' false (Syntax.pp_global thy) false (consts_of thy) thy;
val cert_term = #1 oo certify_term;
val cert_prop = #1 oo certify_prop;

end;


(* specifications *)

fun no_variables kind add addT mk mkT pp tm =
  (case (add tm [], addT tm []) of
    ([], []) => tm
  | (frees, tfrees) => error (Pretty.string_of (Pretty.block
      (Pretty.str ("Illegal " ^ kind ^ " variable(s) in term:") :: Pretty.brk 1 ::
       Pretty.commas (map (Pretty.term pp o mk) frees @ map (Pretty.typ pp o mkT) tfrees)))));

val no_frees = no_variables "free" Term.add_frees Term.add_tfrees Free TFree;
val no_vars = no_variables "schematic" Term.add_vars Term.add_tvars Var TVar;

fun cert_def ctxt tm =
  let val ((lhs, rhs), _) = tm
    |> no_vars (Syntax.pp ctxt)
    |> Logic.strip_imp_concl
    |> PrimitiveDefs.dest_def ctxt Term.is_Const (K false) (K false)
  in (Term.dest_Const (Term.head_of lhs), rhs) end
  handle TERM (msg, _) => error msg;



(** read and certify entities **)    (*exception ERROR*)

(* classes *)

fun read_class thy c = certify_class thy (intern_class thy c)
  handle TYPE (msg, _, _) => error msg;


(* type arities *)

fun prep_arity prep_tycon prep_sort thy (t, Ss, S) =
  let val arity = (prep_tycon thy t, map (prep_sort thy) Ss, prep_sort thy S)
  in Type.add_arity (Syntax.pp_global thy) arity (tsig_of thy); arity end;

val read_arity = prep_arity intern_type Syntax.read_sort_global;
val cert_arity = prep_arity (K I) certify_sort;



(** signature extension functions **)  (*exception ERROR/TYPE*)

(* add default sort *)

fun gen_add_defsort prep_sort s thy =
  thy |> map_tsig (Type.set_defsort (prep_sort thy s));

val add_defsort = gen_add_defsort Syntax.read_sort_global;
val add_defsort_i = gen_add_defsort certify_sort;


(* add type constructors *)

fun add_types types thy = thy |> map_sign (fn (naming, syn, tsig, consts) =>
  let
    val syn' = Syntax.update_type_gram types syn;
    val decls = map (fn (a, n, mx) => (Syntax.type_name a mx, n)) types;
    val tags = [(Markup.theory_nameN, Context.theory_name thy)];
    val tsig' = fold (Type.add_type naming tags) decls tsig;
  in (naming, syn', tsig', consts) end);


(* add nonterminals *)

fun add_nonterminals ns thy = thy |> map_sign (fn (naming, syn, tsig, consts) =>
  let
    val syn' = Syntax.update_consts ns syn;
    val tsig' = fold (Type.add_nonterminal naming []) ns tsig;
  in (naming, syn', tsig', consts) end);


(* add type abbreviations *)

fun gen_add_tyabbr parse_typ (a, vs, rhs, mx) thy =
  thy |> map_sign (fn (naming, syn, tsig, consts) =>
    let
      val ctxt = ProofContext.init thy;
      val syn' = Syntax.update_type_gram [(a, length vs, mx)] syn;
      val a' = Syntax.type_name a mx;
      val abbr = (a', vs, certify_typ_mode Type.mode_syntax thy (parse_typ ctxt rhs))
        handle ERROR msg => cat_error msg ("in type abbreviation " ^ quote a');
      val tsig' = Type.add_abbrev naming [] abbr tsig;
    in (naming, syn', tsig', consts) end);

val add_tyabbrs = fold (gen_add_tyabbr Syntax.parse_typ);
val add_tyabbrs_i = fold (gen_add_tyabbr (K I));


(* modify syntax *)

fun gen_syntax change_gram parse_typ mode args thy =
  let
    val ctxt = ProofContext.init thy;
    fun prep (c, T, mx) = (c, certify_typ_mode Type.mode_syntax thy (parse_typ ctxt T), mx)
      handle ERROR msg =>
        cat_error msg ("in syntax declaration " ^ quote (Syntax.const_name c mx));
  in thy |> map_syn (change_gram (is_logtype thy) mode (map prep args)) end;

fun gen_add_syntax x = gen_syntax Syntax.update_const_gram x;

val add_modesyntax = gen_add_syntax Syntax.parse_typ;
val add_modesyntax_i = gen_add_syntax (K I);
val add_syntax = add_modesyntax Syntax.mode_default;
val add_syntax_i = add_modesyntax_i Syntax.mode_default;
val del_modesyntax = gen_syntax Syntax.remove_const_gram Syntax.parse_typ;
val del_modesyntax_i = gen_syntax Syntax.remove_const_gram (K I);

fun notation add mode args thy =
  let
    val change_gram = if add then Syntax.update_const_gram else Syntax.remove_const_gram;
    fun const_syntax (Const (c, _), mx) = try (Consts.syntax (consts_of thy)) (c, mx)
      | const_syntax _ = NONE;
  in gen_syntax change_gram (K I) mode (map_filter const_syntax args) thy end;


(* add constants *)

local

fun gen_add_consts parse_typ authentic tags raw_args thy =
  let
    val ctxt = ProofContext.init thy;
    val prepT = Type.no_tvars o Term.no_dummyT o certify_typ thy o parse_typ ctxt;
    fun prep (raw_b, raw_T, raw_mx) =
      let
        val (mx_name, mx) = Syntax.const_mixfix (Binding.base_name raw_b) raw_mx;
        val b = Binding.map_base (K mx_name) raw_b;
        val c = full_name thy b;
        val c_syn = if authentic then Syntax.constN ^ c else Binding.base_name b;
        val T = (prepT raw_T handle TYPE (msg, _, _) => error msg) handle ERROR msg =>
          cat_error msg ("in declaration of constant " ^ quote (Binding.display b));
        val T' = Logic.varifyT T;
      in ((b, T'), (c_syn, T', mx), Const (c, T)) end;
    val args = map prep raw_args;
    val tags' = tags |> Properties.put (Markup.theory_nameN, Context.theory_name thy);
  in
    thy
    |> map_consts (fold (Consts.declare authentic (naming_of thy) tags' o #1) args)
    |> add_syntax_i (map #2 args)
    |> pair (map #3 args)
  end;

fun bindify (name, T, mx) = (Binding.name name, T, mx);

in

fun add_consts args = snd o gen_add_consts Syntax.parse_typ false [] (map bindify args);
fun add_consts_i args = snd o gen_add_consts (K I) false [] (map bindify args);

fun declare_const tags ((b, T), mx) thy =
  let
    val pos = Binding.pos_of b;
    val tags' = Position.default_properties pos tags;
    val ([const as Const (c, _)], thy') = gen_add_consts (K I) true tags' [(b, T, mx)] thy;
    val _ = Position.report (Markup.const_decl c) pos;
  in (const, thy') end;

end;


(* abbreviations *)

fun add_abbrev mode tags (b, raw_t) thy =
  let
    val pp = Syntax.pp_global thy;
    val prep_tm = no_frees pp o Term.no_dummy_patterns o cert_term_abbrev thy;
    val t = (prep_tm raw_t handle TYPE (msg, _, _) => error msg | TERM (msg, _) => error msg)
      handle ERROR msg => cat_error msg ("in constant abbreviation " ^ quote (Binding.display b));
    val (res, consts') = consts_of thy
      |> Consts.abbreviate pp (tsig_of thy) (naming_of thy) mode tags (b, t);
  in (res, thy |> map_consts (K consts')) end;

fun revert_abbrev mode c = map_consts (Consts.revert_abbrev mode c);


(* add constraints *)

fun add_const_constraint (c, opt_T) thy =
  let
    fun prepT raw_T =
      let val T = Logic.varifyT (Type.no_tvars (Term.no_dummyT (certify_typ thy raw_T)))
      in cert_term thy (Const (c, T)); T end
      handle TYPE (msg, _, _) => error msg;
  in thy |> map_consts (Consts.constrain (c, Option.map prepT opt_T)) end;


(* primitive classes and arities *)

fun primitive_class (bclass, classes) thy =
  thy |> map_sign (fn (naming, syn, tsig, consts) =>
    let
      val syn' = Syntax.update_consts [bclass] syn;
      val tsig' = Type.add_class (Syntax.pp_global thy) naming (bclass, classes) tsig;
    in (naming, syn', tsig', consts) end)
  |> add_consts_i [(Logic.const_of_class bclass, Term.a_itselfT --> propT, NoSyn)];

fun primitive_classrel arg thy = thy |> map_tsig (Type.add_classrel (Syntax.pp_global thy) arg);
fun primitive_arity arg thy = thy |> map_tsig (Type.add_arity (Syntax.pp_global thy) arg);


(* add translation functions *)

local

fun mk trs = map Syntax.mk_trfun trs;

fun gen_add_trfuns ext non_typed (atrs, trs, tr's, atr's) =
  map_syn (ext (mk atrs, mk trs, mk (map (apsnd non_typed) tr's), mk atr's));

fun gen_add_trfunsT ext tr's = map_syn (ext ([], [], mk tr's, []));

in

val add_trfuns = gen_add_trfuns Syntax.update_trfuns Syntax.non_typed_tr';
val add_trfunsT = gen_add_trfunsT Syntax.update_trfuns;
val add_advanced_trfuns = gen_add_trfuns Syntax.update_advanced_trfuns Syntax.non_typed_tr'';
val add_advanced_trfunsT = gen_add_trfunsT Syntax.update_advanced_trfuns;

end;

val add_tokentrfuns = map_syn o Syntax.extend_tokentrfuns;
fun add_mode_tokentrfuns m = add_tokentrfuns o map (fn (s, f) => (m, s, f));


(* translation rules *)

fun gen_trrules f args thy = thy |> map_syn (fn syn =>
  let val rules = map (Syntax.map_trrule (apfst (intern_type thy))) args
  in f (ProofContext.init thy) (is_logtype thy) syn rules syn end);

val add_trrules = gen_trrules Syntax.update_trrules;
val del_trrules = gen_trrules Syntax.remove_trrules;
val add_trrules_i = map_syn o Syntax.update_trrules_i;
val del_trrules_i = map_syn o Syntax.remove_trrules_i;


(* naming *)

val add_path        = map_naming o NameSpace.add_path;
val no_base_names   = map_naming NameSpace.no_base_names;
val qualified_names = map_naming NameSpace.qualified_names;
val sticky_prefix   = map_naming o NameSpace.sticky_prefix;
val restore_naming  = map_naming o K o naming_of;

val parent_path   = add_path "..";
val root_path     = add_path "/";
val absolute_path = add_path "//";

fun local_path thy = thy |> root_path |> add_path (Context.theory_name thy);


(* hide names *)

val hide_class = map_tsig oo Type.hide_class;
val hide_type = map_tsig oo Type.hide_type;
val hide_const = map_consts oo Consts.hide;

end;
