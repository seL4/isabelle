(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

Logical signature content: naming conventions, concrete syntax, type
signature, polymorphic constants.
*)

signature SIGN_THEORY =
sig
  val add_defsort: string -> theory -> theory
  val add_defsort_i: sort -> theory -> theory
  val add_types: (bstring * int * mixfix) list -> theory -> theory
  val add_typedecls: (bstring * string list * mixfix) list -> theory -> theory
  val add_nonterminals: bstring list -> theory -> theory
  val add_tyabbrs: (bstring * string list * string * mixfix) list -> theory -> theory
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list -> theory -> theory
  val add_arities: (xstring * string list * string) list -> theory -> theory
  val add_arities_i: (string * sort list * sort) list -> theory -> theory
  val add_syntax: (bstring * string * mixfix) list -> theory -> theory
  val add_syntax_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_modesyntax: (string * bool) -> (bstring * string * mixfix) list -> theory -> theory
  val add_modesyntax_i: (string * bool) -> (bstring * typ * mixfix) list -> theory -> theory
  val del_modesyntax: (string * bool) -> (bstring * string * mixfix) list -> theory -> theory
  val del_modesyntax_i: (string * bool) -> (bstring * typ * mixfix) list -> theory -> theory
  val add_consts: (bstring * string * mixfix) list -> theory -> theory
  val add_consts_i: (bstring * typ * mixfix) list -> theory -> theory
  val add_const_constraint: xstring * string -> theory -> theory
  val add_const_constraint_i: string * typ -> theory -> theory
  val add_classes: (bstring * xstring list) list -> theory -> theory
  val add_classes_i: (bstring * class list) list -> theory -> theory
  val add_classrel: (xstring * xstring) list -> theory -> theory
  val add_classrel_i: (class * class) list -> theory -> theory
  val add_trfuns:
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (ast list -> ast)) list -> theory -> theory
  val add_trfunsT:
    (string * (bool -> typ -> term list -> term)) list -> theory -> theory
  val add_advanced_trfuns:
    (string * (theory -> ast list -> ast)) list *
    (string * (theory -> term list -> term)) list *
    (string * (theory -> term list -> term)) list *
    (string * (theory -> ast list -> ast)) list -> theory -> theory
  val add_advanced_trfunsT:
    (string * (theory -> bool -> typ -> term list -> term)) list -> theory -> theory
  val add_tokentrfuns:
    (string * string * (string -> string * real)) list -> theory -> theory
  val add_mode_tokentrfuns: string -> (string * (string -> string * real)) list
    -> theory -> theory
  val parse_ast_translation: bool * string -> theory -> theory
  val parse_translation: bool * string -> theory -> theory
  val print_translation: bool * string -> theory -> theory
  val typed_print_translation: bool * string -> theory -> theory
  val print_ast_translation: bool * string -> theory -> theory
  val token_translation: string -> theory -> theory
  val add_trrules: (xstring * string) Syntax.trrule list -> theory -> theory
  val add_trrules_i: ast Syntax.trrule list -> theory -> theory
  val add_path: string -> theory -> theory
  val parent_path: theory -> theory
  val root_path: theory -> theory
  val absolute_path: theory -> theory
  val local_path: theory -> theory
  val qualified_names: theory -> theory
  val no_base_names: theory -> theory
  val custom_accesses: (string list -> string list list) -> theory -> theory
  val set_policy: (string -> bstring -> string) * (string list -> string list list) ->
    theory -> theory
  val restore_naming: theory -> theory -> theory
  val hide_classes: bool -> xstring list -> theory -> theory
  val hide_classes_i: bool -> string list -> theory -> theory
  val hide_types: bool -> xstring list -> theory -> theory
  val hide_types_i: bool -> string list -> theory -> theory
  val hide_consts: bool -> xstring list -> theory -> theory
  val hide_consts_i: bool -> string list -> theory -> theory
  val hide_names: bool -> string * xstring list -> theory -> theory
  val hide_names_i: bool -> string * string list -> theory -> theory
end

signature SIGN =
sig
  type sg    (*obsolete*)
  val init_data: theory -> theory
  val rep_sg: theory ->
   {naming: NameSpace.naming,
    syn: Syntax.syntax,
    tsig: Type.tsig,
    consts: Consts.T}
  val naming_of: theory -> NameSpace.naming
  val base_name: string -> bstring
  val full_name: theory -> bstring -> string
  val full_name_path: theory -> string -> bstring -> string
  val declare_name: theory -> string -> NameSpace.T -> NameSpace.T
  val syn_of: theory -> Syntax.syntax
  val tsig_of: theory -> Type.tsig
  val classes_of: theory -> Sorts.classes
  val classes_arities_of: theory -> Sorts.classes * Sorts.arities
  val classes: theory -> class list
  val defaultS: theory -> sort
  val subsort: theory -> sort * sort -> bool
  val of_sort: theory -> typ * sort -> bool
  val witness_sorts: theory -> sort list -> sort list -> (typ * sort) list
  val universal_witness: theory -> (typ * sort) option
  val all_sorts_nonempty: theory -> bool
  val typ_instance: theory -> typ * typ -> bool
  val typ_match: theory -> typ * typ -> Type.tyenv -> Type.tyenv
  val typ_unify: theory -> typ * typ -> Type.tyenv * int -> Type.tyenv * int
  val is_logtype: theory -> string -> bool
  val const_constraint: theory -> string -> typ option
  val the_const_constraint: theory -> string -> typ
  val const_type: theory -> string -> typ option
  val the_const_type: theory -> string -> typ
  val declared_tyname: theory -> string -> bool
  val declared_const: theory -> string -> bool
  val const_monomorphic: theory -> string -> bool
  val const_typargs: theory -> string * typ -> typ list
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
  val extern_term: theory -> term -> term
  val intern_tycons: theory -> typ -> typ
  val pretty_term': Syntax.syntax -> theory -> term -> Pretty.T
  val pretty_term: theory -> term -> Pretty.T
  val pretty_typ: theory -> typ -> Pretty.T
  val pretty_sort: theory -> sort -> Pretty.T
  val pretty_classrel: theory -> class list -> Pretty.T
  val pretty_arity: theory -> arity -> Pretty.T
  val string_of_term: theory -> term -> string
  val string_of_typ: theory -> typ -> string
  val string_of_sort: theory -> sort -> string
  val string_of_classrel: theory -> class list -> string
  val string_of_arity: theory -> arity -> string
  val pprint_term: theory -> term -> pprint_args -> unit
  val pprint_typ: theory -> typ -> pprint_args -> unit
  val pp: theory -> Pretty.pp
  val certify_class: theory -> class -> class
  val certify_sort: theory -> sort -> sort
  val certify_typ: theory -> typ -> typ
  val certify_typ_syntax: theory -> typ -> typ
  val certify_typ_abbrev: theory -> typ -> typ
  val certify_term: Pretty.pp -> theory -> term -> term * typ * int
  val certify_prop: Pretty.pp -> theory -> term -> term * typ * int
  val cert_term: theory -> term -> term
  val cert_prop: theory -> term -> term
  val read_sort': Syntax.syntax -> theory -> string -> sort
  val read_sort: theory -> string -> sort
  val read_typ': Syntax.syntax -> theory * (indexname -> sort option) -> string -> typ
  val read_typ_syntax': Syntax.syntax -> theory * (indexname -> sort option) -> string -> typ
  val read_typ_abbrev': Syntax.syntax -> theory * (indexname -> sort option) -> string -> typ
  val read_typ: theory * (indexname -> sort option) -> string -> typ
  val read_typ_syntax: theory * (indexname -> sort option) -> string -> typ
  val read_typ_abbrev: theory * (indexname -> sort option) -> string -> typ
  val read_tyname: theory -> string -> typ
  val read_const: theory -> string -> term
  val infer_types_simult: Pretty.pp -> theory -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> (term list * typ) list -> term list * (indexname * typ) list
  val infer_types: Pretty.pp -> theory -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> term list * typ -> term * (indexname * typ) list
  val read_def_terms': Pretty.pp -> (string -> bool) -> Syntax.syntax ->
    theory * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ) list -> term list * (indexname * typ) list
  val read_def_terms:
    theory * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ) list -> term list * (indexname * typ) list
  val simple_read_term: theory -> typ -> string -> term
  val read_term: theory -> string -> term
  val read_prop: theory -> string -> term
  val const_of_class: class -> string
  val class_of_const: string -> class
  include SIGN_THEORY
end

structure Sign: SIGN =
struct

type sg = theory;


(** datatype sign **)

datatype sign = Sign of
 {naming: NameSpace.naming,     (*common naming conventions*)
  syn: Syntax.syntax,           (*concrete syntax for terms, types, sorts*)
  tsig: Type.tsig,              (*order-sorted signature of types*)
  consts: Consts.T};            (*polymorphic constants*)

fun make_sign (naming, syn, tsig, consts) =
  Sign {naming = naming, syn = syn, tsig = tsig, consts = consts};

structure SignData = TheoryDataFun
(struct
  val name = "Pure/sign";
  type T = sign;
  val copy = I;
  fun extend (Sign {syn, tsig, consts, ...}) =
    make_sign (NameSpace.default_naming, syn, tsig, consts);

  val empty =
    make_sign (NameSpace.default_naming, Syntax.pure_syn, Type.empty_tsig, Consts.empty);

  fun merge pp (sign1, sign2) =
    let
      val Sign {naming = _, syn = syn1, tsig = tsig1, consts = consts1} = sign1;
      val Sign {naming = _, syn = syn2, tsig = tsig2, consts = consts2} = sign2;

      val naming = NameSpace.default_naming;
      val syn = Syntax.merge_syntaxes syn1 syn2;
      val tsig = Type.merge_tsigs pp (tsig1, tsig2);
      val consts = Consts.merge (consts1, consts2);
    in make_sign (naming, syn, tsig, consts) end;

  fun print _ _ = ();
end);

val init_data = SignData.init;

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
val full_name = NameSpace.full o naming_of;
fun full_name_path thy elems = NameSpace.full (NameSpace.add_path elems (naming_of thy));
val declare_name = NameSpace.declare o naming_of;


(* syntax *)

val syn_of = #syn o rep_sg;


(* type signature *)

val tsig_of = #tsig o rep_sg;
val classes_of = snd o #classes o Type.rep_tsig o tsig_of;
fun classes_arities_of thy = (classes_of thy, #arities (Type.rep_tsig (tsig_of thy)));
val classes = Type.classes o tsig_of;
val defaultS = Type.defaultS o tsig_of;
val subsort = Type.subsort o tsig_of;
val of_sort = Type.of_sort o tsig_of;
val witness_sorts = Type.witness_sorts o tsig_of;
val universal_witness = Type.universal_witness o tsig_of;
val all_sorts_nonempty = is_some o universal_witness;
val typ_instance = Type.typ_instance o tsig_of;
val typ_match = Type.typ_match o tsig_of;
val typ_unify = Type.unify o tsig_of;
fun is_logtype thy c = c mem_string Type.logical_types (tsig_of thy);


(* polymorphic constants *)

val consts_of = #consts o rep_sg;
val the_const_constraint = Consts.constraint o consts_of;
val const_constraint = try o the_const_constraint;
val the_const_type = Consts.declaration o consts_of;
val const_type = try o the_const_type;
val const_monomorphic = Consts.monomorphic o consts_of;
val const_typargs = Consts.typargs o consts_of;

val declared_tyname = Symtab.defined o #2 o #types o Type.rep_tsig o tsig_of;
val declared_const = is_some oo const_type;



(** intern / extern names **)

val class_space = #1 o #classes o Type.rep_tsig o tsig_of;
val type_space = #1 o #types o Type.rep_tsig o tsig_of;
val const_space = Consts.space o consts_of;

val intern_class = NameSpace.intern o class_space;
val extern_class = NameSpace.extern o class_space;
val intern_type = NameSpace.intern o type_space;
val extern_type = NameSpace.extern o type_space;
val intern_const = NameSpace.intern o const_space;
val extern_const = NameSpace.extern o const_space;

val intern_sort = map o intern_class;
val extern_sort = map o extern_class;

local

fun mapping add_names f t =
  let
    fun f' x = let val y = f x in if x = y then NONE else SOME (x, y) end;
    val tab = List.mapPartial f' (add_names (t, []));
    fun get x = if_none (AList.lookup (op =) tab x) x;
  in get end;

fun typ_mapping f g thy T =
  T |> Term.map_typ
    (mapping add_typ_classes (f thy) T)
    (mapping add_typ_tycons (g thy) T);

fun term_mapping f g h thy t =
  t |> Term.map_term
    (mapping add_term_classes (f thy) t)
    (mapping add_term_tycons (g thy) t)
    (mapping add_term_consts (h thy) t);

in

val intern_typ = typ_mapping intern_class intern_type;
val extern_typ = typ_mapping extern_class extern_type;
val intern_term = term_mapping intern_class intern_type intern_const;
val extern_term = term_mapping extern_class extern_type extern_const;
val intern_tycons = typ_mapping (K I) intern_type;

end;



(** pretty printing of terms, types etc. **)

fun pretty_term' syn thy t =
  Syntax.pretty_term thy syn (Context.exists_name Context.CPureN thy) (extern_term thy t);
fun pretty_term thy t = pretty_term' (syn_of thy) thy t;
fun pretty_typ thy T = Syntax.pretty_typ thy (syn_of thy) (extern_typ thy T);
fun pretty_sort thy S = Syntax.pretty_sort thy (syn_of thy) (extern_sort thy S);

fun pretty_classrel thy cs = Pretty.block (List.concat
  (separate [Pretty.str " <", Pretty.brk 1] (map (single o pretty_sort thy o single) cs)));

fun pretty_arity thy (a, Ss, S) =
  let
    val a' = extern_type thy a;
    val dom =
      if null Ss then []
      else [Pretty.list "(" ")" (map (pretty_sort thy) Ss), Pretty.brk 1];
  in Pretty.block ([Pretty.str (a' ^ " ::"), Pretty.brk 1] @ dom @ [pretty_sort thy S]) end;

val string_of_term = Pretty.string_of oo pretty_term;
val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_sort = Pretty.string_of oo pretty_sort;
val string_of_classrel = Pretty.string_of oo pretty_classrel;
val string_of_arity = Pretty.string_of oo pretty_arity;

val pprint_term = (Pretty.pprint o Pretty.quote) oo pretty_term;
val pprint_typ = (Pretty.pprint o Pretty.quote) oo pretty_typ;

fun pp thy = Pretty.pp (pretty_term thy, pretty_typ thy, pretty_sort thy,
  pretty_classrel thy, pretty_arity thy);



(** certify entities **)    (*exception TYPE*)

(* certify wrt. type signature *)

fun certify cert = cert o tsig_of o Context.check_thy;

val certify_class      = certify Type.cert_class;
val certify_sort       = certify Type.cert_sort;
val certify_typ        = certify Type.cert_typ;
val certify_typ_syntax = certify Type.cert_typ_syntax;
val certify_typ_abbrev = certify Type.cert_typ_abbrev;


(* certify_term *)

local

(*determine and check the type of a term*)
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
      | typ_of (bs, Bound i) = snd (List.nth (bs, i) handle Subscript =>
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

in

fun certify_term pp thy tm =
  let
    val _ = Context.check_thy thy;

    val tm' = map_term_types (certify_typ thy) tm;
    val tm' = if tm = tm' then tm else tm';  (*avoid copying of already normal term*)

    fun err msg = raise TYPE (msg, [], [tm']);

    fun show_const a T = quote a ^ " :: " ^ Pretty.string_of_typ pp T;

    fun check_atoms (t $ u) = (check_atoms t; check_atoms u)
      | check_atoms (Abs (_, _, t)) = check_atoms t
      | check_atoms (Const (a, T)) =
          (case const_type thy a of
            NONE => err ("Undeclared constant " ^ show_const a T)
          | SOME U =>
              if typ_instance thy (T, U) then ()
              else err ("Illegal type for constant " ^ show_const a T))
      | check_atoms (Var ((x, i), _)) =
          if i < 0 then err ("Malformed variable: " ^ quote x) else ()
      | check_atoms _ = ();
  in
    check_atoms tm';
    (tm', type_check pp tm', maxidx_of_term tm')
  end;

end;

fun certify_prop pp thy tm =
  let val res as (tm', T, _) = certify_term pp thy tm
  in if T <> propT then raise TYPE ("Term not of type prop", [T], [tm']) else res end;

fun cert_term thy tm = #1 (certify_term (pp thy) thy tm);
fun cert_prop thy tm = #1 (certify_prop (pp thy) thy tm);



(** read and certify entities **)    (*exception ERROR*)

(* sorts *)

fun read_sort' syn thy str =
  let
    val _ = Context.check_thy thy;
    val S = intern_sort thy (Syntax.read_sort thy syn str);
  in certify_sort thy S handle TYPE (msg, _, _) => error msg end;

fun read_sort thy str = read_sort' (syn_of thy) thy str;


(* types *)

local

fun gen_read_typ' cert syn (thy, def_sort) str =
  let
    val _ = Context.check_thy thy;
    val get_sort = TypeInfer.get_sort (tsig_of thy) def_sort (intern_sort thy);
    val T = intern_tycons thy (Syntax.read_typ thy syn get_sort (intern_sort thy) str);
  in cert thy T handle TYPE (msg, _, _) => error msg end
  handle ERROR => error ("The error(s) above occurred in type " ^ quote str);

fun gen_read_typ cert (thy, def_sort) str =
  gen_read_typ' cert (syn_of thy) (thy, def_sort) str;

in

fun no_def_sort thy = (thy: theory, K NONE);

val read_typ'        = gen_read_typ' certify_typ;
val read_typ_syntax' = gen_read_typ' certify_typ_syntax;
val read_typ_abbrev' = gen_read_typ' certify_typ_abbrev;
val read_typ         = gen_read_typ certify_typ;
val read_typ_syntax  = gen_read_typ certify_typ_syntax;
val read_typ_abbrev  = gen_read_typ certify_typ_abbrev;

end;


(* type and constant names *)

fun read_tyname thy raw_c =
  let val c = intern_type thy raw_c in
    (case Symtab.lookup (#2 (#types (Type.rep_tsig (tsig_of thy)))) c of
      SOME (Type.LogicalType n, _) => Type (c, replicate n dummyT)
    | _ => error ("Undeclared type constructor: " ^ quote c))
  end;

fun read_const thy raw_c =
  let
    val c = intern_const thy raw_c;
    val _ = the_const_type thy c handle TYPE (msg, _, _) => error msg;
  in Const (c, dummyT) end;



(** infer_types **)         (*exception ERROR*)

(*
  def_type: partial map from indexnames to types (constrains Frees and Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees and TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars

  termss: lists of alternative parses (only one combination should be type-correct)
  typs: expected types
*)

fun infer_types_simult pp thy def_type def_sort used freeze args =
  let
    val termss = fold_rev (multiply o fst) args [[]];
    val typs =
      map (fn (_, T) => certify_typ thy T handle TYPE (msg, _, _) => error msg) args;

    fun infer ts = OK (TypeInfer.infer_types (Syntax.pp_show_brackets pp) (tsig_of thy)
        (const_constraint thy) def_type def_sort (intern_const thy) (intern_tycons thy)
        (intern_sort thy) used freeze typs ts)
      handle TYPE (msg, _, _) => Error msg;

    val err_results = map infer termss;
    val errs = List.mapPartial get_error err_results;
    val results = List.mapPartial get_ok err_results;

    val ambiguity = length termss;

    fun ambig_msg () =
      if ambiguity > 1 andalso ambiguity <= ! Syntax.ambiguity_level
      then
        error_msg "Got more than one parse tree.\n\
          \Retry with smaller Syntax.ambiguity_level for more information."
      else ();
  in
    if null results then (ambig_msg (); error (cat_lines errs))
    else if length results = 1 then
      (if ambiguity > ! Syntax.ambiguity_level then
        warning "Fortunately, only one parse tree is type correct.\n\
          \You may still want to disambiguate your grammar or your input."
      else (); hd results)
    else (ambig_msg (); error ("More than one term is type correct:\n" ^
      cat_lines (map (Pretty.string_of_term pp) (List.concat (map fst results)))))
  end;

fun infer_types pp thy def_type def_sort used freeze tsT =
  apfst hd (infer_types_simult pp thy def_type def_sort used freeze [tsT]);


(* read_def_terms -- read terms and infer types *)    (*exception ERROR*)

fun read_def_terms' pp is_logtype syn (thy, types, sorts) used freeze sTs =
  let
    fun read (s, T) =
      let val T' = certify_typ thy T handle TYPE (msg, _, _) => error msg
      in (Syntax.read thy is_logtype syn T' s, T') end;
  in infer_types_simult pp thy types sorts used freeze (map read sTs) end;

fun read_def_terms (thy, types, sorts) =
  read_def_terms' (pp thy) (is_logtype thy) (syn_of thy) (thy, types, sorts);

fun simple_read_term thy T s =
  let val ([t], _) = read_def_terms (thy, K NONE, K NONE) [] true [(s, T)]
  in t end
  handle ERROR => error ("The error(s) above occurred for term " ^ s);

fun read_term thy = simple_read_term thy TypeInfer.logicT;
fun read_prop thy = simple_read_term thy propT;



(** signature extension functions **)  (*exception ERROR/TYPE*)

(* add default sort *)

fun gen_add_defsort prep_sort s thy =
  thy |> map_tsig (Type.set_defsort (prep_sort thy s));

val add_defsort = gen_add_defsort read_sort;
val add_defsort_i = gen_add_defsort certify_sort;


(* add type constructors *)

fun add_types types thy = thy |> map_sign (fn (naming, syn, tsig, consts) =>
  let
    val syn' = Syntax.extend_type_gram types syn;
    val decls = map (fn (a, n, mx) => (Syntax.type_name a mx, n)) types;
    val tsig' = Type.add_types naming decls tsig;
  in (naming, syn', tsig', consts) end);

fun add_typedecls decls thy =
  let
    fun type_of (a, vs, mx) =
      if null (duplicates vs) then (a, length vs, mx)
      else error ("Duplicate parameters in type declaration: " ^ quote a);
  in add_types (map type_of decls) thy end;


(* add nonterminals *)

fun add_nonterminals ns thy = thy |> map_sign (fn (naming, syn, tsig, consts) =>
  let
    val syn' = Syntax.extend_consts ns syn;
    val tsig' = Type.add_nonterminals naming ns tsig;
  in (naming, syn', tsig', consts) end);


(* add type abbreviations *)

fun gen_add_tyabbr prep_typ (a, vs, rhs, mx) thy =
  thy |> map_sign (fn (naming, syn, tsig, consts) =>
    let
      val syn' = Syntax.extend_type_gram [(a, length vs, mx)] syn;
      val a' = Syntax.type_name a mx;
      val abbr = (a', vs, prep_typ thy rhs)
        handle ERROR => error ("in type abbreviation " ^ quote a');
      val tsig' = Type.add_abbrevs naming [abbr] tsig;
    in (naming, syn', tsig', consts) end);

val add_tyabbrs = fold (gen_add_tyabbr (read_typ_syntax o no_def_sort));
val add_tyabbrs_i = fold (gen_add_tyabbr certify_typ_syntax);


(* add type arities *)

fun gen_add_arities int_type prep_sort arities thy = thy |> map_tsig (fn tsig =>
  let
    fun prep_arity (a, Ss, S) = (int_type thy a, map (prep_sort thy) Ss, prep_sort thy S)
      handle ERROR => error ("in arity for type " ^ quote a);
    val tsig' = Type.add_arities (pp thy) (map prep_arity arities) tsig;
  in tsig' end);

val add_arities = gen_add_arities intern_type read_sort;
val add_arities_i = gen_add_arities (K I) certify_sort;


(* modify syntax *)

fun gen_syntax change_gram prep_typ prmode args thy =
  let
    fun prep (c, T, mx) = (c, prep_typ thy T, mx)
      handle ERROR => error ("in syntax declaration " ^ quote (Syntax.const_name c mx));
  in thy |> map_syn (change_gram (is_logtype thy) prmode (map prep args)) end;

fun gen_add_syntax x = gen_syntax Syntax.extend_const_gram x;

val add_modesyntax = gen_add_syntax (read_typ_syntax o no_def_sort);
val add_modesyntax_i = gen_add_syntax certify_typ_syntax;
val add_syntax = add_modesyntax Syntax.default_mode;
val add_syntax_i = add_modesyntax_i Syntax.default_mode;
val del_modesyntax = gen_syntax Syntax.remove_const_gram (read_typ_syntax o no_def_sort);
val del_modesyntax_i = gen_syntax Syntax.remove_const_gram certify_typ_syntax;


(* add constants *)

local

fun gen_add_consts prep_typ raw_args thy =
  let
    val prepT = Compress.typ thy o Type.varifyT o Type.no_tvars o Term.no_dummyT o prep_typ thy;
    fun prep (c, T, mx) = ((c, prepT T, mx) handle TYPE (msg, _, _) => error msg)
      handle ERROR => error ("in declaration of constant " ^ quote (Syntax.const_name c mx));
    val args = map prep raw_args;
    val decls = args |> map (fn (c, T, mx) => (Syntax.const_name c mx, T));
  in
    thy
    |> map_consts (fold (Consts.declare (naming_of thy)) decls)
    |> add_syntax_i args
  end;

in

val add_consts = gen_add_consts (read_typ o no_def_sort);
val add_consts_i = gen_add_consts certify_typ;

end;


(* add constraints *)

fun gen_add_constraint int_const prep_typ (raw_c, raw_T) thy =
  let
    val c = int_const thy raw_c;
    val T = Term.zero_var_indexesT (Term.no_dummyT (prep_typ thy raw_T))
      handle TYPE (msg, _, _) => error msg;
    val _ = cert_term thy (Const (c, T))
      handle TYPE (msg, _, _) => error msg;
  in thy |> map_consts (Consts.constrain (c, T)) end;

val add_const_constraint = gen_add_constraint intern_const (read_typ o no_def_sort);
val add_const_constraint_i = gen_add_constraint (K I) certify_typ;


(* add type classes *)

val classN = "_class";

val const_of_class = suffix classN;
fun class_of_const c = unsuffix classN c
  handle Fail _ => raise TERM ("class_of_const: bad name " ^ quote c, []);

fun gen_add_class int_class (bclass, raw_classes) thy =
  thy |> map_sign (fn (naming, syn, tsig, consts) =>
    let
      val classes = map (int_class thy) raw_classes;
      val syn' = Syntax.extend_consts [bclass] syn;
      val tsig' = Type.add_classes (pp thy) naming [(bclass, classes)] tsig;
    in (naming, syn', tsig', consts) end)
  |> add_consts_i [(const_of_class bclass, a_itselfT --> propT, Syntax.NoSyn)];

val add_classes = fold (gen_add_class intern_class);
val add_classes_i = fold (gen_add_class (K I));


(* add to classrel *)

fun gen_add_classrel int_class raw_pairs thy = thy |> map_tsig (fn tsig =>
  let
    val pairs = map (pairself (int_class thy)) raw_pairs;
    val tsig' = Type.add_classrel (pp thy) pairs tsig;
  in tsig' end);

val add_classrel = gen_add_classrel intern_class;
val add_classrel_i = gen_add_classrel (K I);


(* add translation functions *)

local

fun mk trs = map Syntax.mk_trfun trs;

fun gen_add_trfuns ext non_typed (atrs, trs, tr's, atr's) =
  map_syn (ext (mk atrs, mk trs, mk (map (apsnd non_typed) tr's), mk atr's));

fun gen_add_trfunsT ext tr's = map_syn (ext ([], [], mk tr's, []));

in

val add_trfuns = gen_add_trfuns Syntax.extend_trfuns Syntax.non_typed_tr';
val add_trfunsT = gen_add_trfunsT Syntax.extend_trfuns;
val add_advanced_trfuns = gen_add_trfuns Syntax.extend_advanced_trfuns Syntax.non_typed_tr'';
val add_advanced_trfunsT = gen_add_trfunsT Syntax.extend_advanced_trfuns;

end;

val add_tokentrfuns = map_syn o Syntax.extend_tokentrfuns;
fun add_mode_tokentrfuns m = add_tokentrfuns o map (fn (s, f) => (m, s, f));


(* compile translation functions *)

local

fun advancedT false = ""
  | advancedT true = "theory -> ";

fun advancedN false = ""
  | advancedN true = "advanced_";

in

fun parse_ast_translation (a, txt) =
  txt |> Context.use_let ("val parse_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Sign.add_" ^ advancedN a ^ "trfuns (parse_ast_translation, [], [], [])");

fun parse_translation (a, txt) =
  txt |> Context.use_let ("val parse_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Sign.add_" ^ advancedN a ^ "trfuns ([], parse_translation, [], [])");

fun print_translation (a, txt) =
  txt |> Context.use_let ("val print_translation: (string * (" ^ advancedT a ^
      "term list -> term)) list")
    ("Sign.add_" ^ advancedN a ^ "trfuns ([], [], print_translation, [])");

fun print_ast_translation (a, txt) =
  txt |> Context.use_let ("val print_ast_translation: (string * (" ^ advancedT a ^
      "Syntax.ast list -> Syntax.ast)) list")
    ("Sign.add_" ^ advancedN a ^ "trfuns ([], [], [], print_ast_translation)");

fun typed_print_translation (a, txt) =
  txt |> Context.use_let ("val typed_print_translation: (string * (" ^ advancedT a ^
      "bool -> typ -> term list -> term)) list")
    ("Sign.add_" ^ advancedN a ^ "trfunsT typed_print_translation");

val token_translation =
  Context.use_let "val token_translation: (string * string * (string -> string * real)) list"
    "Sign.add_tokentrfuns token_translation";

end;


(* add translation rules *)

fun add_trrules args thy = thy |> map_syn (fn syn =>
  let val rules = map (Syntax.map_trrule (apfst (intern_type thy))) args
  in Syntax.extend_trrules thy (is_logtype thy) syn rules syn end);

val add_trrules_i = map_syn o Syntax.extend_trrules_i;


(* modify naming *)

val add_path        = map_naming o NameSpace.add_path;
val qualified_names = map_naming NameSpace.qualified_names;
val no_base_names   = map_naming NameSpace.no_base_names;
val custom_accesses = map_naming o NameSpace.custom_accesses;
val set_policy      = map_naming o NameSpace.set_policy;
val restore_naming  = map_naming o K o naming_of;

val parent_path     = add_path "..";
val root_path       = add_path "/";
val absolute_path   = add_path "//";

fun local_path thy = thy |> root_path |> add_path (Context.theory_name thy);


(* hide names *)

fun hide_classes b xs thy = thy |> map_tsig (Type.hide_classes b (map (intern_class thy) xs));
val hide_classes_i = map_tsig oo Type.hide_classes;
fun hide_types b xs thy = thy |> map_tsig (Type.hide_types b (map (intern_type thy) xs));
val hide_types_i = map_tsig oo Type.hide_types;
fun hide_consts b xs thy = thy |> map_consts (fold (Consts.hide b o intern_const thy) xs);
val hide_consts_i = map_consts oo (fold o Consts.hide);

local

val kinds =
 [("class", (intern_class, can o certify_class, hide_classes_i)),
  ("type", (intern_type, declared_tyname, hide_types_i)),
  ("const", (intern_const, declared_const, hide_consts_i))];

fun gen_hide int b (kind, xnames) thy =
  (case AList.lookup (op =) kinds kind of
    SOME (intern, check, hide) =>
      let
        val names = if int then map (intern thy) xnames else xnames;
        val bads = filter_out (check thy) names;
      in
        if null bads then hide b names thy
        else error ("Attempt to hide undeclared item(s): " ^ commas_quote bads)
      end
  | NONE => error ("Bad name space specification: " ^ quote kind));

in

val hide_names = gen_hide true;
val hide_names_i = gen_hide false;

end;

end;
