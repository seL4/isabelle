(*  Title:      Pure/consts.ML
    Author:     Makarius

Polymorphic constants: declarations, abbreviations, additional type
constraints.
*)

signature CONSTS =
sig
  type T
  val eq_consts: T * T -> bool
  val retrieve_abbrevs: T -> string list -> term -> (term * term) list
  val dest: T ->
   {constants: (typ * term option) NameSpace.table,
    constraints: typ NameSpace.table}
  val the_type: T -> string -> typ                             (*exception TYPE*)
  val the_abbreviation: T -> string -> typ * term              (*exception TYPE*)
  val type_scheme: T -> string -> typ                          (*exception TYPE*)
  val the_tags: T -> string -> Properties.T                    (*exception TYPE*)
  val is_monomorphic: T -> string -> bool                      (*exception TYPE*)
  val the_constraint: T -> string -> typ                       (*exception TYPE*)
  val space_of: T -> NameSpace.T
  val intern: T -> xstring -> string
  val extern: T -> string -> xstring
  val extern_early: T -> string -> xstring
  val syntax: T -> string * mixfix -> string * typ * mixfix
  val syntax_name: T -> string -> string
  val read_const: T -> string -> term
  val certify: Pretty.pp -> Type.tsig -> bool -> T -> term -> term  (*exception TYPE*)
  val typargs: T -> string * typ -> typ list
  val instance: T -> string * typ list -> typ
  val declare: bool -> NameSpace.naming -> Properties.T -> (binding * typ) -> T -> T
  val constrain: string * typ option -> T -> T
  val abbreviate: Pretty.pp -> Type.tsig -> NameSpace.naming -> string -> Properties.T ->
    binding * term -> T -> (term * term) * T
  val revert_abbrev: string -> string -> T -> T
  val hide: bool -> string -> T -> T
  val empty: T
  val merge: T * T -> T
end;

structure Consts: CONSTS =
struct

(** consts type **)

(* datatype T *)

type decl = {T: typ, typargs: int list list, tags: Properties.T, authentic: bool};
type abbrev = {rhs: term, normal_rhs: term, force_expand: bool};

datatype T = Consts of
 {decls: ((decl * abbrev option) * serial) NameSpace.table,
  constraints: typ Symtab.table,
  rev_abbrevs: (term * term) Item_Net.T Symtab.table};

fun eq_consts
   (Consts {decls = decls1, constraints = constraints1, rev_abbrevs = rev_abbrevs1},
    Consts {decls = decls2, constraints = constraints2, rev_abbrevs = rev_abbrevs2}) =
  pointer_eq (decls1, decls2) andalso
  pointer_eq (constraints1, constraints2) andalso
  pointer_eq (rev_abbrevs1, rev_abbrevs2);

fun make_consts (decls, constraints, rev_abbrevs) =
  Consts {decls = decls, constraints = constraints, rev_abbrevs = rev_abbrevs};

fun map_consts f (Consts {decls, constraints, rev_abbrevs}) =
  make_consts (f (decls, constraints, rev_abbrevs));


(* reverted abbrevs *)

val empty_abbrevs = Item_Net.init (fn ((t, u), (t', u')) => t aconv t' andalso u aconv u') #1;

fun insert_abbrevs mode abbrs =
  Symtab.map_default (mode, empty_abbrevs) (Item_Net.insert abbrs);

fun retrieve_abbrevs (Consts {rev_abbrevs, ...}) modes =
  let val nets = map_filter (Symtab.lookup rev_abbrevs) modes
  in fn t => maps (fn net => Item_Net.retrieve net t) nets end;


(* dest consts *)

fun dest (Consts {decls = (space, decls), constraints, ...}) =
 {constants = (space,
    Symtab.fold (fn (c, (({T, ...}, abbr), _)) =>
      Symtab.update (c, (T, Option.map #rhs abbr))) decls Symtab.empty),
  constraints = (space, constraints)};


(* lookup consts *)

fun the_const (Consts {decls = (_, tab), ...}) c =
  (case Symtab.lookup tab c of
    SOME (decl, _) => decl
  | NONE => raise TYPE ("Unknown constant: " ^ quote c, [], []));

fun the_type consts c =
  (case the_const consts c of
    ({T, ...}, NONE) => T
  | _ => raise TYPE ("Not a logical constant: " ^ quote c, [], []));

fun the_abbreviation consts c =
  (case the_const consts c of
    ({T, ...}, SOME {rhs, ...}) => (T, rhs)
  | _ => raise TYPE ("Not an abbreviated constant: " ^ quote c, [], []));

val the_decl = #1 oo the_const;
val type_scheme = #T oo the_decl;
val type_arguments = #typargs oo the_decl;
val the_tags = #tags oo the_decl;

val is_monomorphic = null oo type_arguments;

fun the_constraint (consts as Consts {constraints, ...}) c =
  (case Symtab.lookup constraints c of
    SOME T => T
  | NONE => type_scheme consts c);


(* name space and syntax *)

fun space_of (Consts {decls = (space, _), ...}) = space;

val intern = NameSpace.intern o space_of;
val extern = NameSpace.extern o space_of;

fun extern_early consts c =
  (case try (the_const consts) c of
    SOME ({authentic = true, ...}, _) => Syntax.constN ^ c
  | _ => extern consts c);

fun syntax consts (c, mx) =
  let
    val ({T, authentic, ...}, _) = the_const consts c handle TYPE (msg, _, _) => error msg;
    val c' = if authentic then Syntax.constN ^ c else Long_Name.base_name c;
  in (c', T, mx) end;

fun syntax_name consts c = #1 (syntax consts (c, NoSyn));


(* read_const *)

fun read_const consts raw_c =
  let
    val c = intern consts raw_c;
    val T = type_scheme consts c handle TYPE (msg, _, _) => error msg;
  in Const (c, T) end;


(* certify *)

fun certify pp tsig do_expand consts =
  let
    fun err msg (c, T) =
      raise TYPE (msg ^ " " ^ quote c ^ " :: " ^ Pretty.string_of_typ pp T, [], []);
    val certT = Type.cert_typ tsig;
    fun cert tm =
      let
        val (head, args) = Term.strip_comb tm;
        val args' = map cert args;
        fun comb head' = Term.list_comb (head', args');
      in
        (case head of
          Abs (x, T, t) => comb (Abs (x, certT T, cert t))
        | Const (c, T) =>
            let
              val T' = certT T;
              val ({T = U, ...}, abbr) = the_const consts c;
              fun expand u =
                Term.betapplys (Envir.expand_atom T' (U, u) handle TYPE _ =>
                  err "Illegal type for abbreviation" (c, T), args');
            in
              if not (Type.raw_instance (T', U)) then
                err "Illegal type for constant" (c, T)
              else
                (case abbr of
                  SOME {rhs, normal_rhs, force_expand} =>
                    if do_expand then expand normal_rhs
                    else if force_expand then expand rhs
                    else comb head
                | _ => comb head)
            end
        | _ => comb head)
      end;
  in cert end;


(* typargs -- view actual const type as instance of declaration *)

local

fun args_of (Type (_, Ts)) pos = args_of_list Ts 0 pos
  | args_of (TVar v) pos = insert (eq_fst op =) (v, rev pos)
  | args_of (TFree _) _ = I
and args_of_list (T :: Ts) i is = args_of T (i :: is) #> args_of_list Ts (i + 1) is
  | args_of_list [] _ _ = I;

fun subscript (Type (_, Ts)) (i :: is) = subscript (nth Ts i) is
  | subscript T [] = T
  | subscript T _ = raise Subscript;

in

fun typargs_of T = map #2 (rev (args_of T [] []));

fun typargs consts (c, T) = map (subscript T) (type_arguments consts c);

end;

fun instance consts (c, Ts) =
  let
    val declT = type_scheme consts c;
    val vars = map Term.dest_TVar (typargs consts (c, declT));
    val inst = vars ~~ Ts handle UnequalLengths =>
      raise TYPE ("Consts.instance", Ts, [Const (c, dummyT)]);
  in declT |> Term_Subst.instantiateT inst end;



(** build consts **)

fun err_dup_const c =
  error ("Duplicate declaration of constant " ^ quote c);

fun extend_decls naming decl tab = NameSpace.define naming decl tab
  handle Symtab.DUP c => err_dup_const c;


(* name space *)

fun hide fully c = map_consts (fn (decls, constraints, rev_abbrevs) =>
  (apfst (NameSpace.hide fully c) decls, constraints, rev_abbrevs));


(* declarations *)

fun declare authentic naming tags (b, declT) = map_consts (fn (decls, constraints, rev_abbrevs) =>
  let
    val tags' = tags |> Position.default_properties (Position.thread_data ());
    val decl = {T = declT, typargs = typargs_of declT, tags = tags', authentic = authentic};
    val (_, decls') = decls |> extend_decls naming (b, ((decl, NONE), serial ()));
  in (decls', constraints, rev_abbrevs) end);


(* constraints *)

fun constrain (c, C) consts =
  consts |> map_consts (fn (decls, constraints, rev_abbrevs) =>
    (the_const consts c handle TYPE (msg, _, _) => error msg;
      (decls,
        constraints |> (case C of SOME T => Symtab.update (c, T) | NONE => Symtab.delete_safe c),
        rev_abbrevs)));


(* abbreviations *)

local

fun strip_abss (t as Abs (x, T, b)) =
      if Term.loose_bvar1 (b, 0) then strip_abss b |>> cons (x, T)
      else ([], t)
  | strip_abss t = ([], t);

fun rev_abbrev lhs rhs =
  let
    val (xs, body) = strip_abss (Envir.beta_eta_contract rhs);
    val vars = fold (fn (x, T) => cons (Var ((x, 0), T))) (Term.rename_wrt_term body xs) [];
  in (Term.subst_bounds (rev vars, body), Term.list_comb (lhs, vars)) end;

in

fun abbreviate pp tsig naming mode tags (b, raw_rhs) consts =
  let
    val cert_term = certify pp tsig false consts;
    val expand_term = certify pp tsig true consts;
    val force_expand = mode = PrintMode.internal;

    val _ = Term.exists_subterm Term.is_Var raw_rhs andalso
      error ("Illegal schematic variables on rhs of abbreviation: " ^ Binding.str_of b);

    val rhs = raw_rhs
      |> Term.map_types (Type.cert_typ tsig)
      |> cert_term
      |> Term.close_schematic_term;
    val normal_rhs = expand_term rhs;
    val T = Term.fastype_of rhs;
    val lhs = Const (NameSpace.full_name naming b, T);
  in
    consts |> map_consts (fn (decls, constraints, rev_abbrevs) =>
      let
        val tags' = tags |> Position.default_properties (Position.thread_data ());
        val decl = {T = T, typargs = typargs_of T, tags = tags', authentic = true};
        val abbr = {rhs = rhs, normal_rhs = normal_rhs, force_expand = force_expand};
        val (_, decls') = decls
          |> extend_decls naming (b, ((decl, SOME abbr), serial ()));
        val rev_abbrevs' = rev_abbrevs
          |> insert_abbrevs mode (rev_abbrev lhs rhs);
      in (decls', constraints, rev_abbrevs') end)
    |> pair (lhs, rhs)
  end;

fun revert_abbrev mode c consts = consts |> map_consts (fn (decls, constraints, rev_abbrevs) =>
  let
    val (T, rhs) = the_abbreviation consts c;
    val rev_abbrevs' = rev_abbrevs
      |> insert_abbrevs mode (rev_abbrev (Const (c, T)) rhs);
  in (decls, constraints, rev_abbrevs') end);

end;


(* empty and merge *)

val empty = make_consts (NameSpace.empty_table, Symtab.empty, Symtab.empty);

fun merge
   (Consts {decls = decls1, constraints = constraints1, rev_abbrevs = rev_abbrevs1},
    Consts {decls = decls2, constraints = constraints2, rev_abbrevs = rev_abbrevs2}) =
  let
    val decls' = NameSpace.merge_tables (eq_snd (op =)) (decls1, decls2)
      handle Symtab.DUP c => err_dup_const c;
    val constraints' = Symtab.join (K fst) (constraints1, constraints2);
    val rev_abbrevs' = Symtab.join (K Item_Net.merge) (rev_abbrevs1, rev_abbrevs2);
  in make_consts (decls', constraints', rev_abbrevs') end;

end;
