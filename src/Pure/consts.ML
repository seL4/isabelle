(*  Title:      Pure/consts.ML
    ID:         $Id$
    Author:     Makarius

Polymorphic constants: declarations, abbreviations, additional type
constraints.
*)

signature CONSTS =
sig
  type T
  val eq_consts: T * T -> bool
  val abbrevs_of: T -> string list -> (term * term) list
  val dest: T ->
   {constants: (typ * (term * term) option) NameSpace.table,
    constraints: typ NameSpace.table}
  val the_abbreviation: T -> string -> typ * (term * term)          (*exception TYPE*)
  val the_declaration: T -> string -> typ                           (*exception TYPE*)
  val is_monomorphic: T -> string -> bool                           (*exception TYPE*)
  val the_constraint: T -> string -> typ                            (*exception TYPE*)
  val the_tags: T -> string -> Markup.property list                 (*exception TYPE*)
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
  val declare: bool -> NameSpace.naming -> Markup.property list -> (bstring * typ) -> T -> T
  val constrain: string * typ option -> T -> T
  val abbreviate: Pretty.pp -> Type.tsig -> NameSpace.naming -> string -> Markup.property list ->
    bstring * term -> T -> (term * term) * T
  val hide: bool -> string -> T -> T
  val empty: T
  val merge: T * T -> T
end;

structure Consts: CONSTS =
struct


(** consts type **)

(* datatype T *)

datatype kind =
  LogicalConst of int list list |      (*typargs positions*)
  Abbreviation of term * term * bool   (*rhs, normal rhs, force_expand*);

type decl = {T: typ, kind: kind, tags: Markup.property list, authentic: bool};

datatype T = Consts of
 {decls: (decl * serial) NameSpace.table,
  constraints: typ Symtab.table,
  rev_abbrevs: (term * term) list Symtab.table} * stamp;

fun eq_consts (Consts (_, s1), Consts (_, s2)) = s1 = s2;

fun make_consts (decls, constraints, rev_abbrevs) =
  Consts ({decls = decls, constraints = constraints, rev_abbrevs = rev_abbrevs}, stamp ());

fun map_consts f (Consts ({decls, constraints, rev_abbrevs}, _)) =
  make_consts (f (decls, constraints, rev_abbrevs));

fun abbrevs_of (Consts ({rev_abbrevs, ...}, _)) modes =
  maps (Symtab.lookup_list rev_abbrevs) modes;


(* dest consts *)

fun dest_kind (LogicalConst _) = NONE
  | dest_kind (Abbreviation (t, t', _)) = SOME (t, t');

fun dest (Consts ({decls = (space, decls), constraints, ...}, _)) =
 {constants = (space,
    Symtab.fold (fn (c, ({T, kind, ...}, _)) =>
      Symtab.update (c, (T, dest_kind kind))) decls Symtab.empty),
  constraints = (space, constraints)};


(* lookup consts *)

fun the_const (Consts ({decls = (_, tab), ...}, _)) c =
  (case Symtab.lookup tab c of
    SOME (decl, _) => decl
  | NONE => raise TYPE ("Undeclared constant: " ^ quote c, [], []));

fun logical_const consts c =
  (case the_const consts c of
    {T, kind = LogicalConst ps, ...} => (T, ps)
  | _ => raise TYPE ("Not a logical constant: " ^ quote c, [], []));

fun the_abbreviation consts c =
  (case the_const consts c of
    {T, kind = Abbreviation (t, t', _), ...} => (T, (t, t'))
  | _ => raise TYPE ("Not an abbreviated constant: " ^ quote c, [], []));

val the_declaration = #1 oo logical_const;
val type_arguments = #2 oo logical_const;
val is_monomorphic = null oo type_arguments;

fun the_constraint (consts as Consts ({constraints, ...}, _)) c =
  (case Symtab.lookup constraints c of
    SOME T => T
  | NONE => #T (the_const consts c));

val the_tags = #tags oo the_const;


(* name space and syntax *)

fun space_of (Consts ({decls = (space, _), ...}, _)) = space;

val intern = NameSpace.intern o space_of;
val extern = NameSpace.extern o space_of;

fun extern_early consts c =
  (case try (the_const consts) c of
    SOME {authentic = true, ...} => Syntax.constN ^ c
  | _ => extern consts c);

fun syntax consts (c, mx) =
  let
    val {T, authentic, ...} = the_const consts c handle TYPE (msg, _, _) => error msg;
    val c' = if authentic then Syntax.constN ^ c else NameSpace.base c;
  in (c', T, mx) end;

fun syntax_name consts c = #1 (syntax consts (c, NoSyn));


(* read_const *)

fun read_const consts raw_c =
  let
    val c = intern consts raw_c;
    val {T, ...} = the_const consts c handle TYPE (msg, _, _) => error msg;
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
              val {T = U, kind, ...} = the_const consts c;
            in
              if not (Type.raw_instance (T', U)) then
                err "Illegal type for constant" (c, T)
              else
                (case kind of
                  Abbreviation (_, u, force_expand) =>
                    if do_expand orelse force_expand then
                      Term.betapplys (Envir.expand_atom T' (U, u) handle TYPE _ =>
                        err "Illegal type for abbreviation" (c, T), args')
                    else comb head
                | _ => comb head)
            end
        | _ => comb head)
      end;
  in cert end;


(* typargs -- view actual const type as instance of declaration *)

fun subscript (Type (_, Ts)) (i :: is) = subscript (nth Ts i) is
  | subscript T [] = T
  | subscript T _ = raise Subscript;

fun typargs consts (c, T) = map (subscript T) (type_arguments consts c);

fun instance consts (c, Ts) =
  let
    val declT = the_declaration consts c;
    val vars = map Term.dest_TVar (typargs consts (c, declT));
    val inst = vars ~~ Ts handle UnequalLengths =>
      raise TYPE ("Consts.instance", Ts, [Const (c, dummyT)]);
  in declT |> TermSubst.instantiateT inst end;



(** build consts **)

fun err_dup_const c =
  error ("Duplicate declaration of constant " ^ quote c);

fun err_inconsistent_constraints c =
  error ("Inconsistent type constraints for constant " ^ quote c);

fun extend_decls naming decl tab = NameSpace.extend_table naming [decl] tab
  handle Symtab.DUP c => err_dup_const c;


(* name space *)

fun hide fully c = map_consts (fn (decls, constraints, rev_abbrevs) =>
  (apfst (NameSpace.hide fully c) decls, constraints, rev_abbrevs));


(* declarations *)

fun declare authentic naming tags (c, declT) = map_consts (fn (decls, constraints, rev_abbrevs) =>
  let
    fun args_of (Type (_, Ts)) pos = args_of_list Ts 0 pos
      | args_of (TVar v) pos = insert (eq_fst op =) (v, rev pos)
      | args_of (TFree _) _ = I
    and args_of_list (T :: Ts) i is = args_of T (i :: is) #> args_of_list Ts (i + 1) is
      | args_of_list [] _ _ = I;
    val decl =
      {T = declT, kind = LogicalConst (map #2 (rev (args_of declT [] []))),
        tags = tags, authentic = authentic};
    val decls' = decls |> extend_decls naming (c, (decl, serial ()));
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

fun strip_abss tm = ([], tm) ::
  (case tm of
    Abs (a, T, t) =>
      if Term.loose_bvar1 (t, 0) then
        strip_abss t |> map (fn (xs, b) => ((a, T) :: xs, b))
      else []
  | _ => []);

fun rev_abbrev lhs rhs =
  let
    fun abbrev (xs, body) =
      let val vars = fold (fn (x, T) => cons (Var ((x, 0), T))) (Term.rename_wrt_term body xs) []
      in (Term.subst_bounds (rev vars, body), Term.list_comb (lhs, vars)) end;
  in map abbrev (strip_abss (Envir.beta_eta_contract rhs)) end;

in

fun abbreviate pp tsig naming mode tags (c, raw_rhs) consts =
  let
    val cert_term = certify pp tsig false consts;
    val expand_term = certify pp tsig true consts;
    val force_expand = mode = Syntax.internalM;

    val rhs = raw_rhs
      |> Term.map_types (Type.cert_typ tsig)
      |> cert_term;
    val T = Term.fastype_of rhs;
    val lhs = Const (NameSpace.full naming c, T);
    val rhs' = expand_term rhs;

    fun err msg = error (msg ^ " on rhs of abbreviation:\n" ^
      Pretty.string_of_term pp (Logic.mk_equals (lhs, rhs)));
    val _ = Term.exists_subterm Term.is_Var rhs andalso err "Illegal schematic variables"
    val _ = null (Term.hidden_polymorphism rhs T) orelse err "Extra type variables";
  in
    consts |> map_consts (fn (decls, constraints, rev_abbrevs) =>
      let
        val decl =
          {T = T, kind = Abbreviation (rhs, rhs', force_expand), tags = tags, authentic = true};
        val decls' = decls
          |> extend_decls naming (c, (decl, serial ()));
        val rev_abbrevs' = rev_abbrevs
          |> fold (curry Symtab.update_list mode) (rev_abbrev lhs rhs);
      in (decls', constraints, rev_abbrevs') end)
    |> pair (lhs, rhs)
  end;

end;


(* empty and merge *)

val empty = make_consts (NameSpace.empty_table, Symtab.empty, Symtab.empty);

fun merge
   (Consts ({decls = decls1, constraints = constraints1, rev_abbrevs = rev_abbrevs1}, _),
    Consts ({decls = decls2, constraints = constraints2, rev_abbrevs = rev_abbrevs2}, _)) =
  let
    val decls' = NameSpace.merge_tables (eq_snd (op =)) (decls1, decls2)
      handle Symtab.DUP c => err_dup_const c;
    val constraints' = Symtab.merge (op =) (constraints1, constraints2)
      handle Symtab.DUP c => err_inconsistent_constraints c;
    val rev_abbrevs' = (rev_abbrevs1, rev_abbrevs2) |> Symtab.join
      (K (Library.merge (fn ((t, u), (t', u')) => t aconv t' andalso u aconv u')));
  in make_consts (decls', constraints', rev_abbrevs') end;

end;
