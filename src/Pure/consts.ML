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
   {constants: (typ * term option) NameSpace.table,
    constraints: typ NameSpace.table}
  val declaration: T -> string -> typ                               (*exception TYPE*)
  val monomorphic: T -> string -> bool                              (*exception TYPE*)
  val constraint: T -> string -> typ                                (*exception TYPE*)
  val space_of: T -> NameSpace.T
  val intern: T -> xstring -> string
  val extern: T -> string -> xstring
  val extern_early: T -> string -> xstring
  val syntax: T -> string * mixfix -> string * typ * mixfix
  val read_const: T -> string -> term
  val certify: Pretty.pp -> Type.tsig -> T -> term -> term          (*exception TYPE*)
  val typargs: T -> string * typ -> typ list
  val instance: T -> string * typ list -> typ
  val declare: NameSpace.naming -> (bstring * typ) * bool -> T -> T
  val constrain: string * typ option -> T -> T
  val expand_abbrevs: bool -> T -> T
  val abbreviate: Pretty.pp -> Type.tsig -> NameSpace.naming -> string ->
    (bstring * term) * bool -> T -> T
  val hide: bool -> string -> T -> T
  val empty: T
  val merge: T * T -> T
end;

structure Consts: CONSTS =
struct


(** consts type **)

(* datatype T *)

datatype kind =
  LogicalConst of int list list |
  Abbreviation of term;

type decl =
  (typ * kind) *
  bool; (*authentic syntax*)

datatype T = Consts of
 {decls: (decl * stamp) NameSpace.table,
  constraints: typ Symtab.table,
  rev_abbrevs: (term * term) list Symtab.table,
  expand_abbrevs: bool} * stamp;

fun eq_consts (Consts (_, s1), Consts (_, s2)) = s1 = s2;

fun make_consts (decls, constraints, rev_abbrevs, expand_abbrevs) =
  Consts ({decls = decls, constraints = constraints, rev_abbrevs = rev_abbrevs,
    expand_abbrevs = expand_abbrevs}, stamp ());

fun map_consts f (Consts ({decls, constraints, rev_abbrevs, expand_abbrevs}, _)) =
  make_consts (f (decls, constraints, rev_abbrevs, expand_abbrevs));

fun abbrevs_of (Consts ({rev_abbrevs, ...}, _)) modes =
  maps (Symtab.lookup_list rev_abbrevs) modes;


(* dest consts *)

fun dest_kind (LogicalConst _) = NONE
  | dest_kind (Abbreviation t) = SOME t;

fun dest (Consts ({decls = (space, decls), constraints, ...}, _)) =
 {constants = (space,
    Symtab.fold (fn (c, (((T, kind), _), _)) =>
      Symtab.update (c, (T, dest_kind kind))) decls Symtab.empty),
  constraints = (space, constraints)};


(* lookup consts *)

fun the_const (Consts ({decls = (_, tab), ...}, _)) c =
  (case Symtab.lookup tab c of
    SOME (decl, _) => decl
  | NONE => raise TYPE ("Undeclared constant: " ^ quote c, [], []));

fun logical_const consts c =
  (case the_const consts c of
    ((T, LogicalConst ps), _) => (T, ps)
  | _ => raise TYPE ("Illegal abbreviation: " ^ quote c, [], []));

val declaration = #1 oo logical_const;
val type_arguments = #2 oo logical_const;
val monomorphic = null oo type_arguments;

fun constraint (consts as Consts ({constraints, ...}, _)) c =
  (case Symtab.lookup constraints c of
    SOME T => T
  | NONE => #1 (#1 (the_const consts c)));


(* name space and syntax *)

fun space_of (Consts ({decls = (space, _), ...}, _)) = space;

val intern = NameSpace.intern o space_of;
val extern = NameSpace.extern o space_of;

fun extern_early consts c =
  (case try (the_const consts) c of
    SOME (_, true) => Syntax.constN ^ c
  | _ => extern consts c);

fun syntax consts (c, mx) =
  let
    val ((T, _), authentic) = the_const consts c handle TYPE (msg, _, _) => error msg;
    val c' = if authentic then Syntax.constN ^ c else NameSpace.base c;
  in (c', T, mx) end;


(* read_const *)

fun read_const consts raw_c =
  let
    val c = intern consts raw_c;
    val _ = the_const consts c handle TYPE (msg, _, _) => error msg;
  in Const (c, dummyT) end;


(* certify *)

fun certify pp tsig (consts as Consts ({expand_abbrevs, ...}, _)) =
  let
    fun err msg (c, T) =
      raise TYPE (msg ^ " " ^ quote c ^ " :: " ^ Pretty.string_of_typ pp T, [], []);
    fun cert tm =
      let
        val (head, args) = Term.strip_comb tm;
        fun comb h = Term.list_comb (h, map cert args);
      in
        (case head of
          Abs (x, T, t) => comb (Abs (x, T, cert t))
        | Const (c, T) =>
            let
              val T' = Type.cert_typ tsig T;
              val ((U, kind), _) = the_const consts c;
            in
              if not (Type.raw_instance (T', U)) then
                err "Illegal type for constant" (c, T)
              else
                (case (kind, expand_abbrevs) of
                  (Abbreviation u, true) =>
                    Term.betapplys (Envir.expand_atom T' (U, u) handle TYPE _ =>
                      err "Illegal type for abbreviation" (c, T), map cert args)
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
    val declT = declaration consts c;
    val vars = map Term.dest_TVar (typargs consts (c, declT));
  in declT |> Term.instantiateT (vars ~~ Ts) end;



(** build consts **)

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);

fun err_inconsistent_constraints cs =
  error ("Inconsistent type constraints for constant(s) " ^ commas_quote cs);

fun extend_decls naming decl tab = NameSpace.extend_table naming (tab, [decl])
  handle Symtab.DUPS cs => err_dup_consts cs;


(* name space *)

fun hide fully c = map_consts (fn (decls, constraints, rev_abbrevs, expand_abbrevs) =>
  (apfst (NameSpace.hide fully c) decls, constraints, rev_abbrevs, expand_abbrevs));


(* declarations *)

fun declare naming ((c, declT), authentic) =
    map_consts (fn (decls, constraints, rev_abbrevs, expand_abbrevs) =>
  let
    fun args_of (Type (_, Ts)) pos = args_of_list Ts 0 pos
      | args_of (TVar v) pos = insert (eq_fst op =) (v, rev pos)
      | args_of (TFree _) _ = I
    and args_of_list (T :: Ts) i is = args_of T (i :: is) #> args_of_list Ts (i + 1) is
      | args_of_list [] _ _ = I;
    val decl = (((declT, LogicalConst (map #2 (rev (args_of declT [] [])))), authentic), stamp ());
  in (extend_decls naming (c, decl) decls, constraints, rev_abbrevs, expand_abbrevs) end);


(* constraints *)

fun constrain (c, C) consts =
  consts |> map_consts (fn (decls, constraints, rev_abbrevs, expand_abbrevs) =>
    (the_const consts c handle TYPE (msg, _, _) => error msg;
      (decls,
        constraints |> (case C of SOME T => Symtab.update (c, T) | NONE => Symtab.delete_safe c),
        rev_abbrevs, expand_abbrevs)));


(* abbreviations *)

fun expand_abbrevs b = map_consts (fn (decls, constraints, rev_abbrevs, _) =>
  (decls, constraints, rev_abbrevs, b));

local

fun strip_abss tm = ([], tm) ::
  (case tm of
    Abs (a, T, t) =>
      if Term.loose_bvar1 (t, 0) then
        strip_abss t |> map (fn (xs, b) => ((a, T) :: xs, b))
      else []
  | _ => []);

fun rev_abbrev const rhs =
  let
    fun abbrev (xs, body) =
      let val vars = fold (fn (x, T) => cons (Var ((x, 0), T))) (Term.rename_wrt_term body xs) []
      in (Term.subst_bounds (rev vars, body), Term.list_comb (Const const, vars)) end;
  in map abbrev (strip_abss (Envir.beta_eta_contract rhs)) end;

in

fun abbreviate pp tsig naming mode ((c, raw_rhs), authentic) consts =
  let
    val rhs = raw_rhs
      |> Term.map_term_types (Type.cert_typ tsig)
      |> certify pp tsig (consts |> expand_abbrevs false);
    val rhs' = rhs
      |> certify pp tsig (consts |> expand_abbrevs true);
    val T = Term.fastype_of rhs;
  in
    consts |> map_consts (fn (decls, constraints, rev_abbrevs, expand_abbrevs) =>
      let
        val decls' = decls
          |> extend_decls naming (c, (((T, Abbreviation rhs'), authentic), stamp ()));
        val rev_abbrevs' = rev_abbrevs
          |> fold (curry Symtab.update_list mode) (rev_abbrev (NameSpace.full naming c, T) rhs);
      in (decls', constraints, rev_abbrevs', expand_abbrevs) end)
  end;

end;


(* empty and merge *)

val empty = make_consts (NameSpace.empty_table, Symtab.empty, Symtab.empty, true);

fun merge
   (Consts ({decls = decls1, constraints = constraints1,
      rev_abbrevs = rev_abbrevs1, expand_abbrevs = expand_abbrevs1}, _),
    Consts ({decls = decls2, constraints = constraints2,
      rev_abbrevs = rev_abbrevs2, expand_abbrevs = expand_abbrevs2}, _)) =
  let
    val decls' = NameSpace.merge_tables (eq_snd (op =)) (decls1, decls2)
      handle Symtab.DUPS cs => err_dup_consts cs;
    val constraints' = Symtab.merge (op =) (constraints1, constraints2)
      handle Symtab.DUPS cs => err_inconsistent_constraints cs;
    val rev_abbrevs' = (rev_abbrevs1, rev_abbrevs2) |> Symtab.join
      (K (Library.merge (fn ((t, u), (t', u')) => t aconv t' andalso u aconv u')));
    val expand_abbrevs' = expand_abbrevs1 orelse expand_abbrevs2;
  in make_consts (decls', constraints', rev_abbrevs', expand_abbrevs') end;

end;
