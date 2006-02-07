(*  Title:      Pure/consts.ML
    ID:         $Id$
    Author:     Makarius

Polymorphic constants: declarations, abbreviations, additional type
constraints.
*)

signature CONSTS =
sig
  type T
  val dest: T ->
   {constants: (typ * term option) NameSpace.table,
    constraints: typ NameSpace.table}
  val space_of: T -> NameSpace.T
  val abbrevs_of: T -> (term * term) list
  val declaration: T -> string -> typ                           (*exception TYPE*)
  val monomorphic: T -> string -> bool                          (*exception TYPE*)
  val constraint: T -> string -> typ                            (*exception TYPE*)
  val certify: Pretty.pp -> Type.tsig -> T -> term -> term      (*exception TYPE*)
  val read_const: T -> string -> term
  val typargs: T -> string * typ -> typ list
  val instance: T -> string * typ list -> typ
  val declare: NameSpace.naming -> bstring * typ -> T -> T
  val abbreviate: Pretty.pp -> Type.tsig -> NameSpace.naming -> bool -> string * term -> T -> T
  val constrain: string * typ -> T -> T
  val hide: bool -> string -> T -> T
  val empty: T
  val merge: T * T -> T
end

structure Consts: CONSTS =
struct

(** datatype T **)

datatype decl =
  LogicalConst of typ * int list list |
  Abbreviation of typ * term;

datatype T = Consts of
 {decls: (decl * serial) NameSpace.table,
  abbrevs: (term * term) list,
  constraints: typ Symtab.table};

fun make_consts (decls, abbrevs, constraints) =
  Consts {decls = decls, abbrevs = abbrevs, constraints = constraints};

fun map_consts f (Consts {decls, abbrevs, constraints}) =
  make_consts (f (decls, abbrevs, constraints));

fun dest (Consts {decls = (space, decls), abbrevs = _, constraints}) =
 {constants = (space, Symtab.fold
    (fn (c, (LogicalConst (T, _), _)) => Symtab.update (c, (T, NONE))
      | (c, (Abbreviation (T, t), _)) => Symtab.update (c, (T, SOME t))) decls Symtab.empty),
  constraints = (space, constraints)};

fun space_of (Consts {decls = (space, _), ...}) = space;
fun abbrevs_of (Consts {abbrevs, ...}) = abbrevs;


(* lookup consts *)

fun err_undeclared c = raise TYPE ("Undeclared constant: " ^ quote c, [], []);

fun the_const (Consts {decls = (_, tab), ...}) c =
  (case Symtab.lookup tab c of SOME (decl, _) => decl | NONE => err_undeclared c);

fun logical_const consts c =
  (case the_const consts c of LogicalConst d => d | _ => err_undeclared c);

fun declaration consts c = #1 (logical_const consts c);
fun monomorphic consts c = null (#2 (logical_const consts c));

fun constraint (consts as Consts {constraints, ...}) c =
  (case Symtab.lookup constraints c of
    SOME T => T
  | NONE => (case the_const consts c of LogicalConst (T, _) => T | Abbreviation (T, _) => T));


(* certify: check/expand consts *)

fun certify pp tsig consts =
  let
    fun err msg (c, T) =
      raise TYPE (msg ^ " " ^ quote c ^ " :: " ^ Pretty.string_of_typ pp T, [], []);
    fun cert tm =
      let
        val (head, args) = Term.strip_comb tm;
        val args' = map cert args;
      in
        (case head of
          Const (c, T) =>
            (case the_const consts c of
              LogicalConst (U, _) =>
                if Type.typ_instance tsig (T, U) then Term.list_comb (head, args')
                else err "Illegal type for constant" (c, T)
            | Abbreviation (U, u) =>
                Term.betapplys (Envir.expand_atom tsig T (U, u) handle TYPE _ =>
                  err "Illegal type for abbreviation" (c, T), args'))
        | Abs (x, T, t) => Term.list_comb (Abs (x, T, cert t), args')
        | _ => Term.list_comb (head, args'))
      end;
  in cert end;


(* read_const *)

fun read_const consts raw_c =
  let
    val c = NameSpace.intern (space_of consts) raw_c;
    val _ = the_const consts c handle TYPE (msg, _, _) => error msg;
  in Const (c, dummyT) end;


(* typargs -- view actual const type as instance of declaration *)

fun sub (Type (_, Ts)) (i :: is) = sub (nth Ts i) is
  | sub T [] = T
  | sub T _ = raise Subscript;

fun typargs consts (c, T) = map (sub T) (#2 (logical_const consts c));

fun instance consts (c, Ts) =
  let
    val declT = declaration consts c;
    val vars = map Term.dest_TVar (typargs consts (c, declT));
  in declT |> Term.instantiateT (vars ~~ Ts) end;



(** declare consts **)

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);

fun err_inconsistent_constraints cs =
  error ("Inconsistent type constraints for constant(s) " ^ commas_quote cs);

fun extend_decls naming decl tab = NameSpace.extend_table naming (tab, [decl])
  handle Symtab.DUPS cs => err_dup_consts cs;


(* name space *)

fun hide fully c = map_consts (fn (decls, abbrevs, constraints) =>
  (apfst (NameSpace.hide fully c) decls, abbrevs, constraints));


(* declarations *)

fun declare naming (c, declT) = map_consts (fn (decls, abbrevs, constraints) =>
  let
    fun args_of (Type (_, Ts)) pos = args_of_list Ts 0 pos
      | args_of (TVar v) pos = insert (eq_fst op =) (v, rev pos)
      | args_of (TFree _) _ = I
    and args_of_list (T :: Ts) i is = args_of T (i :: is) #> args_of_list Ts (i + 1) is
      | args_of_list [] _ _ = I;
    val decl = (c, (LogicalConst (declT, map #2 (rev (args_of declT [] []))), serial ()));
  in (extend_decls naming decl decls, abbrevs, constraints) end);


(* abbreviations *)

fun revert_abbrev const rhs =
  let
    val (xs, body) = Term.strip_abs (Envir.beta_eta_contract rhs);
    val vars = fold (fn (x, T) => cons (Var ((x, 0), T))) (Term.rename_wrt_term body xs) [];
  in (Term.list_comb (Const const, vars), Term.subst_bounds (rev vars, body)) end;

fun abbreviate pp tsig naming revert (c, raw_rhs) consts =
    consts |> map_consts (fn (decls, abbrevs, constraints) =>
  let
    val rhs = certify pp tsig consts raw_rhs;
    val T = Term.fastype_of rhs;
    val decls' = decls |> extend_decls naming (c, (Abbreviation (T, rhs), serial ()));
    val abbrevs' =
      if revert then revert_abbrev (NameSpace.full naming c, T) rhs :: abbrevs else abbrevs;
  in (decls', abbrevs', constraints) end);


(* constraints *)

fun constrain (c, T) = map_consts (fn (decls, abbrevs, constraints) =>
  (decls, abbrevs, Symtab.update (c, T) constraints));


(* empty and merge *)

val empty = make_consts (NameSpace.empty_table, [], Symtab.empty);

fun merge
   (Consts {decls = decls1, abbrevs = abbrevs1, constraints = constraints1},
    Consts {decls = decls2, abbrevs = abbrevs2, constraints = constraints2}) =
  let
    val decls' = NameSpace.merge_tables (eq_snd (op =)) (decls1, decls2)
      handle Symtab.DUPS cs => err_dup_consts cs;
    val abbrevs' =
      Library.merge (fn ((t, u), (t', u')) => t aconv t' andalso u aconv u') (abbrevs1, abbrevs2);
    val constraints' = Symtab.merge (op =) (constraints1, constraints2)
      handle Symtab.DUPS cs => err_inconsistent_constraints cs;
  in make_consts (decls', abbrevs', constraints') end;

end;
