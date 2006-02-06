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
  val space: T -> NameSpace.T
  val declaration: T -> string -> typ                           (*exception TYPE*)
  val monomorphic: T -> string -> bool                          (*exception TYPE*)
  val constraint: T -> string -> typ                            (*exception TYPE*)
  val expansion: Type.tsig -> T -> string * typ -> term option  (*exception TYPE*)
  val certify: Pretty.pp -> Type.tsig -> T -> term -> term      (*exception TYPE*)
  val typargs: T -> string * typ -> typ list
  val instance: T -> string * typ list -> typ
  val declare: NameSpace.naming -> bstring * typ -> T -> T
  val abbreviate: Pretty.pp -> Type.tsig -> NameSpace.naming -> string * term -> T -> T
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
  constraints: typ Symtab.table};

fun make_consts (decls, constraints) = Consts {decls = decls, constraints = constraints};
fun map_consts f (Consts {decls, constraints}) = make_consts (f (decls, constraints));

fun dest (Consts {decls = (space, decls), constraints}) =
 {constants = (space, Symtab.fold
    (fn (c, (LogicalConst (T, _), _)) => Symtab.update (c, (T, NONE))
      | (c, (Abbreviation (T, t), _)) => Symtab.update (c, (T, SOME t))) decls Symtab.empty),
  constraints = (space, constraints)};

fun space (Consts {decls, ...}) = #1 decls;


(* lookup consts *)

fun err_undeclared c = raise TYPE ("Undeclared constant: " ^ quote c, [], []);

fun the_const (Consts {decls = (_, tab), ...}) c =
  (case Symtab.lookup tab c of SOME (decl, _) => decl | NONE => err_undeclared c);

fun logical_const consts c =
  (case the_const consts c of LogicalConst d => d | _ => err_undeclared c);

fun declaration consts c = #1 (logical_const consts c);
fun monomorphic consts c = null (#2 (logical_const consts c));

fun expansion tsig consts (c, T) =
  (case the_const consts c of
    Abbreviation a => SOME (Envir.expand_atom tsig T a)
  | _ => NONE);

fun constraint (consts as Consts {constraints, ...}) c =
  (case Symtab.lookup constraints c of
    SOME T => T
  | NONE => (case the_const consts c of LogicalConst (T, _) => T | Abbreviation (T, _) => T));


(* certify: check/expand consts -- without beta normalization *)

fun certify pp tsig consts tm =
  let
    fun err msg = raise TYPE (msg, [], [tm]);
    fun show_const (c, T) = quote c ^ " :: " ^ Pretty.string_of_typ pp T;

    fun cert (t as Const (c, T)) =
          (case the_const consts c of
            LogicalConst (U, _) =>
              if Type.typ_instance tsig (T, U) then t
              else err ("Illegal type for constant " ^ show_const (c, T))
          | Abbreviation (U, u) =>
              Envir.expand_atom tsig T (U, u) handle TYPE _ =>
                err ("Illegal type for abbreviation " ^ show_const (c, T)))
      | cert (t $ u) = cert t $ cert u
      | cert (Abs (x, T, t)) = Abs (x, T, cert t)
      | cert a = a;
  in cert tm end;


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

fun hide fully c = map_consts (fn (decls, constraints) =>
  (apfst (NameSpace.hide fully c) decls, constraints));


(* declarations *)

fun declare naming (c, declT) = map_consts (fn (decls, constraints) =>
  let
    fun args_of (Type (_, Ts)) pos = args_of_list Ts 0 pos
      | args_of (TVar v) pos = insert (eq_fst op =) (v, rev pos)
      | args_of (TFree _) _ = I
    and args_of_list (T :: Ts) i is = args_of T (i :: is) #> args_of_list Ts (i + 1) is
      | args_of_list [] _ _ = I;
    val decl = (c, (LogicalConst (declT, map #2 (rev (args_of declT [] []))), serial ()));
  in (extend_decls naming decl decls, constraints) end);


(* abbreviations *)

fun abbreviate pp tsig naming (c, rhs) consts =
    consts |> map_consts (fn (decls, constraints) =>
  let
    val rhs' = Envir.beta_norm (certify pp tsig consts rhs);
    val decl = (c, (Abbreviation (Term.fastype_of rhs', rhs'), serial ()));
  in (extend_decls naming decl decls, constraints) end);


(* constraints *)

fun constrain (c, T) =
  map_consts (fn (decls, constraints) => (decls, Symtab.update (c, T) constraints));


(* empty and merge *)

val empty = make_consts (NameSpace.empty_table, Symtab.empty);

fun merge
  (Consts {decls = decls1, constraints = constraints1},
   Consts {decls = decls2, constraints = constraints2}) =
  let
    val decls' = NameSpace.merge_tables (eq_snd (op =)) (decls1, decls2)
      handle Symtab.DUPS cs => err_dup_consts cs;
    val constraints' = Symtab.merge (op =) (constraints1, constraints2)
      handle Symtab.DUPS cs => err_inconsistent_constraints cs;
  in make_consts (decls', constraints') end;

end;
