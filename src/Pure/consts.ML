(*  Title:      Pure/consts.ML
    ID:         $Id$
    Author:     Makarius

Polymorphic constants.
*)

signature CONSTS =
sig
  type T
  val dest: T -> {declarations: typ NameSpace.table, constraints: typ NameSpace.table}
  val space: T -> NameSpace.T
  val declaration: T -> string -> typ  (*exception TYPE*)
  val constraint: T -> string -> typ    (*exception TYPE*)
  val monomorphic: T -> string -> bool
  val typargs: T -> string -> typ -> typ list
  val declare: NameSpace.naming -> bstring * typ -> T -> T
  val constrain: string * typ -> T -> T
  val hide: bool -> string -> T -> T
  val empty: T
  val merge: T * T -> T
end

structure Consts: CONSTS =
struct


(** datatype T **)

type arg = (indexname * sort) * int list;  (*type variable with first occurrence*)

datatype T = Consts of
 {declarations: ((typ * arg list) * serial) NameSpace.table,
  constraints: typ Symtab.table};

fun make_consts (declarations, constraints) =
  Consts {declarations = declarations, constraints = constraints};

fun map_consts f (Consts {declarations, constraints}) =
  make_consts (f (declarations, constraints));

fun dest (Consts {declarations = (space, decls), constraints}) =
 {declarations = (space, Symtab.map (#1 o #1) decls),
  constraints = (space, constraints)};

fun space (Consts {declarations = (space, _), ...}) = space;


(* lookup consts *)

fun the_const (Consts {declarations = (_, decls), ...}) c =
  (case Symtab.lookup decls c of SOME (decl, _) => decl
  | NONE => raise TYPE ("Undeclared constant " ^ quote c, [], []));

fun declaration consts c = #1 (the_const consts c);

fun constraint (consts as Consts {constraints, ...}) c =
  (case Symtab.lookup constraints c of
    SOME T => T
  | NONE => declaration consts c);

fun monomorphic consts c = null (#2 (the_const consts c));


(* typargs -- view actual const type as instance of declaration *)

fun sub (Type (_, Ts)) (i :: is) = sub (nth Ts i) is
  | sub T [] = T
  | sub T _ = raise Subscript;

fun typargs consts c =
  let val (_, args) = the_const consts c
  in fn T => map (sub T o #2) args end;



(** build consts **)

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);

fun err_inconsistent_constraints cs =
  error ("Inconsistent type constraints for constant(s) " ^ commas_quote cs);


(* declarations etc. *)

fun args_of declT =
  let
    fun args (Type (_, Ts)) pos = args_list Ts 0 pos
      | args (TVar v) pos = insert (eq_fst op =) (v, rev pos)
      | args (TFree _) _ = I
    and args_list (T :: Ts) i is = args T (i :: is) #> args_list Ts (i + 1) is
      | args_list [] _ _ = I;
  in rev (args declT [] []) end;

fun declare naming (c, T) = map_consts (apfst (fn declarations =>
  let
    val decl = (c, ((T, args_of T), serial ()));
    val declarations' = NameSpace.extend_table naming (declarations, [decl])
      handle Symtab.DUPS cs => err_dup_consts cs;
  in declarations' end));

val constrain = map_consts o apsnd o Symtab.update;

fun hide fully c = map_consts (apfst (apfst (NameSpace.hide fully c)));


(* empty and merge *)

val empty = make_consts (NameSpace.empty_table, Symtab.empty);

fun merge
  (Consts {declarations = declarations1, constraints = constraints1},
   Consts {declarations = declarations2, constraints = constraints2}) =
  let
    val declarations = NameSpace.merge_tables (eq_snd (op =)) (declarations1, declarations2)
      handle Symtab.DUPS cs => err_dup_consts cs;
    val constraints = Symtab.merge (op =) (constraints1, constraints2)
      handle Symtab.DUPS cs => err_inconsistent_constraints cs;
  in make_consts (declarations, constraints) end;

end;
