(*  Title:      Pure/defs.ML
    ID:         $Id$
    Author:     Makarius

Global well-formedness checks for constant definitions.  Dependencies
are only tracked for non-overloaded definitions!
*)

signature DEFS =
sig
  type T
  val define: (string -> typ) -> bool -> string -> string ->
    string * typ -> (string * typ) list -> T -> T
  val empty: T
  val specifications_of: T -> string ->
   (serial * {is_def: bool, module: string, name: string, lhs: typ, rhs: (string * typ) list}) list
  val merge: Pretty.pp -> T * T -> T
end

structure Defs: DEFS =
struct


(** datatype T **)

type spec = {is_def: bool, module: string, name: string, lhs: typ, rhs: (string * typ) list};

datatype T = Defs of
 {consts: typ Graph.T,
    (*constant declarations and dependencies*)
  specified: spec Inttab.table Symtab.table};

fun make_defs (consts, specified) = Defs {consts = consts, specified = specified};
fun map_defs f (Defs {consts, specified}) = make_defs (f (consts, specified));


(* specified consts *)

fun disjoint_types T U =
  (Type.raw_unify (T, Logic.incr_tvar (maxidx_of_typ T + 1) U) Vartab.empty; false)
    handle Type.TUNIFY => true;

fun check_specified c (i, {lhs = T, name = a, ...}: spec) =
  Inttab.forall (fn (j, {lhs = U, name = b, ...}: spec) =>
    i = j orelse not (Type.could_unify (T, U)) orelse disjoint_types T U orelse
      error ("Type clash in specifications " ^ quote a ^ " and " ^ quote b ^
        " for constant " ^ quote c));


(* define consts *)

fun err_cyclic cycles =
  error ("Cyclic dependency of constants:\n" ^
    cat_lines (map (space_implode " -> " o map quote o rev) cycles));

fun define const_type is_def module name lhs rhs = map_defs (fn (consts, specified) =>
  let
    fun declare (a, _) = Graph.default_node (a, const_type a);
    fun add_deps (a, bs) G = Graph.add_deps_acyclic (a, bs) G
      handle Graph.CYCLES cycles => err_cyclic cycles;

    val (c, T) = lhs;
    val spec = (serial (), {is_def = is_def, module = module, name = name, lhs = T, rhs = rhs});
    val no_overloading = Type.raw_instance (const_type c, T);

    val consts' =
      consts |> declare lhs |> fold declare rhs
      |> K no_overloading ? add_deps (c, map #1 rhs);
    val specified' = specified
      |> Symtab.default (c, Inttab.empty)
      |> Symtab.map_entry c (fn specs =>
        (check_specified c spec specs; Inttab.update spec specs));
  in (consts', specified') end);

fun specifications_of (Defs {specified, ...}) c =
  Inttab.dest (the_default Inttab.empty (Symtab.lookup specified c));


(* empty and merge *)

val empty = make_defs (Graph.empty, Symtab.empty);

fun merge pp
   (Defs {consts = consts1, specified = specified1},
    Defs {consts = consts2, specified = specified2}) =
  let
    val consts' = (consts1, consts2) |> Graph.merge_acyclic (K true)
      handle Graph.CYCLES cycles => err_cyclic cycles;
    val specified' = (specified1, specified2) |> Symtab.join (fn c => fn (orig_specs1, specs2) =>
      Inttab.fold (fn spec2 => fn specs1 =>
        (check_specified c spec2 orig_specs1; Inttab.update spec2 specs1)) specs2 orig_specs1);
  in make_defs (consts', specified') end;

end;
