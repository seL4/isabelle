(*  Title:      Pure/defs.ML
    ID:         $Id$
    Author:     Makarius

Global well-formedness checks for constant definitions.  Dependencies
are only tracked for non-overloaded definitions!
*)

signature DEFS =
sig
  type T
  val monomorphic: T -> string -> bool
  val define: string -> string * typ -> (string * typ) list -> T -> T
  val empty: T
  val merge: Pretty.pp -> T * T -> T
end

structure Defs (* FIXME : DEFS *) =
struct

(** datatype T **)

datatype T = Defs of
 {consts: typ Graph.T,                                 (*constant declarations and dependencies*)
  specified: (string * typ) Inttab.table Symtab.table, (*specification name and const type*)
  monomorphic: unit Symtab.table};                     (*constants having monomorphic specs*)

fun rep_defs (Defs args) = args;

fun make_defs (consts, specified, monomorphic) =
  Defs {consts = consts, specified = specified, monomorphic = monomorphic};

fun map_defs f (Defs {consts, specified, monomorphic}) =
  make_defs (f (consts, specified, monomorphic));


(* specified consts *)

fun disjoint_types T U =
  (Type.raw_unify (T, Logic.incr_tvar (maxidx_of_typ T + 1) U) Vartab.empty; false)
    handle Type.TUNIFY => true;

fun check_specified c specified =
  specified |> Inttab.forall (fn (i, (a, T)) =>
    specified |> Inttab.forall (fn (j, (b, U)) =>
      i = j orelse disjoint_types T U orelse
        error ("Type clash in specifications " ^ quote a ^ " and " ^ quote b ^
          " for constant " ^ quote c)));


(* monomorphic constants *)

val monomorphic = Symtab.defined o #monomorphic o rep_defs;

fun update_monomorphic specified c =
  let
    val specs = the_default Inttab.empty (Symtab.lookup specified c);
    fun is_monoT (Type (_, Ts)) = forall is_monoT Ts
      | is_monoT _ = false;
    val is_mono =
      Inttab.is_empty specs orelse
        Inttab.min_key specs = Inttab.max_key specs andalso
        is_monoT (snd (the (Inttab.lookup specs (the (Inttab.min_key specs)))));
  in if is_mono then Symtab.update (c, ()) else Symtab.remove (K true) (c, ()) end;


(* define consts *)

fun err_cyclic cycles =
  error ("Cyclic dependency of constants:\n" ^
    cat_lines (map (space_implode " -> " o map quote o rev) cycles));

fun define const_type name lhs rhs = map_defs (fn (consts, specified, monomorphic) =>
  let
    fun declare (a, _) = Graph.default_node (a, const_type a);
    fun add_deps (a, bs) G = Graph.add_deps_acyclic (a, bs) G
      handle Graph.CYCLES cycles => err_cyclic cycles;

    val (c, T) = lhs;
    val no_overloading = Type.raw_instance (const_type c, T);

    val consts' =
      consts |> declare lhs |> fold declare rhs
      |> K no_overloading ? add_deps (c, map #1 rhs);
    val specified' =
      specified |> Symtab.default (c, Inttab.empty)
      |> Symtab.map_entry c (Inttab.update (serial (), (name, T)) #> tap (check_specified c));
    val monomorphic' = monomorphic |> update_monomorphic specified' c;
  in (consts', specified', monomorphic') end);


(* empty and merge *)

val empty = make_defs (Graph.empty, Symtab.empty, Symtab.empty);

fun merge pp
   (Defs {consts = consts1, specified = specified1, monomorphic},
    Defs {consts = consts2, specified = specified2, ...}) =
  let
    val consts' = (consts1, consts2) |> Graph.merge_acyclic (K true)
      handle Graph.CYCLES cycles => err_cyclic cycles;
    val specified' = (specified1, specified2)
      |> Symtab.join (fn c => Inttab.merge (K true) #> tap (check_specified c) #> SOME);
    val monomorphic' = monomorphic
      |> Symtab.fold (update_monomorphic specified' o #1) specified';
  in make_defs (consts', specified', monomorphic') end;

end;
