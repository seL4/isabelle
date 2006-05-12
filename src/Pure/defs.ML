(*  Title:      Pure/defs.ML
    ID:         $Id$
    Author:     Makarius

Global well-formedness checks for constant definitions.  Covers
dependencies of simple sub-structural overloading, where type
arguments are approximated by the outermost type constructor.
*)

signature DEFS =
sig
  type T
  val specifications_of: T -> string ->
   (serial * {is_def: bool, module: string, name: string, lhs: typ, rhs: (string * typ) list}) list
  val empty: T
  val merge: T * T -> T
  val define: (string * typ -> typ list) ->
    bool -> string -> string -> string * typ -> (string * typ) list -> T -> T
end

structure Defs: DEFS =
struct

(* dependency items *)

(*
  Constant c covers all instances of c

  Instance (c, a) covers all instances of applications (c, [Type (a, _)])

  Different Constant/Constant or Instance/Instance items represent
  disjoint sets of instances.  The set Constant c subsumes any
  Instance (c, a) -- dependencies are propagated accordingly.
*)

datatype item =
  Constant of string |
  Instance of string * string;

fun make_item (c, [Type (a, _)]) = Instance (c, a)
  | make_item (c, _) = Constant c;

fun pretty_item (Constant c) = Pretty.str (quote c)
  | pretty_item (Instance (c, a)) = Pretty.str (quote c ^ " (type " ^ quote a ^ ")");

fun item_ord (Constant c, Constant c') = fast_string_ord (c, c')
  | item_ord (Instance ca, Instance ca') = prod_ord fast_string_ord fast_string_ord (ca, ca')
  | item_ord (Constant _, Instance _) = LESS
  | item_ord (Instance _, Constant _) = GREATER;

structure Items = GraphFun(type key = item val ord = item_ord);

fun declare_edge (i, j) =
  Items.default_node (i, ()) #>
  Items.default_node (j, ()) #>
  Items.add_edge_acyclic (i, j);

fun propagate_deps insts deps =
  let
    fun inst_item (Constant c) = Symtab.lookup_list insts c
      | inst_item (Instance _) = [];
    fun inst_edge i j =
      fold declare_edge (tl (product (i :: inst_item i) (j :: inst_item j)));
  in Items.fold (fn (i, (_, (_, js))) => fold (inst_edge i) js) deps deps end;


(* specifications *)

type spec = {is_def: bool, module: string, name: string, lhs: typ, rhs: (string * typ) list};

datatype T = Defs of
 {specs: (bool * spec Inttab.table) Symtab.table,
  insts: item list Symtab.table,
  deps: unit Items.T};

fun no_overloading_of (Defs {specs, ...}) c =
  (case Symtab.lookup specs c of
    SOME (b, _) => b
  | NONE => false);

fun specifications_of (Defs {specs, ...}) c =
  (case Symtab.lookup specs c of
    SOME (_, sps) => Inttab.dest sps
  | NONE => []);

fun make_defs (specs, insts, deps) = Defs {specs = specs, insts = insts, deps = deps};
fun map_defs f (Defs {specs, insts, deps}) = make_defs (f (specs, insts, deps));

val empty = make_defs (Symtab.empty, Symtab.empty, Items.empty);


(* disjoint specs *)

fun disjoint_types T U =
  (Type.raw_unify (T, Logic.incr_tvar (maxidx_of_typ T + 1) U) Vartab.empty; false)
    handle Type.TUNIFY => true;

fun disjoint_specs c (i, {lhs = T, name = a, ...}: spec) =
  Inttab.forall (fn (j, {lhs = U, name = b, ...}: spec) =>
    i = j orelse not (Type.could_unify (T, U)) orelse disjoint_types T U orelse
      error ("Type clash in specifications " ^ quote a ^ " and " ^ quote b ^
        " for constant " ^ quote c));


(* merge *)

fun cycle_msg css =
  let
    fun prt_cycle items = Pretty.block (flat
      (separate [Pretty.str " ->", Pretty.brk 1] (map (single o pretty_item) items)));
  in Pretty.string_of (Pretty.big_list "Cyclic dependency of constants:" (map prt_cycle css)) end;

fun merge
   (Defs {specs = specs1, insts = insts1, deps = deps1},
    Defs {specs = specs2, insts = insts2, deps = deps2}) =
  let
    val specs' = (specs1, specs2) |> Symtab.join (fn c => fn ((b, sps1), (_, sps2)) =>
      (b, Inttab.fold (fn sp2 => (disjoint_specs c sp2 sps1; Inttab.update sp2)) sps2 sps1));
    val insts' = Symtab.merge_list (op =) (insts1, insts2);
    val items' = propagate_deps insts' (Items.merge_acyclic (K true) (deps1, deps2))
      handle Items.CYCLES cycles => error (cycle_msg cycles);
  in make_defs (specs', insts', items') end;


(* define *)

fun pure_args args = forall Term.is_TVar args andalso not (has_duplicates (op =) args);

fun define const_typargs is_def module name lhs rhs defs = defs
    |> map_defs (fn (specs, insts, deps) =>
  let
    val (c, T) = lhs;
    val args = const_typargs lhs;
    val no_overloading = pure_args args;
    val rec_args = (case args of [Type (_, Ts)] => if pure_args Ts then Ts else [] | _ => []);

    val spec = (serial (), {is_def = is_def, module = module, name = name, lhs = T, rhs = rhs});
    val specs' = specs
      |> Symtab.default (c, (false, Inttab.empty))
      |> Symtab.map_entry c (fn (_, sps) =>
          (disjoint_specs c spec sps; (no_overloading, Inttab.update spec sps)));

    val lhs' = make_item (c, args);
    val rhs' = rhs |> map_filter (fn (c', T') =>
      let val args' = const_typargs (c', T') in
        if gen_subset (op =) (args', rec_args) then NONE
        else SOME (make_item (c', if no_overloading_of defs c' then [] else args'))
      end);

    val insts' = insts |> fold (fn i as Instance (c, _) =>
        Symtab.insert_list (op =) (c, i) | _ => I) (lhs' :: rhs');
    val deps' = deps
      |> fold (fn r => declare_edge (r, lhs')) rhs'
      |> propagate_deps insts'
      handle Items.CYCLES cycles =>
        if no_overloading then error (cycle_msg cycles)
        else (warning (cycle_msg cycles ^ "\nUnchecked overloaded specification: " ^ name); deps);

  in (specs', insts', deps') end);

end;
