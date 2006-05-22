(*  Title:      Pure/defs.ML
    ID:         $Id$
    Author:     Makarius

Global well-formedness checks for constant definitions.  Covers plain
definitions and simple sub-structural overloading (depending on a
single type argument).
*)

signature DEFS =
sig
  val pretty_const: Pretty.pp -> string * typ list -> Pretty.T
  type T
  val specifications_of: T -> string -> (serial * {is_def: bool, module: string, name: string,
    lhs: typ list, rhs: (string * typ list) list}) list
  val dest: T ->
   {restricts: ((string * typ list) * string) list,
    reducts: ((string * typ list) * (string * typ list) list) list}
  val empty: T
  val merge: Pretty.pp -> T * T -> T
  val define: Pretty.pp -> Consts.T ->
    bool -> bool -> string -> string -> string * typ -> (string * typ) list -> T -> T
end

structure Defs: DEFS =
struct


(* type arguments *)

type args = typ list;

fun pretty_const pp (c, args) =
  let
    val prt_args =
      if null args then []
      else [Pretty.list "(" ")" (map (Pretty.typ pp o Type.freeze_type) args)];
  in Pretty.block (Pretty.str c :: prt_args) end;

fun disjoint_args (Ts, Us) =
  not (Type.could_unifys (Ts, Us)) orelse
    ((Type.raw_unifys (Ts, map (Logic.incr_tvar (maxidx_of_typs Ts + 1)) Us) Vartab.empty; false)
      handle Type.TUNIFY => true);

fun match_args (Ts, Us) =
  Option.map Envir.typ_subst_TVars
    (SOME (Type.raw_matches (Ts, Us) Vartab.empty) handle Type.TYPE_MATCH => NONE);


(* datatype defs *)

type spec = {is_def: bool, module: string, name: string, lhs: args, rhs: (string * args) list};

type def =
 {specs: spec Inttab.table,
  restricts: (args * string) list,
  reducts: (args * (string * args) list) list};

fun make_def (specs, restricts, reducts) =
  {specs = specs, restricts = restricts, reducts = reducts}: def;

fun map_def c f =
  Symtab.default (c, make_def (Inttab.empty, [], [])) #>
  Symtab.map_entry c (fn {specs, restricts, reducts}: def =>
    make_def (f (specs, restricts, reducts)));


datatype T = Defs of def Symtab.table;

fun lookup_list which (Defs defs) c =
  (case Symtab.lookup defs c of
    SOME def => which def
  | NONE => []);

val specifications_of = lookup_list (Inttab.dest o #specs);
val restricts_of = lookup_list #restricts;
val reducts_of = lookup_list #reducts;

fun dest (Defs defs) =
  let
    val restricts = Symtab.fold (fn (c, {restricts, ...}) =>
      fold (fn (args, name) => cons ((c, args), name)) restricts) defs [];
    val reducts = Symtab.fold (fn (c, {reducts, ...}) =>
      fold (fn (args, deps) => cons ((c, args), deps)) reducts) defs [];
  in {restricts = restricts, reducts = reducts} end;

val empty = Defs Symtab.empty;


(* specifications *)

fun disjoint_specs c (i, {lhs = Ts, name = a, ...}: spec) =
  Inttab.forall (fn (j, {lhs = Us, name = b, ...}: spec) =>
    i = j orelse disjoint_args (Ts, Us) orelse
      error ("Type clash in specifications " ^ quote a ^ " and " ^ quote b ^
        " for constant " ^ quote c));

fun join_specs c ({specs = specs1, restricts, reducts}, {specs = specs2, ...}: def) =
  let
    val specs' =
      Inttab.fold (fn spec2 => (disjoint_specs c spec2 specs1; Inttab.update spec2)) specs2 specs1;
  in make_def (specs', restricts, reducts) end;

fun update_specs c spec = map_def c (fn (specs, restricts, reducts) =>
  (disjoint_specs c spec specs; (Inttab.update spec specs, restricts, reducts)));


(* normalization: reduction and well-formedness check *)

local

fun reduction reds_of deps =
  let
    fun reduct Us (Ts, rhs) =
      (case match_args (Ts, Us) of
        NONE => NONE
      | SOME subst => SOME (map (apsnd (map subst)) rhs));
    fun reducts (d: string, Us) = get_first (reduct Us) (reds_of d);

    fun add (NONE, dp) = insert (op =) dp
      | add (SOME dps, _) = fold (insert (op =)) dps;
    val deps' = map (`reducts) deps;
  in
    if forall (is_none o #1) deps' then NONE
    else SOME (fold_rev add deps' [])
  end;

fun reductions reds_of deps =
  (case reduction reds_of deps of
    SOME deps' => reductions reds_of deps'
  | NONE => deps);

fun contained U (Type (_, Ts)) = exists (fn T => T = U orelse contained U T) Ts
  | contained _ _ = false;

fun wellformed pp rests_of (c, args) (d, Us) =
  let
    val prt = Pretty.string_of o pretty_const pp;
    fun err s1 s2 =
      error (s1 ^ " dependency of constant " ^ prt (c, args) ^ " -> " ^ prt (d, Us) ^ s2);
  in
    exists (fn U => exists (contained U) args) Us orelse
    (c <> d andalso exists (member (op =) args) Us) orelse
      (case find_first (fn (Ts, _) => not (disjoint_args (Ts, Us))) (rests_of d) of
        NONE =>
          c <> d orelse is_none (match_args (args, Us)) orelse err "Circular" ""
      | SOME (Ts, name) =>
          if c = d then err "Circular" ("\n(via " ^ quote name ^ ")")
          else
            err "Malformed" ("\n(restriction " ^ prt (d, Ts) ^ " from " ^ quote name ^ ")"))
  end;

fun normalize pp rests_of reds_of (c, args) deps =
  let
    val deps' = reductions reds_of deps;
    val _ = forall (wellformed pp rests_of (c, args)) deps';
  in deps' end;

fun normalize_all pp (c, args) deps defs =
  let
    val norm = normalize pp (restricts_of (Defs defs));
    val norm_rule = norm (fn c' => if c' = c then [(args, deps)] else []);
    val norm_defs = norm (reducts_of (Defs defs));
    fun norm_update (c', {reducts, ...}: def) =
      let val reducts' = reducts
        |> map (fn (args', deps') => (args', norm_defs (c', args') (norm_rule (c', args') deps')))
      in
        K (reducts <> reducts') ?
          map_def c' (fn (specs, restricts, reducts) => (specs, restricts, reducts'))
      end;
  in Symtab.fold norm_update defs defs end;

in

fun dependencies pp (c, args) restr deps (Defs defs) =
  let
    val deps' = normalize pp (restricts_of (Defs defs)) (reducts_of (Defs defs)) (c, args) deps;
    val defs' = defs
      |> map_def c (fn (specs, restricts, reducts) =>
        (specs, Library.merge (op =) (restricts, restr), reducts))
      |> normalize_all pp (c, args) deps';
    val deps'' =
      normalize pp (restricts_of (Defs defs')) (reducts_of (Defs defs')) (c, args) deps';
    val defs'' = defs'
      |> map_def c (fn (specs, restricts, reducts) =>
        (specs, restricts, insert (op =) (args, deps'') reducts));
  in Defs defs'' end;

end;


(* merge *)

fun merge pp (Defs defs1, Defs defs2) =
  let
    fun add_deps (c, args) restr deps defs =
      if AList.defined (op =) (reducts_of defs c) args then defs
      else dependencies pp (c, args) restr deps defs;
    fun add_def (c, {restricts, reducts, ...}: def) =
      fold (fn (args, deps) => add_deps (c, args) restricts deps) reducts;
  in Defs (Symtab.join join_specs (defs1, defs2)) |> Symtab.fold add_def defs2 end;

local  (* FIXME *)
  val merge_aux = merge
  val acc = Output.time_accumulator "Defs.merge"
in fun merge pp = acc (merge_aux pp) end;


(* define *)

fun plain_args args =
  forall Term.is_TVar args andalso not (has_duplicates (op =) args);

fun define pp consts unchecked is_def module name lhs rhs (Defs defs) =
  let
    fun typargs const = (#1 const, Consts.typargs consts const);
    val (c, args) = typargs lhs;
    val deps = map typargs rhs;
    val restr =
      if plain_args args orelse
        (case args of [Type (a, rec_args)] => plain_args rec_args | _ => false)
      then [] else [(args, name)];
    val spec =
      (serial (), {is_def = is_def, module = module, name = name, lhs = args, rhs = deps});
    val defs' = defs |> update_specs c spec;
  in Defs defs' |> (if unchecked then I else dependencies pp (c, args) restr deps) end;


local  (* FIXME *)
  val define_aux = define
  val acc = Output.time_accumulator "Defs.define"
in
  fun define pp consts unchecked is_def module name lhs rhs =
    acc (define_aux pp consts unchecked is_def module name lhs rhs)
end;


end;
