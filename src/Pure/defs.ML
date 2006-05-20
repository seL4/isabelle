(*  Title:      Pure/defs.ML
    ID:         $Id$
    Author:     Makarius

Global well-formedness checks for constant definitions.  Covers plain
definitions and simple sub-structural overloading (depending on a
single type argument).
*)

signature DEFS =
sig
  type T
  val specifications_of: T -> string ->
   (serial * {is_def: bool, module: string, name: string, lhs: typ, rhs: (string * typ) list}) list
  val empty: T
  val merge: Pretty.pp -> T * T -> T
  val define: Pretty.pp -> Consts.T ->
    bool -> bool -> string -> string -> string * typ -> (string * typ) list -> T -> T
end

structure Defs: DEFS =
struct

(* consts with type arguments *)

fun print_const pp (c, args) =
  let
    val prt_args =
      if null args then []
      else [Pretty.brk 1, Pretty.list "(" ")" (map (Pretty.typ pp o Type.freeze_type) args)];
  in Pretty.string_of (Pretty.block (Pretty.str c :: prt_args)) end;


(* source specs *)

type spec = {is_def: bool, module: string, name: string, lhs: typ, rhs: (string * typ) list};

fun disjoint_types T U =
  (Type.raw_unify (T, Logic.incr_tvar (maxidx_of_typ T + 1) U) Vartab.empty; false)
    handle Type.TUNIFY => true;

fun disjoint_specs c (i, {lhs = T, name = a, ...}: spec) =
  Inttab.forall (fn (j, {lhs = U, name = b, ...}: spec) =>
    i = j orelse not (Type.could_unify (T, U)) orelse disjoint_types T U orelse
      error ("Type clash in specifications " ^ quote a ^ " and " ^ quote b ^
        " for constant " ^ quote c));


(* patterns *)

datatype pattern = Unknown | Plain | Overloaded;

fun str_of_pattern Overloaded = "overloading"
  | str_of_pattern _ = "no overloading";

fun merge_pattern c (p1, p2) =
  if p1 = p2 orelse p2 = Unknown then p1
  else if p1 = Unknown then p2
  else error ("Inconsistent type patterns for constant " ^ quote c ^ ":\n" ^
    str_of_pattern p1 ^ " versus " ^ str_of_pattern p2);

fun plain_args args =
  forall Term.is_TVar args andalso not (has_duplicates (op =) args);

fun the_pattern _ name (c, [Type (a, args)]) =
      (Overloaded, if plain_args args then [] else [(a, (args, name))])
  | the_pattern prt _ (c, args) =
      if plain_args args then (Plain, [])
      else error ("Illegal type pattern for constant " ^ prt (c, args));


(* datatype defs *)

type def =
 {specs: spec Inttab.table,
  pattern: pattern,
  restricts: (string * (typ list * string)) list,
  reducts: (typ list * (string * typ list) list) list};

fun make_def (specs, pattern, restricts, reducts) =
  {specs = specs, pattern = pattern, restricts = restricts, reducts = reducts}: def;

fun map_def f ({specs, pattern, restricts, reducts}: def) =
  make_def (f (specs, pattern, restricts, reducts));

fun default_def (pattern, restricts) = make_def (Inttab.empty, pattern, restricts, []);

datatype T = Defs of def Symtab.table;
val empty = Defs Symtab.empty;

fun lookup_list which (Defs defs) c =
  (case Symtab.lookup defs c of
    SOME def => which def
  | NONE => []);

val specifications_of = lookup_list (Inttab.dest o #specs);
val restricts_of = lookup_list #restricts;
val reducts_of = lookup_list #reducts;


(* normalize defs *)

fun matcher arg =
  Option.map Envir.typ_subst_TVars
    (SOME (Type.raw_matches arg Vartab.empty) handle Type.TYPE_MATCH => NONE);

fun restriction prt defs (c, args) =
  (case args of
    [Type (a, Us)] =>
      (case AList.lookup (op =) (restricts_of defs c) a of
        SOME (Ts, name) =>
          if is_some (matcher (Ts, Us)) then ()
          else error ("Occurrence of overloaded constant " ^ prt (c, args) ^
            "\nviolates restriction " ^ prt (c, Ts) ^ "\nimposed by " ^ quote name)
      | NONE => ())
  | _ => ());

fun reduction defs deps =
  let
    fun reduct Us (Ts, rhs) =
      (case matcher (Ts, Us) of
        NONE => NONE
      | SOME subst => SOME (map (apsnd (map subst)) rhs));
    fun reducts (d, Us) = get_first (reduct Us) (reducts_of defs d);

    fun add (NONE, dp) = insert (op =) dp
      | add (SOME dps, _) = fold (insert (op =)) dps;
    val deps' = map (`reducts) deps;
  in
    if forall (is_none o #1) deps' then NONE
    else SOME (fold_rev add deps' [])
  end;

fun normalize prt defs (c, args) deps =
  let
    val reds = reduction defs deps;
    val deps' = the_default deps reds;
    val _ = List.app (restriction prt defs) ((c, args) :: deps');
    val _ = deps' |> List.app (fn (c', args') =>
      if c' = c andalso is_some (matcher (args, args')) then
        error ("Circular dependency of constant " ^ prt (c, args) ^ " -> " ^ prt (c, args'))
      else ());
  in reds end;


(* dependencies *)

fun normalize_deps prt defs0 (Defs defs) =
  let
    fun norm const deps = perhaps (normalize prt defs0 const) deps;
    fun norm_update (c, {reducts, ...}: def) =
      let val reducts' = reducts |> map (fn (args, deps) => (args, norm (c, args) deps)) in
        if reducts = reducts' then I
        else Symtab.map_entry c (map_def (fn (specs, pattern, restricts, reducts) =>
          (specs, pattern, restricts, reducts')))
      end;
  in Defs (Symtab.fold norm_update defs defs) end;

fun dependencies prt (c, args) pat deps (Defs defs) =
  let
    val deps' = perhaps (normalize prt (Defs defs) (c, args)) deps;
    val defs' = defs
      |> Symtab.default (c, default_def pat)
      |> Symtab.map_entry c (map_def (fn (specs, pattern, restricts, reducts) =>
        let
          val pattern' = merge_pattern c (pattern, #1 pat);
          val restricts' = Library.merge (op =) (restricts, #2 pat);
          val reducts' = insert (op =) (args, deps') reducts;
        in (specs, pattern', restricts', reducts') end));
  in normalize_deps prt (Defs defs') (Defs defs') end;


(* merge *)

fun join_specs c ({specs = specs1, pattern, restricts, reducts}, {specs = specs2, ...}: def) =
  let
    val specs' =
      Inttab.fold (fn spec2 => (disjoint_specs c spec2 specs1; Inttab.update spec2)) specs2 specs1;
  in make_def (specs', pattern, restricts, reducts) end;

fun merge pp (Defs defs1, Defs defs2) =
  let
    fun add_deps (c, args) pat deps defs =
      if AList.defined (op =) (reducts_of defs c) args then defs
      else dependencies (print_const pp) (c, args) pat deps defs;
    fun add_def (c, {pattern, restricts, reducts, ...}: def) =
      fold (fn (args, deps) => add_deps (c, args) (pattern, restricts) deps) reducts;
  in Defs (Symtab.join join_specs (defs1, defs2)) |> Symtab.fold add_def defs2 end;


(* define *)

fun define pp consts unchecked is_def module name lhs rhs (Defs defs) =
  let
    val prt = print_const pp;
    fun typargs const = (#1 const, Consts.typargs consts const);

    val (c, args) = typargs lhs;
    val pat =
      if unchecked then (Unknown, [])
      else the_pattern prt name (c, args);
    val spec =
      (serial (), {is_def = is_def, module = module, name = name, lhs = #2 lhs, rhs = rhs});

    val defs' = defs
      |> Symtab.default (c, default_def pat)
      |> Symtab.map_entry c (map_def (fn (specs, pattern, restricts, reducts) =>
        let
          val _ = disjoint_specs c spec specs;
          val specs' = Inttab.update spec specs;
        in (specs', pattern, restricts, reducts) end));
  in Defs defs' |> (if unchecked then I else dependencies prt (c, args) pat (map typargs rhs)) end;

end;
