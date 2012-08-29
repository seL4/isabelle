(*  Title:      Pure/facts.ML
    Author:     Makarius

Environment of named facts, optionally indexed by proposition.
*)

signature FACTS =
sig
  val the_single: string -> thm list -> thm
  datatype interval = FromTo of int * int | From of int | Single of int
  datatype ref =
    Named of (string * Position.T) * interval list option |
    Fact of string
  val named: string -> ref
  val string_of_ref: ref -> string
  val name_of_ref: ref -> string
  val pos_of_ref: ref -> Position.T
  val map_name_of_ref: (string -> string) -> ref -> ref
  val select: ref -> thm list -> thm list
  val selections: string * thm list -> (ref * thm) list
  type T
  val empty: T
  val space_of: T -> Name_Space.T
  val is_concealed: T -> string -> bool
  val intern: T -> xstring -> string
  val extern: Proof.context -> T -> string -> xstring
  val lookup: Context.generic -> T -> string -> (bool * thm list) option
  val defined: T -> string -> bool
  val fold_static: (string * thm list -> 'a -> 'a) -> T -> 'a -> 'a
  val dest_static: T list -> T -> (string * thm list) list
  val extern_static: Proof.context -> T list -> T -> (xstring * thm list) list
  val props: T -> thm list
  val could_unify: T -> term -> thm list
  val merge: T * T -> T
  val add_global: Context.generic -> binding * thm list -> T -> string * T
  val add_local: Context.generic -> bool -> binding * thm list -> T -> string * T
  val add_dynamic: Context.generic -> binding * (Context.generic -> thm list) -> T -> string * T
  val del: string -> T -> T
  val hide: bool -> string -> T -> T
end;

structure Facts: FACTS =
struct

(** fact references **)

fun the_single _ [th] : thm = th
  | the_single name _ = error ("Expected singleton fact " ^ quote name);


(* datatype interval *)

datatype interval =
  FromTo of int * int |
  From of int |
  Single of int;

fun string_of_interval (FromTo (i, j)) = string_of_int i ^ "-" ^ string_of_int j
  | string_of_interval (From i) = string_of_int i ^ "-"
  | string_of_interval (Single i) = string_of_int i;

fun interval n iv =
  let fun err () = raise Fail ("Bad interval specification " ^ string_of_interval iv) in
    (case iv of
      FromTo (i, j) => if i <= j then i upto j else err ()
    | From i => if i <= n then i upto n else err ()
    | Single i => [i])
  end;


(* datatype ref *)

datatype ref =
  Named of (string * Position.T) * interval list option |
  Fact of string;

fun named name = Named ((name, Position.none), NONE);

fun name_pos_of_ref (Named (name_pos, _)) = name_pos
  | name_pos_of_ref (Fact _) = error "Illegal literal fact";

val name_of_ref = #1 o name_pos_of_ref;
val pos_of_ref = #2 o name_pos_of_ref;

fun map_name_of_ref f (Named ((name, pos), is)) = Named ((f name, pos), is)
  | map_name_of_ref _ r = r;

fun string_of_ref (Named ((name, _), NONE)) = name
  | string_of_ref (Named ((name, _), SOME is)) =
      name ^ enclose "(" ")" (commas (map string_of_interval is))
  | string_of_ref (Fact _) = error "Illegal literal fact";


(* select *)

fun select (Fact _) ths = ths
  | select (Named (_, NONE)) ths = ths
  | select (Named ((name, pos), SOME ivs)) ths =
      let
        val n = length ths;
        fun err msg =
          error (msg ^ " for " ^ quote name ^ " (length " ^ string_of_int n ^ ")" ^
            Position.here pos);
        fun sel i =
          if i < 1 orelse i > n then err ("Bad subscript " ^ string_of_int i)
          else nth ths (i - 1);
        val is = maps (interval n) ivs handle Fail msg => err msg;
      in map sel is end;


(* selections *)

fun selections (name, [th]) = [(Named ((name, Position.none), NONE), th)]
  | selections (name, ths) = map2 (fn i => fn th =>
      (Named ((name, Position.none), SOME [Single i]), th)) (1 upto length ths) ths;



(** fact environment **)

(* datatypes *)

datatype fact = Static of thm list | Dynamic of Context.generic -> thm list;

datatype T = Facts of
 {facts: fact Name_Space.table,
  props: thm Net.net};

fun make_facts facts props = Facts {facts = facts, props = props};

val empty = make_facts (Name_Space.empty_table "fact") Net.empty;


(* named facts *)

fun facts_of (Facts {facts, ...}) = facts;

val space_of = #1 o facts_of;
val table_of = #2 o facts_of;

val is_concealed = Name_Space.is_concealed o space_of;

val intern = Name_Space.intern o space_of;
fun extern ctxt = Name_Space.extern ctxt o space_of;

val defined = Symtab.defined o table_of;

fun lookup context facts name =
  (case Symtab.lookup (table_of facts) name of
    NONE => NONE
  | SOME (Static ths) => SOME (true, ths)
  | SOME (Dynamic f) => SOME (false, f context));

fun fold_static f =
  Symtab.fold (fn (name, Static ths) => f (name, ths) | _ => I) o table_of;


(* content difference *)

fun diff_table prev_facts facts =
  fold_static (fn (name, ths) =>
    if exists (fn prev => defined prev name) prev_facts then I
    else cons (name, ths)) facts [];

fun dest_static prev_facts facts =
  sort_wrt #1 (diff_table prev_facts facts);

fun extern_static ctxt prev_facts facts =
  sort_wrt #1 (diff_table prev_facts facts |> map (apfst (extern ctxt facts)));


(* indexed props *)

val prop_ord = Term_Ord.term_ord o pairself Thm.full_prop_of;

fun props (Facts {props, ...}) = sort_distinct prop_ord (Net.content props);
fun could_unify (Facts {props, ...}) = Net.unify_term props;


(* merge facts *)

fun merge (Facts {facts = facts1, props = props1}, Facts {facts = facts2, props = props2}) =
  let
    val facts' = Name_Space.merge_tables (facts1, facts2);
    val props' = Net.merge (is_equal o prop_ord) (props1, props2);
  in make_facts facts' props' end;


(* add static entries *)

local

fun add context strict do_props (b, ths) (Facts {facts, props}) =
  let
    val (name, facts') =
      if Binding.is_empty b then ("", facts)
      else Name_Space.define context strict (b, Static ths) facts;
    val props' =
      if do_props
      then fold (fn th => Net.insert_term (K false) (Thm.full_prop_of th, th)) ths props
      else props;
  in (name, make_facts facts' props') end;

in

fun add_global context = add context true false;
fun add_local context = add context false;

end;


(* add dynamic entries *)

fun add_dynamic context (b, f) (Facts {facts, props}) =
  let val (name, facts') = Name_Space.define context true (b, Dynamic f) facts;
  in (name, make_facts facts' props) end;


(* remove entries *)

fun del name (Facts {facts = (space, tab), props}) =
  let
    val space' = Name_Space.hide true name space handle ERROR _ => space;
    val tab' = Symtab.delete_safe name tab;
  in make_facts (space', tab') props end;

fun hide fully name (Facts {facts = (space, tab), props}) =
  make_facts (Name_Space.hide fully name space, tab) props;

end;
