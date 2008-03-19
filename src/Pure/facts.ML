(*  Title:      Pure/facts.ML
    ID:         $Id$
    Author:     Makarius

Environment of named facts, optionally indexed by proposition.
*)

signature FACTS =
sig
  val the_single: string -> thm list -> thm
  datatype interval = FromTo of int * int | From of int | Single of int
  datatype ref =
    Named of string * interval list option |
    Fact of string
  val string_of_ref: ref -> string
  val name_of_ref: ref -> string
  val map_name_of_ref: (string -> string) -> ref -> ref
  val select: ref -> thm list -> thm list
  val selections: string * thm list -> (ref * thm) list
  type T
  val space_of: T -> NameSpace.T
  val lookup: T -> string -> thm list option
  val dest: T -> (string * thm list) list
  val extern: T -> (xstring * thm list) list
  val props: T -> thm list
  val could_unify: T -> term -> thm list
  val empty: T
  val merge: T * T -> T
  val add_global: NameSpace.naming -> string * thm list -> T -> T
  val add_local: bool -> NameSpace.naming -> string * thm list -> T -> T
  val del: string -> T -> T
end;

structure Facts: FACTS =
struct

(** fact references **)

fun the_single _ [th] : thm = th
  | the_single name _ = error ("Single theorem expected " ^ quote name);


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
  Named of string * interval list option |
  Fact of string;

fun name_of_ref (Named (name, _)) = name
  | name_of_ref (Fact _) = error "Illegal literal fact";

fun map_name_of_ref f (Named (name, is)) = Named (f name, is)
  | map_name_of_ref _ r = r;

fun string_of_ref (Named (name, NONE)) = name
  | string_of_ref (Named (name, SOME is)) =
      name ^ enclose "(" ")" (commas (map string_of_interval is))
  | string_of_ref (Fact _) = error "Illegal literal fact";


(* select *)

fun select (Fact _) ths = ths
  | select (Named (_, NONE)) ths = ths
  | select (Named (name, SOME ivs)) ths =
      let
        val n = length ths;
        fun err msg = error (msg ^ " for " ^ quote name ^ " (length " ^ string_of_int n ^ ")");
        fun sel i =
          if i < 1 orelse i > n then err ("Bad subscript " ^ string_of_int i)
          else nth ths (i - 1);
        val is = maps (interval n) ivs handle Fail msg => err msg;
      in map sel is end;


(* selections *)

fun selections (name, [th]) = [(Named (name, NONE), th)]
  | selections (name, ths) =
      map2 (fn i => fn th => (Named (name, SOME [Single i]), th)) (1 upto length ths) ths;



(** fact environment **)

(* datatype T *)

datatype T = Facts of
 {facts: thm list NameSpace.table,
  props: thm Net.net};

fun make_facts facts props = Facts {facts = facts, props = props};


(* named facts *)

fun facts_of (Facts {facts, ...}) = facts;

val space_of = #1 o facts_of;
val lookup = Symtab.lookup o #2 o facts_of;
val dest = NameSpace.dest_table o facts_of;
val extern = NameSpace.extern_table o facts_of;


(* indexed props *)

val prop_ord = Term.term_ord o pairself Thm.full_prop_of;

fun props (Facts {props, ...}) = sort_distinct prop_ord (Net.content props);
fun could_unify (Facts {props, ...}) = Net.unify_term props;


(* build facts *)

val empty = make_facts NameSpace.empty_table Net.empty;

fun merge (Facts {facts = facts1, props = props1}, Facts {facts = facts2, props = props2}) =
  let
    val facts' = NameSpace.merge_tables (K true) (facts1, facts2);
    val props' = Net.merge (is_equal o prop_ord) (props1, props2);
  in make_facts facts' props' end;

fun add permissive do_props naming (name, ths) (Facts {facts, props}) =
  let
    val facts' =
      if name = "" then facts
      else
        let
          val (space, tab) = facts;
          val space' = NameSpace.declare naming name space;
          val tab' = (if permissive then Symtab.update else Symtab.update_new) (name, ths) tab
            handle Symtab.DUP dup => (legacy_feature ("Duplicate fact " ^ quote dup ^
              Position.str_of (Position.thread_data ())); tab);
        in (space', tab') end;
    val props' =
      if do_props then fold (fn th => Net.insert_term (K false) (Thm.full_prop_of th, th)) ths props
      else props;
  in make_facts facts' props' end;

val add_global = add false false;
val add_local = add true;

fun del name (Facts {facts = (space, tab), props}) =
  let
    val space' = NameSpace.hide true name space handle ERROR _ => space;
    val tab' = Symtab.delete_safe name tab;
  in make_facts (space', tab') props end;

end;
