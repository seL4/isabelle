(*  Title:      Pure/facts.ML
    ID:         $Id$
    Author:     Makarius

Environment of named facts, optionally indexed by proposition.
*)

signature FACTS =
sig
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

(* datatype *)

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
