(*  Title:      Pure/Isar/net_rules.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Efficient storage of rules: preserves order, prefers later entries.
*)

signature NET_RULES =
sig
  type 'a T
  val rules: 'a T -> 'a list
  val may_unify: 'a T -> term -> 'a list
  val init: ('a * 'a -> bool) -> ('a -> term) -> 'a T
  val merge: 'a T * 'a T -> 'a T
  val delete: 'a -> 'a T -> 'a T
  val insert: 'a -> 'a T -> 'a T
  val deletes: 'a list -> 'a T -> 'a T
  val inserts: 'a list -> 'a T -> 'a T
  val init_intro: thm T
  val init_elim: thm T
end;

structure NetRules: NET_RULES =
struct

(* datatype rules *)

datatype 'a T =
  Rules of {
    eq: 'a * 'a -> bool,
    index: 'a -> term,
    rules: 'a list,
    next: int,
    net: (int * 'a) Net.net};

fun mk_rules eq index rules next net =
  Rules {eq = eq, index = index, rules = rules, next = next, net = net};

fun rules (Rules {rules = rs, ...}) = rs;
fun may_unify (Rules {net, ...}) tm = Tactic.orderlist (Net.unify_term net tm);


(* build rules *)

fun init eq index = mk_rules eq index [] ~1 Net.empty;

fun add rule (Rules {eq, index, rules, next, net}) =
  mk_rules eq index (rule :: rules) (next - 1)
    (Net.insert_term ((index rule, (next, rule)), net, K false));

fun make eq index rules = foldr (uncurry add) (rules, init eq index);


fun merge (Rules {eq, index, rules = rules1, ...}, Rules {rules = rules2, ...}) =
  make eq index (Library.generic_merge eq I I rules1 rules2);

fun delete rule (rs as Rules {eq, index, rules, next, net}) =
  if not (Library.gen_mem eq (rule, rules)) then rs
  else mk_rules eq index (Library.gen_rem eq (rules, rule)) next
    (Net.delete_term ((index rule, (0, rule)), net, eq o pairself #2));

fun insert rule rs = add rule (delete rule rs);    (*ensure new rule gets precedence*)

fun deletes rules rs = foldr (uncurry delete) (rules, rs);
fun inserts rules rs = foldr (uncurry insert) (rules, rs);


(* intro/elim rules *)

val init_intro = init Thm.eq_thm Thm.concl_of;
val init_elim = init Thm.eq_thm Thm.major_prem_of;


end;
