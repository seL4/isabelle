(*  Title:      Pure/Isar/net_rules.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Efficient storage of rules: preserves order, prefers later entries.
*)

signature NET_RULES =
sig
  type 'a T
  val rules: 'a T -> 'a list
  val retrieve: 'a T -> term -> 'a list
  val retrieve_weighted: 'a T -> term -> 'a list
  val init: ('a * 'a -> bool) -> ('a -> int) -> ('a -> term) -> 'a T
  val merge: 'a T * 'a T -> 'a T
  val delete: 'a -> 'a T -> 'a T
  val insert: 'a -> 'a T -> 'a T
  val deletes: 'a list -> 'a T -> 'a T
  val inserts: 'a list -> 'a T -> 'a T
  val intro: thm T
  val elim: thm T
end;

structure NetRules: NET_RULES =
struct

(* datatype rules *)

datatype 'a T =
  Rules of {
    eq: 'a * 'a -> bool,
    weight: 'a -> int,
    index: 'a -> term,
    rules: 'a list,
    next: int,
    net: ((int * int) * 'a) Net.net};

fun mk_rules eq weight index rules next net =
  Rules {eq = eq, weight = weight, index = index, rules = rules, next = next, net = net};

fun rules (Rules {rules = rs, ...}) = rs;


(* retrieve rules *)

fun gen_retrieve order (Rules {rules, net, ...}) tm =
  Tactic.untaglist (map (fn ((_, k), x) => (k, x))
    (sort (order o pairself #1) (Net.unify_term net tm)));

fun retrieve x = gen_retrieve (int_ord o pairself snd) x;
fun retrieve_weighted x = gen_retrieve (prod_ord int_ord int_ord) x;


(* build rules *)

fun init eq weight index = mk_rules eq weight index [] ~1 Net.empty;

fun add rule (Rules {eq, weight, index, rules, next, net}) =
  mk_rules eq weight index (rule :: rules) (next - 1)
    (Net.insert_term ((index rule, ((weight rule, next), rule)), net, K false));

fun make eq weight index rules = foldr (uncurry add) (rules, init eq weight index);


fun merge (Rules {eq, weight, index, rules = rules1, ...}, Rules {rules = rules2, ...}) =
  make eq weight index (Library.gen_merge_lists' eq rules1 rules2);

fun delete rule (rs as Rules {eq, weight, index, rules, next, net}) =
  if not (Library.gen_mem eq (rule, rules)) then rs
  else mk_rules eq weight index (Library.gen_rem eq (rules, rule)) next
    (Net.delete_term ((index rule, ((0, 0), rule)), net, eq o pairself #2));

fun insert rule rs = add rule (delete rule rs);    (*ensure new rule gets precedence*)

fun deletes rules rs = foldr (uncurry delete) (rules, rs);
fun inserts rules rs = foldr (uncurry insert) (rules, rs);


(* intro/elim rules *)

val intro = init Thm.eq_thm Thm.nprems_of Thm.concl_of;
val elim = init Thm.eq_thm Thm.nprems_of Thm.major_prem_of;


end;
