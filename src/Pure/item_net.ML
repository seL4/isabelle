(*  Title:      Pure/item_net.ML
    Author:     Markus Wenzel, TU Muenchen

Efficient storage of items indexed by terms; preserves order and
prefers later entries.
*)

signature ITEM_NET =
sig
  type 'a T
  val content: 'a T -> 'a list
  val retrieve: 'a T -> term -> 'a list
  val init: ('a * 'a -> bool) -> ('a -> term) -> 'a T
  val merge: 'a T * 'a T -> 'a T
  val delete: 'a -> 'a T -> 'a T
  val insert: 'a -> 'a T -> 'a T
end;

structure Item_Net: ITEM_NET =
struct

(* datatype *)

datatype 'a T =
  Items of {
    eq: 'a * 'a -> bool,
    index: 'a -> term,
    content: 'a list,
    next: int,
    net: (int * 'a) Net.net};

fun mk_items eq index content next net =
  Items {eq = eq, index = index, content = content, next = next, net = net};

fun content (Items {content, ...}) = content;
fun retrieve (Items {net, ...}) = order_list o Net.unify_term net;


(* build net *)

fun init eq index = mk_items eq index [] ~1 Net.empty;

fun add x (Items {eq, index, content, next, net}) =
  mk_items eq index (x :: content) (next - 1)
    (Net.insert_term (K false) (index x, (next, x)) net);

fun merge (Items {eq, index, content = content1, ...}, Items {content = content2, ...}) =
  let val content = Library.merge eq (content1, content2)
  in fold_rev add content (init eq index) end;

fun delete x (items as Items {eq, index, content, next, net}) =
  if not (member eq content x) then items
  else mk_items eq index (remove eq x content) next
    (Net.delete_term (eq o pairself #2) (index x, (0, x)) net);

fun insert x items = add x (delete x items);   (*ensure that added entry gets precedence*)

end;
