structure Recon_Base =
struct

(* Auxiliary functions *)

exception Assertion of string;

val DEBUG = ref true;
fun TRACE s = if !DEBUG then print s else ();

exception Noassoc;
fun assoc a [] = raise Noassoc
  | assoc a ((x, y)::t) = if a = x then y else assoc a t;
fun assoc_exists a [] = false
  | assoc_exists a ((x, y)::t) = if a = x then true else assoc_exists a t;
fun assoc_update (a, b) [] = raise Noassoc
  | assoc_update (a, b) ((x, y)::t)
    = if a = x then (a, b)::t else (x, y)::(assoc_update (a, b) t)
fun assoc_inv a [] = raise Noassoc
  | assoc_inv a ((x, y)::t) = if a = y then x else assoc a t;
fun assoc_inv_exists a [] = false
  | assoc_inv_exists a ((x, y)::t) = if a = y then true else assoc_inv_exists a t;

fun is_mem x [] = false
  | is_mem x (h::t) = (x = h) orelse is_mem x t;
fun elt 0 (h::t) = h
  | elt n (h::t) = elt (n - 1) t
  | elt n l = raise (Assertion "elt: out of range");
fun remove_elt _ [] = raise (Assertion "remove_elt: out of range")
  | remove_elt 0 (h::t) = t
  | remove_elt n (h::t) = h::(remove_elt (n - 1) t);
fun elt_num x [] = raise (Assertion "elt_num: not in list")
  | elt_num x (h::t) = if h = x then 0 else 1 + elt_num x t;
fun set_add x l = if is_mem x l then l else x::l;

fun iter f a [] = a
  | iter f a (h::t) = f h (iter f a t);

end;
