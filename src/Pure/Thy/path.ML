(*  Title:      Pure/Thy/path.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Abstract algebra of file paths.  External representation Unix-style.
*)

signature PATH =
sig
  type T
  val pack: T -> string
  val unpack: string -> T
  val current: T
  val parent: T
  val root: T
  val variable: string -> T
  val absolute: T -> bool
  val base: T -> string
  val append: T -> T -> T
  val evaluate: (string -> T) -> T -> T
  val expand: (string -> string) -> string -> string
  val base_name: string -> string
end;

structure Path: PATH =
struct

(* type path *)

datatype T = Path of string list;

val current = Path [];
val parent = Path [".."];
val root = Path ["/"];

fun absolute (Path ("/" :: _)) = true
  | absolute _ = false;

fun base (Path []) = ""
  | base (Path ["/"]) = ""
  | base (Path xs) = snd (split_last xs);

fun variable name = Path ["$" ^ name];
fun is_variable elem = ord elem = ord "$";


(* append and norm *)

(*append non-normal path (2n arg) to reversed normal one, result is normal*)
fun rev_app xs [] = rev xs
  | rev_app _ ("/" :: ys) = rev_app ["/"] ys
  | rev_app xs ("." :: ys) = rev_app xs ys
  | rev_app (x :: xs) (".." :: ys) =
      if x = ".." orelse is_variable x then rev_app (".." :: x :: xs) ys
      else if x = "/" then rev_app (x :: xs) ys
      else rev_app xs ys
  | rev_app xs (y :: ys) = rev_app (y :: xs) ys;

fun norm path = rev_app [] path;

fun append (Path xs) (Path ys) = Path (rev_app (rev xs) ys);


(* pack and unpack *)

fun pack (Path []) = "."
  | pack (Path ("/" :: xs)) = "/" ^ space_implode "/" xs
  | pack (Path xs) = space_implode "/" xs;

fun unpack str =
  (case space_explode "/" str of
    [""] => []
  | "" :: xs => "/" :: filter (not_equal "") xs
  | xs => filter (not_equal "") xs)
    |> map (fn "~" => "$HOME" | x => x)
    |> norm
    |> Path;


(* eval variables *)

fun eval env x =
  if is_variable x then
    let val Path ys = env (implode (tl (explode x)))
    in ys end
  else [x];

fun evaluate env (Path xs) =
  Path (norm (flat (map (eval env) xs)));


(* operations on packed paths *)

fun expand env str =
  pack (evaluate (unpack o env) (unpack str));

val base_name = base o unpack;


end;
