(*  Title:      Pure/Thy/path.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Abstract algebra of file paths.  External representation Unix-style.

TODO:
  - support variables and  eval:(string->T)->T->T (!?)
*)

signature PATH =
sig
  type T
  val pack: T -> string
  val unpack: string -> T
  val current: T
  val parent: T
  val root: T
  val absolute: T -> bool
  val append: T -> T -> T
end;

structure Path: PATH =
struct

(* type path *)

datatype T = Path of string list;

val current = Path [];
val parent = Path [".."];
val root = Path [""];

fun absolute (Path ("" :: _)) = true
  | absolute _ = false;


(* append and norm *)

(*append non-normal path (2n arg) to reversed normal one, result is normal*)
fun rev_app xs [] = rev xs
  | rev_app _ ("" :: ys) = rev_app [""] ys
  | rev_app xs ("." :: ys) = rev_app xs ys
  | rev_app [] (".." :: ys) = rev_app [".."] ys
  | rev_app (xs as ".." :: _) (".." :: ys) = rev_app (".." :: xs) ys
  | rev_app (xs as "" :: _) (".." :: ys) = rev_app xs ys
  | rev_app (_ :: xs) (".." :: ys) = rev_app xs ys
  | rev_app xs (y :: ys) = rev_app (y :: xs) ys;

fun norm path = rev_app [] path;
fun append (Path xs) (Path ys) = Path (rev_app (rev xs) ys);


(* pack and unpack *)

fun pack (Path []) = "."
  | pack (path as Path xs) =
      (if absolute path then "/" else "") ^ space_implode "/" xs;

fun unpack str =
  Path (norm
    (case space_explode "/" str of
      [""] => []
    | "" :: xs => "" :: filter (not_equal "") xs
    | xs => filter (not_equal "") xs));


end;
