(*  Title:      Pure/General/path.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Abstract algebra of file paths (external encoding Unix-style).
*)

signature PATH =
sig
  datatype elem = Root | Parent | Basic of string | Variable of string
  eqtype T
  val rep: T -> elem list
  val current: T
  val root: T
  val parent: T
  val basic: string -> T
  val variable: string -> T
  val is_absolute: T -> bool
  val is_basic: T -> bool
  val append: T -> T -> T
  val pack: T -> string
  val unpack: string -> T
  val base: T -> T
  val ext: string -> T -> T
(* FIXME  val evaluate: (string -> T) -> T -> T	*)
  val expand: T -> T
end;

structure Path(* FIXME : PATH *) =
struct


(* path elements *)

datatype elem = Root | Parent | Basic of string | Variable of string;

fun no_meta_chars chs =
  (case ["/", "\\", "$", "~"] inter_string chs of
    [] => chs
  | bads => error ("Illegal character(s) " ^ commas_quote bads ^
      " in path element specification: " ^ quote (implode chs)));

val basic_elem = Basic o implode o no_meta_chars;
val variable_elem = Variable o implode o no_meta_chars;

fun is_var (Variable _) = true
  | is_var _ = false;


(* type path *)

datatype T = Path of elem list;

fun rep (Path xs) = xs;

val current = Path [];
val root = Path [Root];
val parent = Path [Parent];
fun basic s = Path [basic_elem (explode s)];
fun variable s = Path [variable_elem (explode s)];

fun is_absolute (Path (Root :: _)) = true
  | is_absolute _ = false;

fun is_basic (Path [Basic _]) = true
  | is_basic _ = false;


(* append and norm *)

(*append non-normal path (2n arg) to reversed normal one, result is normal*)
fun rev_app xs [] = rev xs
  | rev_app _ (Root :: ys) = rev_app [Root] ys
  | rev_app (x :: xs) (Parent :: ys) =
      if x = Parent orelse is_var x then rev_app (Parent :: x :: xs) ys
      else if x = Root then rev_app (x :: xs) ys
      else rev_app xs ys
  | rev_app xs (y :: ys) = rev_app (y :: xs) ys;

fun append (Path xs) (Path ys) = Path (rev_app (rev xs) ys);
fun norm path = rev_app [] path;


(* pack *)

fun pack_elem Root = ""
  | pack_elem Parent = ".."
  | pack_elem (Basic s) = s
  | pack_elem (Variable s) = "$" ^ s;

fun pack (Path []) = "."
  | pack (Path (Root :: xs)) = "/" ^ space_implode "/" (map pack_elem xs)
  | pack (Path xs) = space_implode "/" (map pack_elem xs);


(* unpack *)

fun unpack_elem "" = Root
  | unpack_elem ".." = Parent
  | unpack_elem "~" = Variable "HOME"
  | unpack_elem "~~" = Variable "ISABELLE_HOME"
  | unpack_elem s =
      (case explode s of
        "$" :: cs => variable_elem cs
      | cs => basic_elem cs);

val unpack_elems = map unpack_elem o filter_out (equal "" orf equal ".");

fun unpack str = Path (norm
  (case space_explode "/" str of
    "" :: ss => Root :: unpack_elems ss
  | ss => unpack_elems ss));


(* base element *)

fun err_no_base path =
  error ("No base path element in " ^ quote (pack path));

fun base (path as Path xs) =
  (case try split_last xs of
    Some (_, x as Basic _) => Path [x]
  | _ => err_no_base path);

fun ext e (path as Path xs) =
  (case try split_last xs of
    Some (prfx, Basic s) => if e = "" then path else Path (prfx @ [Basic (s ^ "." ^ e)])
  | _ => err_no_base path);


(* evaluate variables *)

fun eval env (Variable s) = rep (env s)
  | eval _ x = [x];

fun evaluate env (Path xs) =
  Path (norm (flat (map (eval env) xs)));

val expand = evaluate (unpack o getenv);


end;
