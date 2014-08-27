(*  Title:      HOL/Tools/SMT/smtlib.ML
    Author:     Sascha Boehme, TU Muenchen

Parsing and generating SMT-LIB 2.
*)

signature SMTLIB =
sig
  exception PARSE of int * string
  datatype tree = 
    Num of int |
    Dec of int * int |
    Str of string |
    Sym of string |
    Key of string |
    S of tree list
  val parse: string list -> tree
  val pretty_tree: tree -> Pretty.T
  val str_of: tree -> string
end;

structure SMTLIB: SMTLIB =
struct

(* data structures *)

exception PARSE of int * string

datatype tree = 
  Num of int |
  Dec of int * int |
  Str of string |
  Sym of string |
  Key of string |
  S of tree list

datatype unfinished = None | String of string | Symbol of string


(* utilities *)

fun read_raw pred l cs =
  (case take_prefix pred cs of
    ([], []) => raise PARSE (l, "empty token")
  | ([], c :: _) => raise PARSE (l, "unexpected character " ^ quote c)
  | x => x)


(* numerals and decimals *)

fun int_of cs = fst (read_int cs)

fun read_num l cs =
  (case read_raw Symbol.is_ascii_digit l cs of
    (cs1, "." :: cs') =>
      let val (cs2, cs'') = read_raw Symbol.is_ascii_digit l cs'
      in (Dec (int_of cs1, int_of cs2), cs'') end
  | (cs1, cs2) => (Num (int_of cs1), cs2))


(* binary numbers *)

fun is_bin c = (c = "0" orelse c = "1")

fun read_bin l cs = read_raw is_bin l cs |>> Num o fst o read_radix_int 2


(* hex numbers *)

val is_hex = member (op =) (raw_explode "0123456789abcdefABCDEF")

fun within c1 c2 c = (ord c1 <= ord c andalso ord c <= ord c2)

fun unhex i [] = i
  | unhex i (c :: cs) =
      if within "0" "9" c then unhex (i * 16 + (ord c - ord "0")) cs
      else if within "a" "f" c then unhex (i * 16 + (ord c - ord "a" + 10)) cs
      else if within "A" "F" c then unhex (i * 16 + (ord c - ord "A" + 10)) cs
      else raise Fail ("bad hex character " ^ quote c)

fun read_hex l cs = read_raw is_hex l cs |>> Num o unhex 0


(* symbols *)

val symbol_chars = raw_explode "~!@$%^&*_+=<>.?/-" 

fun is_sym c =
  Symbol.is_ascii_letter c orelse
  Symbol.is_ascii_digit c orelse
  member (op =) symbol_chars c

fun read_sym f l cs = read_raw is_sym l cs |>> f o implode


(* quoted tokens *)

fun read_quoted stop (escape, replacement) cs =
  let
    fun read _ [] = NONE
      | read rs (cs as (c :: cs')) =
          if is_prefix (op =) stop cs then
            SOME (implode (rev rs), drop (length stop) cs)
          else if not (null escape) andalso is_prefix (op =) escape cs then
            read (replacement :: rs) (drop (length escape) cs)
          else read (c :: rs) cs'
  in read [] cs end

fun read_string cs = read_quoted ["\\", "\""] (["\\", "\\"], "\\") cs
fun read_symbol cs = read_quoted ["|"] ([], "") cs


(* core parser *)

fun read _ [] rest tss = (rest, tss)
  | read l ("(" :: cs) None tss = read l cs None ([] :: tss)
  | read l (")" :: cs) None (ts1 :: ts2 :: tss) =
      read l cs None ((S (rev ts1) :: ts2) :: tss)
  | read l ("#" :: "x" :: cs) None (ts :: tss) =
      token read_hex l cs ts tss
  | read l ("#" :: "b" :: cs) None (ts :: tss) =
      token read_bin l cs ts tss
  | read l (":" :: cs) None (ts :: tss) =
      token (read_sym Key) l cs ts tss
  | read l ("\"" :: cs) None (ts :: tss) =
      quoted read_string String Str l "" cs ts tss
  | read l ("|" :: cs) None (ts :: tss) =
      quoted read_symbol Symbol Sym l "" cs ts tss
  | read l ((c as "!") :: cs) None (ts :: tss) =
      token (fn _ => pair (Sym c)) l cs ts tss
  | read l (c :: cs) None (ts :: tss) =
      if Symbol.is_ascii_blank c then read l cs None (ts :: tss)
      else if Symbol.is_digit c then token read_num l (c :: cs) ts tss
      else token (read_sym Sym) l (c :: cs) ts tss
  | read l cs (String s) (ts :: tss) =
      quoted read_string String Str l s cs ts tss
  | read l cs (Symbol s) (ts :: tss) =
      quoted read_symbol Symbol Sym l s cs ts tss
  | read l _ _ [] = raise PARSE (l, "bad parser state")

and token f l cs ts tss =
  let val (t, cs') = f l cs
  in read l cs' None ((t :: ts) :: tss) end

and quoted r f g l s cs ts tss =
  (case r cs of
    NONE => (f (s ^ implode cs), ts :: tss)
  | SOME (s', cs') => read l cs' None ((g (s ^ s') :: ts) :: tss))
  


(* overall parser *)

fun read_line l line = read l (raw_explode line)

fun add_line line (l, (None, tss)) =
      if size line = 0 orelse nth_string line 0 = ";" then (l + 1, (None, tss))
      else (l + 1, read_line l line None tss)
  | add_line line (l, (unfinished, tss)) =
      (l + 1, read_line l line unfinished tss)

fun finish (_, (None, [[t]])) = t
  | finish (l, _) = raise PARSE (l, "bad nesting")

fun parse lines = finish (fold add_line lines (1, (None, [[]])))


(* pretty printer *)

fun pretty_tree (Num i) = Pretty.str (string_of_int i)
  | pretty_tree (Dec (i, j)) =
      Pretty.str (string_of_int i ^ "." ^ string_of_int j)
  | pretty_tree (Str s) =
      raw_explode s
      |> maps (fn "\"" => ["\\", "\""] | "\\" => ["\\", "\\"] | c => [c])
      |> implode
      |> enclose "\"" "\""
      |> Pretty.str
  | pretty_tree (Sym s) =
      if String.isPrefix "(" s (* for bit vector functions *) orelse
         forall is_sym (raw_explode s) then
        Pretty.str s
      else
        Pretty.str ("|" ^ s ^ "|")
  | pretty_tree (Key s) = Pretty.str (":" ^ s)
  | pretty_tree (S trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_tree trees))

val str_of = Pretty.str_of o pretty_tree

end;
