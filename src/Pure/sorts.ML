(*  Title:      Pure/sorts.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Type classes and sorts.
*)

signature SORTS =
sig
  type classrel
  type arities
  val str_of_classrel: class * class -> string
  val str_of_sort: sort -> string
  val str_of_arity: string * sort list * sort -> string
  val class_eq: classrel -> class * class -> bool
  val class_less: classrel -> class * class -> bool
  val class_le: classrel -> class * class -> bool
  val sort_eq: classrel -> sort * sort -> bool
  val sort_less: classrel -> sort * sort -> bool
  val sort_le: classrel -> sort * sort -> bool
  val sorts_le: classrel -> sort list * sort list -> bool
  val inter_class: classrel -> class * sort -> sort
  val inter_sort: classrel -> sort * sort -> sort
  val norm_sort: classrel -> sort -> sort
  val of_sort: classrel -> arities -> typ * sort -> bool
  val mg_domain: classrel -> arities -> string -> sort -> sort list
  val nonempty_sort: classrel -> arities -> sort list -> sort -> bool
end;

structure Sorts: SORTS =
struct


(** type classes and sorts **)

(*
  Classes denote (possibly empty) collections of types that are
  partially ordered by class inclusion. They are represented
  symbolically by strings.

  Sorts are intersections of finitely many classes. They are
  represented by lists of classes.  Normal forms of sorts are sorted
  lists of minimal classes (wrt. current class inclusion).

  (already defined in Pure/term.ML)
*)


(* sort signature information *)

(*
  classrel:
    table representing the proper subclass relation; entries (c, cs)
    represent the superclasses cs of c;

  arities:
    table of association lists of all type arities; (t, ars) means
    that type constructor t has the arities ars; an element (c, Ss) of
    ars represents the arity t::(Ss)c;
*)

type classrel = (class list) Symtab.table;
type arities = ((class * sort list) list) Symtab.table;


(* print sorts and arities *)

val str_of_sort = Syntax.simple_str_of_sort;
fun str_of_classrel (c1, c2) = str_of_sort [c1] ^ " < " ^ str_of_sort [c2];
fun str_of_dom Ss = enclose "(" ")" (commas (map str_of_sort Ss));

fun str_of_arity (t, [], S) = t ^ " :: " ^ str_of_sort S
  | str_of_arity (t, Ss, S) =
      t ^ " :: " ^ str_of_dom Ss ^ " " ^ str_of_sort S;



(** equality and inclusion **)

(* classes *)

fun class_eq _ (c1, c2:class) = c1 = c2;

fun class_less classrel (c1, c2) =
  (case Symtab.lookup (classrel, c1) of
     Some cs => c2 mem_string cs
   | None => false);

fun class_le classrel (c1, c2) =
   c1 = c2 orelse class_less classrel (c1, c2);


(* sorts *)

fun sort_le classrel (S1, S2) =
  forall (fn c2 => exists  (fn c1 => class_le classrel (c1, c2)) S1) S2;

fun sorts_le classrel (Ss1, Ss2) =
  ListPair.all (sort_le classrel) (Ss1, Ss2);

fun sort_eq classrel (S1, S2) =
  sort_le classrel (S1, S2) andalso sort_le classrel (S2, S1);

fun sort_less classrel (S1, S2) =
  sort_le classrel (S1, S2) andalso not (sort_le classrel (S2, S1));


(* normal forms of sorts *)

fun minimal_class classrel S c =
  not (exists (fn c' => class_less classrel (c', c)) S);

fun norm_sort classrel S =
  sort_strings (distinct (filter (minimal_class classrel S) S));



(** intersection **)

(*intersect class with sort (preserves minimality)*)    (* FIXME tune? *)
fun inter_class classrel (c, S) =
  let
    fun intr [] = [c]
      | intr (S' as c' :: c's) =
          if class_le classrel (c', c) then S'
          else if class_le classrel (c, c') then intr c's
          else c' :: intr c's
  in intr S end;

(*instersect sorts (preserves minimality)*)
fun inter_sort classrel = foldr (inter_class classrel);



(** sorts of types **)

(* mg_domain *)                 (*exception TYPE*)

fun mg_dom arities a c =
  let fun err () = raise TYPE ("No way to get " ^ a ^ "::" ^ c ^ ".", [], []) in
    (case Symtab.lookup (arities, a) of
      None => err ()
    | Some ars => (case assoc (ars, c) of None => err () | Some Ss => Ss))
  end;

fun mg_domain _ _ _ [] = sys_error "mg_domain"  (*don't know number of args!*)
  | mg_domain classrel arities a S =
      let val doms = map (mg_dom arities a) S in
        foldl (ListPair.map (inter_sort classrel)) (hd doms, tl doms)
      end;


(* of_sort *)

fun of_sort classrel arities =
  let
    fun ofS (_, []) = true
      | ofS (TFree (_, S), S') = sort_le classrel (S, S')
      | ofS (TVar (_, S), S') = sort_le classrel (S, S')
      | ofS (Type (a, Ts), S) =
          let val Ss = mg_domain classrel arities a S in
            ListPair.all ofS (Ts, Ss)
          end handle TYPE _ => false;
  in ofS end;



(** nonempty_sort **)

(* FIXME improve: proper sorts; non-base, non-ground types (vars from hyps) *)
fun nonempty_sort classrel _ _ [] = true
  | nonempty_sort classrel arities hyps S =
      Symtab.exists (exists (fn (c, Ss) => [c] = S andalso null Ss) o snd) arities
        orelse exists (fn S' => sort_le classrel (S', S)) hyps;

end;
