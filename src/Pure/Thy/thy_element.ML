(*  Title:      Pure/Thy/thy_element.ML
    Author:     Makarius

Theory elements: statements with optional proof.
*)

signature THY_ELEMENT =
sig
  datatype 'a element = Element of 'a * ('a element list * 'a) option
  val atom: 'a -> 'a element
  val map_element: ('a -> 'b) -> 'a element -> 'b element
  val flat_element: 'a element -> 'a list
  val last_element: 'a element -> 'a
  val parse_elements: Keyword.keywords -> Command_Span.span list -> Command_Span.span element list
end;

structure Thy_Element: THY_ELEMENT =
struct

(* datatype element: command with optional proof *)

datatype 'a element = Element of 'a * ('a element list * 'a) option;

fun element (a, b) = Element (a, SOME b);
fun atom a = Element (a, NONE);

fun map_element f (Element (a, NONE)) = Element (f a, NONE)
  | map_element f (Element (a, SOME (elems, b))) =
      Element (f a, SOME ((map o map_element) f elems, f b));

fun flat_element (Element (a, NONE)) = [a]
  | flat_element (Element (a, SOME (elems, b))) = a :: maps flat_element elems @ [b];

fun last_element (Element (a, NONE)) = a
  | last_element (Element (_, SOME (_, b))) = b;


(* scanning spans *)

val eof = Command_Span.Span (Command_Span.Command_Span ("", Position.none), []);

fun is_eof (Command_Span.Span (Command_Span.Command_Span ("", _), _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper = Scan.stopper (K eof) is_eof;


(* parse *)

local

fun parse_element keywords =
  let
    fun category pred other =
      Scan.one
        (fn (Command_Span.Span (Command_Span.Command_Span (name, _), _)) =>
            pred keywords name
          | _ => other);

    fun theory_element x =
      (category Keyword.is_theory_goal false -- proof_rest >> element) x
    and proof_element x =
      (category Keyword.is_proof_goal false -- proof_rest >> element ||
        category Keyword.is_proof_body true >> atom) x
    and proof_rest x = (Scan.repeat proof_element -- category Keyword.is_qed false) x;

  in theory_element || Scan.one not_eof >> atom end;

in

fun parse_elements keywords =
  Source.of_list #>
  Source.source stopper (Scan.bulk (parse_element keywords)) #>
  Source.exhaust;

end;

end;
