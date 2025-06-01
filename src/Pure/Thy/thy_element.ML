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
  val parse_elements_generic: Keyword.keywords -> ('a -> Command_Span.span) -> 'a Scan.stopper ->
    'a list -> 'a element list
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



(* parse *)

fun parse_elements_generic keywords get_span stopper =
  let
    val not_eof = not o Scan.is_stopper stopper;

    fun category pred other =
      Scan.one (fn x =>
        (case get_span x of
          Command_Span.Span (Command_Span.Command_Span (name, _), _) => pred keywords name
        | _ => other));

    fun theory_element x =
      (category Keyword.is_theory_goal false -- proof >> element) x
    and proof_element x =
      (category Keyword.is_proof_goal false -- proof >> element ||
        category Keyword.is_proof_body true >> atom) x
    and proof x = (Scan.repeat proof_element -- category Keyword.is_qed false) x;

    val default_element = Scan.one not_eof >> atom;

    val parse_element = theory_element || default_element
  in
    Source.of_list #>
    Source.source stopper (Scan.bulk parse_element) #>
    Source.exhaust
  end;

fun parse_elements keywords =
  parse_elements_generic keywords I Command_Span.stopper;

end;
