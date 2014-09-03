(*  Title:      HOL/Tools/Ctr_Sugar/local_interpretation.ML
    Author:     Jasmin Blanchette, TU Muenchen

Generic interpretation of local theory data -- ad hoc. Based on

    Title:      Pure/interpretation.ML
    Author:     Florian Haftmann and Makarius
*)

signature LOCAL_INTERPRETATION =
sig
  type T
  val result: theory -> T list
  val interpretation: (T -> theory -> theory) -> (T -> local_theory -> local_theory) -> theory ->
    theory
  val data: T -> local_theory -> local_theory
  val data_global: T -> theory -> theory
  val init: theory -> theory
end;

functor Local_Interpretation(type T val eq: T * T -> bool): LOCAL_INTERPRETATION =
struct

type T = T;

structure Interp = Theory_Data
(
  type T =
    T list
    * ((((T -> theory -> theory) * (T -> local_theory -> local_theory)) * stamp) * T list) list;
  val empty = ([], []);
  val extend = I;
  fun merge ((data1, interps1), (data2, interps2)) : T =
    (Library.merge eq (data1, data2),
     AList.join (eq_snd (op =)) (K (Library.merge eq)) (interps1, interps2));
);

val result = #1 o Interp.get;

fun consolidate lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val (data, interps) = Interp.get thy;
    val unfinished = interps |> map (fn (((_, f), _), xs) =>
      (f, if eq_list eq (xs, data) then [] else subtract eq xs data));
    val finished = interps |> map (fn (interp, _) => (interp, data));
  in
    if forall (null o #2) unfinished then NONE
    else SOME (lthy |> fold_rev (uncurry fold_rev) unfinished
      |> Local_Theory.background_theory (Interp.put (data, finished)))
  end;

fun consolidate_global thy =
  let
    val (data, interps) = Interp.get thy;
    val unfinished = interps |> map (fn (((g, _), _), xs) =>
      (g, if eq_list eq (xs, data) then [] else subtract eq xs data));
    val finished = interps |> map (fn (interp, _) => (interp, data));
  in
    if forall (null o #2) unfinished then NONE
    else SOME (thy |> fold_rev (uncurry fold_rev) unfinished |> Interp.put (data, finished))
  end;

fun interpretation g f =
  Interp.map (apsnd (cons (((g, f), stamp ()), []))) #> perhaps consolidate_global;

fun data x = Local_Theory.background_theory (Interp.map (apfst (cons x))) #> perhaps consolidate;
fun data_global x = Interp.map (apfst (cons x)) #> perhaps consolidate_global;

val init = Theory.at_begin consolidate_global;

end;
