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
  val interpretation: string -> (T -> theory -> theory) -> (T -> local_theory -> local_theory) ->
    theory -> theory
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
    (Name_Space.naming * T) list
    * ((((T -> theory -> theory) * (T -> local_theory -> local_theory)) * (string * stamp))
       * (Name_Space.naming * T) list) list;
  val empty = ([], []);
  val extend = I;
  fun merge ((data1, interps1), (data2, interps2)) : T =
    (Library.merge (eq_snd eq) (data1, data2),
     AList.join (eq_snd (op =)) (K (Library.merge (eq_snd eq))) (interps1, interps2));
);

val result = map snd o fst o Interp.get;

fun consolidate_common g_or_f lift_lthy thy thy_or_lthy =
  let
    val (data, interps) = Interp.get thy;
    val unfinished = interps |> map (fn ((gf, _), data') =>
      (g_or_f gf,
       if eq_list (eq_snd eq) (data', data) then [] else subtract (eq_snd eq) data' data));
    val finished = interps |> map (apsnd (K data));
  in
    if forall (null o #2) unfinished then
      NONE
    else
      SOME (thy_or_lthy |> fold_rev (uncurry fold_rev) unfinished
        |> lift_lthy (Interp.put (data, finished)))
  end;

fun consolidate lthy =
  consolidate_common (fn (_, g) => fn (_, x) => g x) Local_Theory.background_theory
    (Proof_Context.theory_of lthy) lthy;

fun consolidate_global thy =
  consolidate_common (fn (f, _) => fn (naming, x) => fn thy =>
    thy |> Sign.map_naming (K naming) |> f x |> Sign.restore_naming thy) I thy thy;

fun interpretation name g f =
  Interp.map (apsnd (cons (((g, f), (name, stamp ())), []))) #> perhaps consolidate_global;

fun data x =
  Local_Theory.background_theory (fn thy => Interp.map (apfst (cons (Sign.naming_of thy, x))) thy)
  #> perhaps consolidate;

fun data_global x =
  (fn thy => Interp.map (apfst (cons (Sign.naming_of thy, x))) thy)
  #> perhaps consolidate_global;

val init = Theory.at_begin consolidate_global;

end;
