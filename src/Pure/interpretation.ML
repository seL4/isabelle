(*  Title:      Pure/interpretation.ML
    ID:         $Id$
    Author:     Florian Haftmann and Makarius

Generic interpretation of theory data.
*)

signature THEORY_INTERPRETATOR =
sig
  type T
  type interpretator = T list -> theory -> theory
  val add_those: T list -> theory -> theory
  val all_those: theory -> T list
  val add_interpretator: interpretator -> theory -> theory
  val init: theory -> theory
end;

signature THEORY_INTERPRETATOR_KEY =
sig
  type T
  val eq: T * T -> bool
end;

functor TheoryInterpretatorFun(Key: THEORY_INTERPRETATOR_KEY) : THEORY_INTERPRETATOR =
struct

open Key;

type interpretator = T list -> theory -> theory;

fun apply ips x = fold_rev (fn (_, f) => f x) ips;

structure InterpretatorData = TheoryDataFun
(
  type T = ((serial * interpretator) list * T list) * (theory -> theory) list;
  val empty = (([], []), []);
  val extend = I;
  val copy = I;
  fun merge pp (((interpretators1, done1), upd1), ((interpretators2, done2), upd2)) =
    let
      fun diff (interpretators1 : (serial * interpretator) list, done1)
        (interpretators2, done2) = let
          val interpretators = subtract (eq_fst (op =)) interpretators1 interpretators2;
          val undone = subtract eq done2 done1;
        in if null interpretators then [] else [apply interpretators undone] end;
      val interpretators = AList.merge (op =) (K true) (interpretators1, interpretators2);
      val done = Library.merge eq (done1, done2);
      val upd_new = diff (interpretators2, done2) (interpretators1, done1)
        @ diff (interpretators1, done1) (interpretators2, done2);
      val upd = upd1 @ upd2 @ upd_new;
    in ((interpretators, done), upd) end;
);

fun consolidate thy =
  (case #2 (InterpretatorData.get thy) of
    [] => NONE
  | upd => SOME (thy |> Library.apply upd |> (InterpretatorData.map o apsnd) (K [])));

val init = Theory.at_begin consolidate;

fun add_those xs thy =
  let
    val ((interpretators, _), _) = InterpretatorData.get thy;
  in
    thy
    |> apply interpretators xs
    |> (InterpretatorData.map o apfst o apsnd) (append xs)
  end;

val all_those = snd o fst o InterpretatorData.get;

fun add_interpretator interpretator thy =
  let
    val ((interpretators, xs), _) = InterpretatorData.get thy;
  in
    thy
    |> interpretator (rev xs)
    |> (InterpretatorData.map o apfst o apfst) (cons (serial (), interpretator))
  end;

end;

