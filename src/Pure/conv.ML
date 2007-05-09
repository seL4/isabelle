(*  Title:      Pure/conv.ML
    ID:         $Id$
    Author:     Amine Chaieb and Makarius

Conversions: primitive equality reasoning.
*)

infix 1 AND;
infix 0 OR;

signature CONV =
sig
  type conv = cterm -> thm
  val no_conv: conv
  val all_conv: conv
  val option_conv: conv -> cterm -> thm option
  val AND: conv * conv -> conv
  val OR: conv * conv -> conv
  val forall_conv: int -> conv -> conv
  val concl_conv: int -> conv -> conv
  val prems_conv: int -> (int -> conv) -> conv
  val goals_conv: (int -> bool) -> conv -> conv
  val fconv_rule: conv -> thm -> thm
end;

structure Conv: CONV =
struct

(* conversionals *)

type conv = cterm -> thm

fun no_conv _ = raise CTERM ("no conversion", []);
val all_conv = Thm.reflexive;

val is_refl = op aconv o Logic.dest_equals o Thm.prop_of;

fun option_conv conv ct =
  (case try conv ct of
    NONE => NONE
  | SOME eq => if is_refl eq then NONE else SOME eq);

fun (conv1 AND conv2) ct =
  let
    val eq1 = conv1 ct;
    val eq2 = conv2 (Thm.rhs_of eq1);
  in
    if is_refl eq1 then eq2
    else if is_refl eq2 then eq1
    else Thm.transitive eq1 eq2
  end;

fun (conv1 OR conv2) ct =
  (case try conv1 ct of SOME eq => eq | NONE => conv2 ct);


(* Pure conversions *)

(*rewrite B in !!x1 ... xn. B*)
fun forall_conv 0 cv ct = cv ct
  | forall_conv n cv ct =
      (case try Thm.dest_comb ct of
        NONE => cv ct
      | SOME (A, B) =>
          (case (term_of A, term_of B) of
            (Const ("all", _), Abs (x, _, _)) =>
              let val (v, B') = Thm.dest_abs (SOME (gensym "all_")) B in
                Thm.combination (Thm.reflexive A)
                  (Thm.abstract_rule x v (forall_conv (n - 1) cv B'))
              end
          | _ => cv ct));

(*rewrite B in A1 ==> ... ==> An ==> B*)
fun concl_conv 0 cv ct = cv ct
  | concl_conv n cv ct =
      (case try Thm.dest_implies ct of
        NONE => cv ct
      | SOME (A, B) => Drule.imp_cong_rule (reflexive A) (concl_conv (n - 1) cv B));

(*rewrite the A's in A1 ==> ... ==> An ==> B*)
fun prems_conv 0 _ = reflexive
  | prems_conv n cv =
      let
        fun conv i ct =
          if i = n + 1 then reflexive ct
          else
            (case try Thm.dest_implies ct of
              NONE => reflexive ct
            | SOME (A, B) => Drule.imp_cong_rule (cv i A) (conv (i + 1) B));
  in conv 1 end;

fun goals_conv pred cv = prems_conv ~1 (fn i => if pred i then cv else all_conv);
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;

end;
