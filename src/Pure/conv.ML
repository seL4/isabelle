(*  Title:      Pure/conv.ML
    ID:         $Id$
    Author:     Amine Chaieb and Makarius

Conversions: primitive equality reasoning.
*)

infix 1 then_conv;
infix 0 else_conv;

signature CONV =
sig
  type conv = cterm -> thm
  val no_conv: conv
  val all_conv: conv
  val then_conv: conv * conv -> conv
  val else_conv: conv * conv -> conv
  val first_conv: conv list -> conv
  val every_conv: conv list -> conv
  val try_conv: conv -> conv
  val repeat_conv: conv -> conv
  val cache_conv: conv -> conv
  val abs_conv: conv -> conv
  val combination_conv: conv -> conv -> conv
  val comb_conv: conv -> conv
  val arg_conv: conv -> conv
  val fun_conv: conv -> conv
  val arg1_conv: conv -> conv
  val fun2_conv: conv -> conv
  val forall_conv: int -> conv -> conv
  val concl_conv: int -> conv -> conv
  val prems_conv: int -> (int -> conv) -> conv
  val goals_conv: (int -> bool) -> conv -> conv
  val fconv_rule: conv -> thm -> thm
end;

structure Conv: CONV =
struct

(* conversionals *)

type conv = cterm -> thm;

fun no_conv _ = raise CTERM ("no conversion", []);
val all_conv = Thm.reflexive;

val is_refl = op aconv o Logic.dest_equals o Thm.prop_of;

fun (cv1 then_conv cv2) ct =
  let
    val eq1 = cv1 ct;
    val eq2 = cv2 (Thm.rhs_of eq1);
  in
    if is_refl eq1 then eq2
    else if is_refl eq2 then eq1
    else Thm.transitive eq1 eq2
  end;

fun (cv1 else_conv cv2) ct =
  (case try cv1 ct of SOME eq => eq | NONE => cv2 ct);

fun first_conv cvs = fold_rev (curry op else_conv) cvs no_conv;
fun every_conv cvs = fold_rev (curry op then_conv) cvs all_conv;

fun try_conv cv = cv else_conv all_conv;
fun repeat_conv cv ct = try_conv (cv then_conv repeat_conv cv) ct;

fun cache_conv cv =
  let
    val cache = ref Termtab.empty;
    fun conv ct =
      (case Termtab.lookup (! cache) (term_of ct) of
        SOME th => th
      | NONE =>
          let val th = cv ct
          in change cache (Termtab.update (term_of ct, th)); th end);
 in conv end;



(** Pure conversions **)

(* lambda terms *)

fun abs_conv cv ct =
  (case term_of ct of
    Abs (x, _, _) =>
      let val (v, ct') = Thm.dest_abs (SOME (gensym "abs_")) ct
      in Thm.abstract_rule x v (cv ct') end
  | _ => raise CTERM ("abs_conv", [ct]));

fun combination_conv cv1 cv2 ct =
  let val (ct1, ct2) = Thm.dest_comb ct
  in Thm.combination (cv1 ct1) (cv2 ct2) end;

fun comb_conv cv = combination_conv cv cv;
fun arg_conv cv = combination_conv all_conv cv;
fun fun_conv cv = combination_conv cv all_conv;

val arg1_conv = fun_conv o arg_conv;
val fun2_conv = fun_conv o fun_conv;


(* logic *)

(*rewrite B in !!x1 ... xn. B*)
fun forall_conv 0 cv ct = cv ct
  | forall_conv n cv ct =
      (case try Thm.dest_comb ct of
        NONE => cv ct
      | SOME (A, B) =>
          (case (term_of A, term_of B) of
            (Const ("all", _), Abs (x, _, _)) =>
              let val (v, B') = Thm.dest_abs (SOME (gensym "all_")) B in
                Thm.combination (all_conv A)
                  (Thm.abstract_rule x v (forall_conv (n - 1) cv B'))
              end
          | _ => cv ct));

(*rewrite B in A1 ==> ... ==> An ==> B*)
fun concl_conv 0 cv ct = cv ct
  | concl_conv n cv ct =
      (case try Thm.dest_implies ct of
        NONE => cv ct
      | SOME (A, B) => Drule.imp_cong_rule (all_conv A) (concl_conv (n - 1) cv B));

(*rewrite the A's in A1 ==> ... ==> An ==> B*)
fun prems_conv 0 _ = all_conv
  | prems_conv n cv =
      let
        fun conv i ct =
          if i = n + 1 then all_conv ct
          else
            (case try Thm.dest_implies ct of
              NONE => all_conv ct
            | SOME (A, B) => Drule.imp_cong_rule (cv i A) (conv (i + 1) B));
  in conv 1 end;

fun goals_conv pred cv = prems_conv ~1 (fn i => if pred i then cv else all_conv);
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;

end;
