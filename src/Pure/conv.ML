(*  Title:      Pure/conv.ML
    ID:         $Id$
    Author:     Amine Chaieb and Makarius

Conversions: primitive equality reasoning.
*)

infix 1 then_conv;
infix 0 else_conv;

signature CONV =
sig
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
  val binop_conv: conv -> conv
  val forall_conv: int -> conv -> conv
  val concl_conv: int -> conv -> conv
  val prems_conv: int -> conv -> conv
  val fconv_rule: conv -> thm -> thm
  val gconv_rule: conv -> int -> thm -> thm
end;

structure Conv: CONV =
struct

(* conversionals *)

fun no_conv _ = raise CTERM ("no conversion", []);
val all_conv = Thm.reflexive;

fun (cv1 then_conv cv2) ct =
  let
    val eq1 = cv1 ct;
    val eq2 = cv2 (Thm.rhs_of eq1);
  in
    if Thm.is_reflexive eq1 then eq2
    else if Thm.is_reflexive eq2 then eq1
    else Thm.transitive eq1 eq2
  end;

fun (cv1 else_conv cv2) ct =
  (cv1 ct
    handle THM _ => cv2 ct
      | CTERM _ => cv2 ct
      | TERM _ => cv2 ct
      | TYPE _ => cv2 ct);

fun first_conv cvs = fold_rev (curry op else_conv) cvs no_conv;
fun every_conv cvs = fold_rev (curry op then_conv) cvs all_conv;

fun try_conv cv = cv else_conv all_conv;
fun repeat_conv cv ct = try_conv (cv then_conv repeat_conv cv) ct;

fun cache_conv cv =
  let
    val cache = ref Termtab.empty;
    fun conv ct =
      (case Termtab.lookup (! cache) (Thm.term_of ct) of
        SOME th => th
      | NONE =>
          let val th = cv ct
          in change cache (Termtab.update (Thm.term_of ct, th)); th end);
 in conv end;



(** Pure conversions **)

(* lambda terms *)

fun abs_conv cv ct =
  (case Thm.term_of ct of
    Abs (x, _, _) =>
      let
        val (v, ct') = Thm.dest_abs (SOME (gensym "gensym_abs_")) ct;
        val eq = cv ct';
      in if Thm.is_reflexive eq then all_conv ct else Thm.abstract_rule x v eq end
  | _ => raise CTERM ("abs_conv", [ct]));

fun combination_conv cv1 cv2 ct =
  let val (ct1, ct2) = Thm.dest_comb ct
  in Thm.combination (cv1 ct1) (cv2 ct2) end;

fun comb_conv cv = combination_conv cv cv;
fun arg_conv cv = combination_conv all_conv cv;
fun fun_conv cv = combination_conv cv all_conv;

val arg1_conv = fun_conv o arg_conv;
val fun2_conv = fun_conv o fun_conv;

fun binop_conv cv = combination_conv (arg_conv cv) cv;


(* logic *)

(*rewrite B in !!x1 ... xn. B*)
fun forall_conv n cv ct =
  if n <> 0 andalso can Logic.dest_all (Thm.term_of ct)
  then arg_conv (abs_conv (forall_conv (n - 1) cv)) ct
  else cv ct;

(*rewrite B in A1 ==> ... ==> An ==> B*)
fun concl_conv 0 cv ct = cv ct
  | concl_conv n cv ct =
      (case try Thm.dest_implies ct of
        NONE => cv ct
      | SOME (A, B) => Drule.imp_cong_rule (all_conv A) (concl_conv (n - 1) cv B));

(*rewrite the A's in A1 ==> ... ==> An ==> B*)
fun prems_conv 0 _ ct = all_conv ct
  | prems_conv n cv ct =
      (case try Thm.dest_implies ct of
        NONE => all_conv ct
      | SOME (A, B) => Drule.imp_cong_rule (cv A) (prems_conv (n - 1) cv B));


(* conversions as rules *)

(*forward conversion, cf. FCONV_RULE in LCF*)
fun fconv_rule cv th =
  let val eq = cv (Thm.cprop_of th) in
    if Thm.is_reflexive eq then th
    else Thm.equal_elim eq th
  end;

(*goal conversion*)
fun gconv_rule cv i th =
  (case try (Thm.cprem_of th) i of
    SOME ct =>
      let val eq = cv ct in
        if Thm.is_reflexive eq then th
        else Drule.with_subgoal i (fconv_rule (arg1_conv (K eq))) th
      end
  | NONE => raise THM ("gconv_rule", i, [th]));

end;
