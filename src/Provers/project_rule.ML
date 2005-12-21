(*  Title:      Provers/project_rule.ML
    ID:         $Id$
    Author:     Makarius

Transform mutual rule:
  HH ==> (x1:A1 --> P1 x1) & ... & (xn:An --> Pn xn)
into projection:
  xi:Ai ==> HH ==> Pi xi
*)

signature PROJECT_RULE_DATA =
sig
  val conjunct1: thm
  val conjunct2: thm
  val mp: thm
end;

signature PROJECT_RULE =
sig
  val project: thm -> int -> thm
  val projections: thm -> thm list
end;

functor ProjectRuleFun(Data: PROJECT_RULE_DATA): PROJECT_RULE =
struct

fun conj1 th = th RS Data.conjunct1;
fun conj2 th = th RS Data.conjunct2;
fun imp th = th RS Data.mp;

val freeze = Drule.zero_var_indexes #> Drule.freeze_all;

fun project rule i =
  let
    fun proj 1 th = the_default th (try conj1 th)
      | proj k th = proj (k - 1) (conj2 th);
    fun prems k th =
      (case try imp th of
        NONE => (k, th)
      | SOME th' => prems (k + 1) th');
  in
    rule
    |> freeze
    |> proj i
    |> prems 0 |-> (fn k =>
      Thm.permute_prems 0 (~ k)
      #> Drule.standard'
      #> RuleCases.save rule
      #> RuleCases.add_consumes k)
  end;

fun projections rule =
  let
    fun projs k th =
      (case try conj2 th of
        NONE => k
      | SOME th' => projs (k + 1) th');
    val n = projs 1 (freeze rule);
  in map (project rule) (1 upto n) end;

end;
