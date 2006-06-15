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
  val project: Proof.context -> int -> thm -> thm
  val projects: Proof.context -> int list -> thm -> thm list
  val projections: Proof.context -> thm -> thm list
end;

functor ProjectRuleFun(Data: PROJECT_RULE_DATA): PROJECT_RULE =
struct

fun conj1 th = th RS Data.conjunct1;
fun conj2 th = th RS Data.conjunct2;
fun imp th = th RS Data.mp;

fun projects ctxt is raw_rule =
  let
    fun proj 1 th = the_default th (try conj1 th)
      | proj k th = proj (k - 1) (conj2 th);
    fun prems k th =
      (case try imp th of
        NONE => (k, th)
      | SOME th' => prems (k + 1) th');
    val ([rule], ctxt') = Variable.import true [raw_rule] ctxt;
    fun result i =
      rule
      |> proj i
      |> prems 0 |-> (fn k =>
        Thm.permute_prems 0 (~ k)
        #> ProofContext.export ctxt' ctxt
        #> Drule.zero_var_indexes
        #> RuleCases.save raw_rule
        #> RuleCases.add_consumes k);
  in map result is end;

fun project ctxt i th = hd (projects ctxt [i] th);

fun projections ctxt raw_rule =
  let
    fun projs k th =
      (case try conj2 th of
        NONE => k
      | SOME th' => projs (k + 1) th');
    val ([rule], _) = Variable.import true [raw_rule] ctxt;
  in projects ctxt (1 upto projs 1 rule) raw_rule end;

end;
