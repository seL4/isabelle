(*  Title:      HOL/Lex/Automata.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversions between different kinds of automata
*)

theory Automata = DA + NAe:

constdefs
 na2da :: "('a,'s)na => ('a,'s set)da"
"na2da A == ({start A}, %a Q. Union(next A a ` Q), %Q. ? q:Q. fin A q)"

 nae2da :: "('a,'s)nae => ('a,'s set)da"
"nae2da A == ({start A},
              %a Q. Union(next A (Some a) ` ((eps A)^* `` Q)),
              %Q. ? p: (eps A)^* `` Q. fin A p)"

(*** Equivalence of NA and DA ***)

lemma DA_delta_is_lift_NA_delta:
 "!!Q. DA.delta (na2da A) w Q = Union(NA.delta A w ` Q)"
by (induct w)(auto simp:na2da_def)

lemma NA_DA_equiv:
  "NA.accepts A w = DA.accepts (na2da A) w"
apply (simp add: DA.accepts_def NA.accepts_def DA_delta_is_lift_NA_delta)
apply (simp add: na2da_def)
done

(*** Direct equivalence of NAe and DA ***)

lemma espclosure_DA_delta_is_steps:
 "!!Q. (eps A)^* `` (DA.delta (nae2da A) w Q) = steps A w `` Q";
apply (induct w)
 apply(simp)
apply (simp add: step_def nae2da_def)
apply (blast)
done

lemma NAe_DA_equiv:
  "DA.accepts (nae2da A) w = NAe.accepts A w"
proof -
  have "!!Q. fin (nae2da A) Q = (EX q : (eps A)^* `` Q. fin A q)"
    by(simp add:nae2da_def)
  thus ?thesis
    apply(simp add:espclosure_DA_delta_is_steps NAe.accepts_def DA.accepts_def)
    apply(simp add:nae2da_def)
    apply blast
    done
qed

end
