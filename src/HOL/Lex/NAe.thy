(*  Title:      HOL/Lex/NAe.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Nondeterministic automata with epsilon transitions
*)

theory NAe = NA:

types ('a,'s)nae = "('a option,'s)na"

syntax eps :: "('a,'s)nae => ('s * 's)set"
translations "eps A" == "step A None"

consts steps :: "('a,'s)nae => 'a list =>   ('s * 's)set"
primrec
"steps A [] = (eps A)^*"
"steps A (a#w) = steps A w  O  step A (Some a)  O  (eps A)^*"

constdefs
 accepts :: "('a,'s)nae => 'a list => bool"
"accepts A w == ? q. (start A,q) : steps A w & fin A q"

(* not really used:
consts delta :: "('a,'s)nae => 'a list => 's => 's set"
primrec
"delta A [] s = (eps A)^* `` {s}"
"delta A (a#w) s = lift(delta A w) (lift(next A (Some a)) ((eps A)^* `` {s}))"
*)

lemma steps_epsclosure[simp]: "steps A w O (eps A)^* = steps A w"
by(cases w)(simp_all add:O_assoc)

lemma in_steps_epsclosure:
  "[| (p,q) : (eps A)^*; (q,r) : steps A w |] ==> (p,r) : steps A w"
apply(rule steps_epsclosure[THEN equalityE])
apply blast
done

lemma epsclosure_steps: "(eps A)^* O steps A w = steps A w";
apply(induct w)
 apply simp
apply(simp add:O_assoc[symmetric])
done

lemma in_epsclosure_steps:
  "[| (p,q) : steps A w; (q,r) : (eps A)^* |] ==> (p,r) : steps A w"
apply(rule epsclosure_steps[THEN equalityE])
apply blast
done

lemma steps_append[simp]:  "steps A (v@w) = steps A w  O  steps A v"
by(induct v)(simp_all add:O_assoc)

lemma in_steps_append[iff]:
  "(p,r) : steps A (v@w) = ((p,r) : (steps A w O steps A v))"
apply(rule steps_append[THEN equalityE])
apply blast
done

(* Equivalence of steps and delta
* Use "(? x : f ` A. P x) = (? a:A. P(f x))" ?? *
Goal "!p. (p,q) : steps A w = (q : delta A w p)";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [comp_def,step_def]) 1);
by (Blast_tac 1);
qed_spec_mp "steps_equiv_delta";
*)

end
