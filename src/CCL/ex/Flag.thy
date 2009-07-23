(*  Title:      CCL/ex/Flag.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Dutch national flag program -- except that the point of Dijkstra's example was to use
  arrays and this uses lists. *}

theory Flag
imports List
begin

consts
  Colour             :: "i set"
  red                :: "i"
  white              :: "i"
  blue               :: "i"
  ccase              :: "[i,i,i,i]=>i"
  flag               :: "i"

axioms

  Colour_def:  "Colour == Unit + Unit + Unit"
  red_def:        "red == inl(one)"
  white_def:    "white == inr(inl(one))"
  blue_def:     "blue == inr(inr(one))"

  ccase_def:   "ccase(c,r,w,b) == when(c,%x. r,%wb. when(wb,%x. w,%x. b))"

  flag_def:    "flag == lam l. letrec
      flagx l be lcase(l,<[],<[],[]>>,
                       %h t. split(flagx(t),%lr p. split(p,%lw lb.
                            ccase(h, <red$lr,<lw,lb>>,
                                     <lr,<white$lw,lb>>,
                                     <lr,<lw,blue$lb>>))))
      in flagx(l)"

  Flag_def:
     "Flag(l,x) == ALL lr:List(Colour).ALL lw:List(Colour).ALL lb:List(Colour).
                    x = <lr,<lw,lb>> -->
                  (ALL c:Colour.(c mem lr = true --> c=red) &
                                (c mem lw = true --> c=white) &
                                (c mem lb = true --> c=blue)) &
                  Perm(l,lr @ lw @ lb)"


lemmas flag_defs = Colour_def red_def white_def blue_def ccase_def

lemma ColourXH: "a : Colour <-> (a=red | a=white | a=blue)"
  unfolding simp_type_defs flag_defs by blast

lemma redT: "red : Colour"
  and whiteT: "white : Colour"
  and blueT: "blue : Colour"
  unfolding ColourXH by blast+

lemma ccaseT:
  "[| c:Colour; c=red ==> r : C(red); c=white ==> w : C(white); c=blue ==> b : C(blue) |]
    ==> ccase(c,r,w,b) : C(c)"
  unfolding flag_defs by ncanT

lemma "flag : List(Colour)->List(Colour)*List(Colour)*List(Colour)"
  apply (unfold flag_def)
  apply (tactic {* typechk_tac @{context}
    [@{thm redT}, @{thm whiteT}, @{thm blueT}, @{thm ccaseT}] 1 *})
  apply (tactic "clean_ccs_tac @{context}")
  apply (erule ListPRI [THEN ListPR_wf [THEN wfI]])
  apply assumption
  done

lemma "flag : PROD l:List(Colour).{x:List(Colour)*List(Colour)*List(Colour).FLAG(x,l)}"
  apply (unfold flag_def)
  apply (tactic {* gen_ccs_tac @{context}
    [@{thm redT}, @{thm whiteT}, @{thm blueT}, @{thm ccaseT}] 1 *})
  oops

end
