theory If
imports FOLP
begin

definition "if" :: "[o,o,o]=>o" where
  "if(P,Q,R) == P&Q | ~P&R"

schematic_lemma ifI:
  assumes "!!x. x : P ==> f(x) : Q"  "!!x. x : ~P ==> g(x) : R"
  shows "?p : if(P,Q,R)"
apply (unfold if_def)
apply (tactic {* fast_tac @{context} (FOLP_cs addIs @{thms assms}) 1 *})
done

schematic_lemma ifE:
  assumes 1: "p : if(P,Q,R)" and
    2: "!!x y. [| x : P; y : Q |] ==> f(x, y) : S" and
    3: "!!x y. [| x : ~P; y : R |] ==> g(x, y) : S"
  shows "?p : S"
apply (insert 1)
apply (unfold if_def)
apply (tactic {* fast_tac @{context} (FOLP_cs addIs [@{thm 2}, @{thm 3}]) 1 *})
done

schematic_lemma if_commute: "?p : if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
apply (rule iffI)
apply (erule ifE)
apply (erule ifE)
apply (rule ifI)
apply (rule ifI)
oops

ML {* val if_cs = FOLP_cs addSIs [@{thm ifI}] addSEs [@{thm ifE}] *}

schematic_lemma if_commute: "?p : if(P, if(Q,A,B), if(Q,C,D)) <-> if(Q, if(P,A,C), if(P,B,D))"
apply (tactic {* fast_tac @{context} if_cs 1 *})
done

schematic_lemma nested_ifs: "?p : if(if(P,Q,R), A, B) <-> if(P, if(Q,A,B), if(R,A,B))"
apply (tactic {* fast_tac @{context} if_cs 1 *})
done

end
