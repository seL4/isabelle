(*  Title:      HOL/BCV/DFA_Framework.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

header "Dataflow Analysis Framework"

theory DFA_Framework = Listn:

text {* 
  The relationship between dataflow analysis and a welltyped-insruction predicate. 
*}

constdefs
 bounded :: "(nat => nat list) => nat => bool"
"bounded succs n == !p<n. !q:set(succs p). q<n"

 stable :: "'s ord =>
           (nat => 's => 's)
           => (nat => nat list) => 's list => nat => bool"
"stable r step succs ss p == !q:set(succs p). step p (ss!p) <=_r ss!q"

 stables :: "'s ord => (nat => 's => 's)
            => (nat => nat list) => 's list => bool"
"stables r step succs ss == !p<size ss. stable r step succs ss p"

 is_dfa :: "'s ord
           => ('s list => 's list)
           => (nat => 's => 's)
           => (nat => nat list)
           => nat => 's set => bool"
"is_dfa r dfa step succs n A == !ss : list n A.
   dfa ss : list n A & stables r step succs (dfa ss) & ss <=[r] dfa ss &
   (!ts: list n A. ss <=[r] ts & stables r step succs ts
                     --> dfa ss <=[r] ts)"

 is_bcv :: "'s ord => 's => (nat => 's => 's) => (nat => nat list)
           => nat => 's set => ('s list => 's list) => bool"
"is_bcv r T step succs n A bcv == !ss : list n A.
   (!p<n. (bcv ss)!p ~= T) =
   (? ts: list n A. ss <=[r] ts & welltyping r T step succs ts)"

 welltyping ::
"'s ord => 's => (nat => 's => 's) => (nat => nat list) => 's list => bool"
"welltyping r T step succs ts ==
 !p<size(ts). ts!p ~= T & stable r step succs ts p"


lemma is_dfaD:
 "[| is_dfa r dfa step succs n A; ss : list n A |] ==> 
  dfa ss:list n A & stables r step succs (dfa ss) & ss <=[r] dfa ss & 
  (!ts: list n A. stables r step succs ts & ss <=[r] ts 
  --> dfa ss <=[r] ts)"
  by (simp add: is_dfa_def)


lemma is_bcv_dfa:
  "[| order r; top r T; is_dfa r dfa step succs n A |] 
  ==> is_bcv r T step succs n A dfa"
apply (unfold is_bcv_def welltyping_def stables_def)
apply clarify
apply (drule is_dfaD)
apply assumption
apply clarify
apply (rule iffI)
 apply (rule bexI)
  apply (rule conjI)
   apply assumption
  apply (simp add: stables_def)
 apply assumption
apply clarify
apply (simp add: imp_conjR all_conj_distrib stables_def 
            cong: conj_cong)
apply (drule_tac x = ts in bspec)
 apply assumption
apply (force dest: le_listD)
done

end
