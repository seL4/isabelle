(*  Title:      HOL/Real/HahnBanach/ZornLemma.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Zorn's Lemma *};

theory ZornLemma = Aux + Zorn:;

text{* 
Zorn's Lemmas says: if every linear ordered subset of an ordered set 
$S$ has an upper bound in $S$, then there exists a maximal element in $S$.
In our application $S$ is a set of sets, ordered by set inclusion. Since 
the union of a chain of sets is an upperbound for all elements of the 
chain, the conditions of Zorn's lemma can be modified:
if $S$ is non-empty, it suffices to show that for every non-empty 
chain $c$ in $S$ the union of $c$ also lies in $S$.
*};

theorem Zorn's_Lemma: 
  "a:S ==> (!!c. c: chain S ==> EX x. x:c ==> Union c : S) 
  ==>  EX y: S. ALL z: S. y <= z --> y = z";
proof (rule Zorn_Lemma2);
  assume aS: "a:S";
  assume r: "!!c. c: chain S ==> EX x. x:c ==> Union c : S";
  show "ALL c:chain S. EX y:S. ALL z:c. z <= y";
  proof;
    fix c; assume "c:chain S"; 
    show "EX y:S. ALL z:c. z <= y";
    proof (rule case_split);
 
      txt{* If $c$ is an empty chain, then every element
      in $S$ is an upperbound of $c$. *};

      assume "c={}"; 
      with aS; show ?thesis; by fast;

      txt{* If $c$ is non-empty, then $\Union c$ 
      is an upperbound of $c$, that lies in $S$. *};

    next;
      assume c: "c~={}";
      show ?thesis; 
      proof; 
        show "ALL z:c. z <= Union c"; by fast;
        show "Union c : S"; 
        proof (rule r);
          from c; show "EX x. x:c"; by fast;  
        qed;
      qed;
    qed;
  qed;
qed;

end;
