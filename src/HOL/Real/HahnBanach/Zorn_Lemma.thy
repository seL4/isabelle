(*  Title:      HOL/Real/HahnBanach/Zorn_Lemma.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

theory Zorn_Lemma = Aux + Zorn:;


lemma Zorn's_Lemma: "a:S ==> (!!c. c: chain S ==> EX x. x:c ==> Union c : S) ==>
 EX y: S. ALL z: S. y <= z --> y = z";
proof (rule Zorn_Lemma2);
  assume aS: "a:S";
  assume r: "!!c. c: chain S ==> EX x. x:c ==> Union c : S";
  show "ALL c:chain S. EX y:S. ALL z:c. z <= y";
  proof;
    fix c; assume "c:chain S"; 

    show "EX y:S. ALL z:c. z <= y";
    proof (rule case_split [of "c={}"]);
      assume "c={}"; 
      with aS; show  ?thesis; by fast;
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
