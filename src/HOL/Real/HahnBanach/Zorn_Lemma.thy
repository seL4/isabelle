
theory Zorn_Lemma = Zorn:;


lemma Zorn's_Lemma: "a:S ==> (!!c. c: chain S ==> EX x. x:c ==> Union c : S) ==>
 EX y: S. ALL z: S. y <= z --> y = z";
proof (rule Zorn_Lemma2);
  assume aS: "a:S";
  assume r: "!!c. c: chain S ==> EX x. x:c ==> Union c : S";
  show "ALL c:chain S. EX y:S. ALL z:c. z <= y";
  proof;
    fix c; assume "c:chain S"; 
    have s: "EX x. x:c ==> Union c : S";
      by (rule r);
    show "EX y:S. ALL z:c. z <= y";
    proof (rule case [of "c={}"]);
      assume "c={}"; 
      show ?thesis; by fast;
    next;
      assume "c~={}";
      show ?thesis; 
      proof;
        have "EX x. x:c"; by fast;
        thus "Union c : S"; by (rule s);
        show "ALL z:c. z <= Union c"; by fast;
      qed;
    qed;
  qed;
qed;



end;
