
Goal "!!a b c. [| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c";
  by (Blast_tac 1);
qed "ex1_functional";
