(*<*)
theory natsum = Main:;
(*>*)
text{*\noindent
In particular, there are \isa{case}-expressions, for example
*}

(*<*)term(*>*) "case n of 0 \\<Rightarrow> 0 | Suc m \\<Rightarrow> m";

text{*\noindent
primitive recursion, for example
*}

consts sum :: "nat \\<Rightarrow> nat";
primrec "sum 0 = 0"
        "sum (Suc n) = Suc n + sum n";

text{*\noindent
and induction, for example
*}

lemma "sum n + sum n = n*(Suc n)";
apply(induct_tac n);
by(auto);

(*<*)
end
(*>*)
