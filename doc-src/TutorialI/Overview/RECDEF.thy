theory RECDEF = Main:

subsection{*Wellfounded Recursion*}

subsubsection{*Examples*}

consts fib :: "nat \<Rightarrow> nat";
recdef fib "measure(\<lambda>n. n)"
  "fib 0 = 0"
  "fib 1 = 1"
  "fib (Suc(Suc x)) = fib x + fib (Suc x)";

consts sep :: "'a \<times> 'a list \<Rightarrow> 'a list";
recdef sep "measure (\<lambda>(a,xs). length xs)"
  "sep(a, [])     = []"
  "sep(a, [x])    = [x]"
  "sep(a, x#y#zs) = x # a # sep(a,y#zs)";

consts last :: "'a list \<Rightarrow> 'a";
recdef last "measure (\<lambda>xs. length xs)"
  "last [x]      = x"
  "last (x#y#zs) = last (y#zs)";


consts sep1 :: "'a \<times> 'a list \<Rightarrow> 'a list";
recdef sep1 "measure (\<lambda>(a,xs). length xs)"
  "sep1(a, x#y#zs) = x # a # sep1(a,y#zs)"
  "sep1(a, xs)     = xs";

thm sep1.simps


consts swap12 :: "'a list \<Rightarrow> 'a list";
recdef swap12 "{}"
  "swap12 (x#y#zs) = y#x#zs"
  "swap12 zs       = zs";


subsubsection{*Beyond Measure*}

consts ack :: "nat\<times>nat \<Rightarrow> nat";
recdef ack "measure(\<lambda>m. m) <*lex*> measure(\<lambda>n. n)"
  "ack(0,n)         = Suc n"
  "ack(Suc m,0)     = ack(m, 1)"
  "ack(Suc m,Suc n) = ack(m,ack(Suc m,n))";


subsubsection{*Induction*}

lemma "map f (sep(x,xs)) = sep(f x, map f xs)"
thm sep.induct
apply(induct_tac x xs rule: sep.induct)
apply simp_all
done

lemma ack_incr2: "n < ack(m,n)"
apply(induct_tac m n rule: ack.induct)
apply simp_all
done


subsubsection{*Recursion Over Nested Datatypes*}

datatype tree = C "tree list"

lemma termi_lem: "t \<in> set ts \<longrightarrow> size t < Suc(tree_list_size ts)"
by(induct_tac ts, auto)

consts mirror :: "tree \<Rightarrow> tree"
recdef mirror "measure size"
 "mirror(C ts) = C(rev(map mirror ts))"
(hints recdef_simp: termi_lem)

lemma "mirror(mirror t) = t"
apply(induct_tac t rule: mirror.induct)
apply(simp add: rev_map sym[OF map_compose] cong: map_cong)
done

text{*
\begin{exercise}
Define a function for merging two ordered lists (of natural numbers) and
show that if the two input lists are ordered, so is the output.
\end{exercise}
*}

end
