theory VC_Condition
imports "HOL-Nominal.Nominal" 
begin

text \<open>
  We give here two examples showing that if we use the variable  
  convention carelessly in rule inductions, we might end 
  up with faulty lemmas. The point is that the examples
  are not variable-convention compatible and therefore in the 
  nominal data package one is protected from such bogus reasoning.
\<close>

text \<open>We define alpha-equated lambda-terms as usual.\<close>
atom_decl name 

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" (\<open>Lam [_]._\<close> [100,100] 100)

text \<open>
  The inductive relation 'unbind' unbinds the top-most  
  binders of a lambda-term; this relation is obviously  
  not a function, since it does not respect alpha-      
  equivalence. However as a relation 'unbind' is ok and     
  a similar relation has been used in our formalisation 
  of the algorithm W.\<close>

inductive
  unbind :: "lam \<Rightarrow> name list \<Rightarrow> lam \<Rightarrow> bool" (\<open>_ \<leadsto> _,_\<close> [60,60,60] 60)
where
  u_var: "(Var a) \<leadsto> [],(Var a)"
| u_app: "(App t1 t2) \<leadsto> [],(App t1 t2)"
| u_lam: "t\<leadsto>xs,t' \<Longrightarrow> (Lam [x].t) \<leadsto> (x#xs),t'"

text \<open>
  We can show that Lam [x].Lam [x].Var x unbinds to [x,x],Var x 
  and also to [z,y],Var y (though the proof for the second is a 
  bit clumsy).\<close> 

lemma unbind_lambda_lambda1: 
  shows "Lam [x].Lam [x].(Var x)\<leadsto>[x,x],(Var x)"
by (auto intro: unbind.intros)

lemma unbind_lambda_lambda2: 
  shows "Lam [x].Lam [x].(Var x)\<leadsto>[y,z],(Var z)"
proof -
  have "Lam [x].Lam [x].(Var x) = Lam [y].Lam [z].(Var z)" 
    by (auto simp add: lam.inject alpha calc_atm abs_fresh fresh_atm)
  moreover
  have "Lam [y].Lam [z].(Var z) \<leadsto> [y,z],(Var z)"
    by (auto intro: unbind.intros)
  ultimately 
  show "Lam [x].Lam [x].(Var x)\<leadsto>[y,z],(Var z)" by simp
qed

text \<open>Unbind is equivariant ...\<close>
equivariance unbind

text \<open>
  ... but it is not variable-convention compatible (see Urban, 
  Berghofer, Norrish [2007]). This condition requires for rule u_lam to 
  have the binder x not being a free variable in this rule's conclusion. 
  Because this condition is not satisfied, Isabelle will not derive a 
  strong induction principle for 'unbind' - that means Isabelle does not 
  allow us to use the variable convention in induction proofs over 'unbind'. 
  We can, however, force Isabelle to derive the strengthening induction 
  principle and see what happens.\<close>

nominal_inductive unbind
  sorry

text \<open>
  To obtain a faulty lemma, we introduce the function 'bind'
  which takes a list of names and abstracts them away in 
  a given lambda-term.\<close>

fun 
  bind :: "name list \<Rightarrow> lam \<Rightarrow> lam"
where
  "bind [] t = t"
| "bind (x#xs) t = Lam [x].(bind xs t)"

text \<open>
  Although not necessary for our main argument below, we can 
  easily prove that bind undoes the unbinding.\<close>

lemma bind_unbind:
  assumes a: "t \<leadsto> xs,t'"
  shows "t = bind xs t'"
using a by (induct) (auto)

text \<open>
  The next lemma shows by induction on xs that if x is a free 
  variable in t, and x does not occur in xs, then x is a free 
  variable in bind xs t. In the nominal tradition we formulate    
  'is a free variable in' as 'is not fresh for'.\<close>

lemma free_variable:
  fixes x::"name"
  assumes a: "\<not>(x\<sharp>t)" and b: "x\<sharp>xs"
  shows "\<not>(x\<sharp>bind xs t)"
using a b
by (induct xs)
   (auto simp add: fresh_list_cons abs_fresh fresh_atm)

text \<open>
  Now comes the first faulty lemma. It is derived using the     
  variable convention (i.e. our strong induction principle). 
  This faulty lemma states that if t unbinds to x#xs and t', 
  and x is a free variable in t', then it is also a free 
  variable in bind xs t'. We show this lemma by assuming that 
  the binder x is fresh w.r.t. to the xs unbound previously.\<close>   

lemma faulty1:
  assumes a: "t\<leadsto>(x#xs),t'"
  shows "\<not>(x\<sharp>t') \<Longrightarrow> \<not>(x\<sharp>bind xs t')"
using a
by (nominal_induct t xs'\<equiv>"x#xs" t' avoiding: xs rule: unbind.strong_induct)
   (simp_all add: free_variable)

text \<open>
  Obviously this lemma is bogus. For example, in 
  case Lam [x].Lam [x].(Var x) \<leadsto> [x,x],(Var x). 
  As a result, we can prove False.\<close>

lemma false1:
  shows "False"
proof -
  fix x
  have "Lam [x].Lam [x].(Var x)\<leadsto>[x,x],(Var x)" 
  and  "\<not>(x\<sharp>Var x)" by (simp_all add: unbind_lambda_lambda1 fresh_atm)
  then have "\<not>(x\<sharp>(bind [x] (Var x)))" by (rule faulty1)
  moreover 
  have "x\<sharp>(bind [x] (Var x))" by (simp add: abs_fresh)
  ultimately
  show "False" by simp
qed
   
text \<open>
  The next example is slightly simpler, but looks more
  contrived than 'unbind'. This example, called 'strip' just 
  strips off the top-most binders from lambdas.\<close>

inductive
  strip :: "lam \<Rightarrow> lam \<Rightarrow> bool" (\<open>_ \<rightarrow> _\<close> [60,60] 60)
where
  s_var: "(Var a) \<rightarrow> (Var a)"
| s_app: "(App t1 t2) \<rightarrow> (App t1 t2)"
| s_lam: "t \<rightarrow> t' \<Longrightarrow> (Lam [x].t) \<rightarrow> t'"

text \<open>
  The relation is equivariant but we have to use again 
  sorry to derive a strong induction principle.\<close>

equivariance strip

nominal_inductive strip
  sorry

text \<open>
  The second faulty lemma shows that a variable being fresh
  for a term is also fresh for this term after striping.\<close>

lemma faulty2:
  fixes x::"name"
  assumes a: "t \<rightarrow> t'"
  shows "x\<sharp>t \<Longrightarrow> x\<sharp>t'"
using a
by (nominal_induct t t'\<equiv>t' avoiding: t' rule: strip.strong_induct)
   (auto simp add: abs_fresh)

text \<open>Obviously Lam [x].Var x is a counter example to this lemma.\<close>

lemma false2:
  shows "False"
proof -
  fix x
  have "Lam [x].(Var x) \<rightarrow> (Var x)" by (auto intro: strip.intros)
  moreover
  have "x\<sharp>Lam [x].(Var x)" by (simp add: abs_fresh)
  ultimately have "x\<sharp>(Var x)" by (simp only: faulty2)
  then show "False" by (simp add: fresh_atm)
qed 

text \<open>A similar effect can be achieved by using naive inversion 
  on rules.\<close>

lemma false3: 
  shows "False"
proof -
  fix x
  have "Lam [x].(Var x) \<rightarrow> (Var x)" by (auto intro: strip.intros)
  moreover obtain y::"name" where fc: "y\<sharp>x" by (rule exists_fresh) (rule fin_supp)
  then have "Lam [x].(Var x) = Lam [y].(Var y)"
    by (simp add: lam.inject alpha calc_atm fresh_atm)
  ultimately have "Lam [y].(Var y) \<rightarrow> (Var x)" by simp
  then have "Var y \<rightarrow> Var x" using fc
    by (cases rule: strip.strong_cases[where x=y])
       (simp_all add: lam.inject alpha abs_fresh)
  then show "False" using fc
    by (cases) (simp_all add: lam.inject fresh_atm)
qed

text \<open>
  Moral: Who would have thought that the variable convention 
  is in general an unsound reasoning principle.
\<close>

end
