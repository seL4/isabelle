(* $Id$ *)

theory VC_Condition
imports "../Nominal" 
begin

text {* 
  We give here two examples that show if we use the variable  
  convention carelessly in rule inductions, we might end 
  up with faulty lemmas. The point is that the examples
  are not variable-convention compatible and therefore in the 
  nominal data package one is protected from such bogus reasoning.
*}

text {* We define alpha-equated lambda-terms as usual. *}
atom_decl name 

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {*
  The inductive relation 'unbind' unbinds the top-most  
  binders of a lambda-term; this relation is obviously  
  not a function, since it does not respect alpha-      
  equivalence. However as a relation 'unbind' is ok and     
  a similar relation has been used in our formalisation 
  of the algorithm W. *}
inductive
  unbind :: "lam \<Rightarrow> name list \<Rightarrow> lam \<Rightarrow> bool" ("_ \<mapsto> _,_" [60,60,60] 60)
where
  u_var: "(Var a) \<mapsto> [],(Var a)"
| u_app: "(App t1 t2) \<mapsto> [],(App t1 t2)"
| u_lam: "t\<mapsto>xs,t' \<Longrightarrow> (Lam [x].t) \<mapsto> (x#xs),t'"

text {*
  We can show that Lam [x].Lam [x].Var x unbinds to [x,x],Var x 
  and also to [z,y],Var y (though the proof for the second is a 
  bit clumsy). *} 
lemma unbind_lambda_lambda1: 
  shows "Lam [x].Lam [x].(Var x)\<mapsto>[x,x],(Var x)"
by (auto intro: unbind.intros)

lemma unbind_lambda_lambda2: 
  shows "Lam [x].Lam [x].(Var x)\<mapsto>[y,z],(Var z)"
proof -
  have "Lam [x].Lam [x].(Var x) = Lam [y].Lam [z].(Var z)" 
    by (auto simp add: lam.inject alpha calc_atm abs_fresh fresh_atm)
  moreover
  have "Lam [y].Lam [z].(Var z) \<mapsto> [y,z],(Var z)"
    by (auto intro: unbind.intros)
  ultimately 
  show "Lam [x].Lam [x].(Var x)\<mapsto>[y,z],(Var z)" by simp
qed

text {* Unbind is equivariant ...*}
equivariance unbind

text {*
  ... but it is not variable-convention compatible (see Urban, 
  Berghofer, Norrish [2007]). This condition requires for rule u_lam to 
  have the binder x not being a free variable in this rule's conclusion. 
  Because this condition is not satisfied, Isabelle will not derive a 
  strong induction principle for 'unbind' - that means Isabelle does not 
  allow us to use the variable convention in induction proofs over 'unbind'. 
  We can, however, force Isabelle to derive the strengthening induction 
  principle and see what happens. *}

nominal_inductive unbind
  sorry

text {*
  To obtain a faulty lemma, we introduce the function 'bind'
  which takes a list of names and abstracts them away in 
  a given lambda-term. *}
fun 
  bind :: "name list \<Rightarrow> lam \<Rightarrow> lam"
where
  "bind [] t = t"
| "bind (x#xs) t = Lam [x].(bind xs t)"

text {*
  Although not necessary for our main argument below, we can 
  easily prove that bind undoes the unbinding. *}
lemma bind_unbind:
  assumes a: "t \<mapsto> xs,t'"
  shows "t = bind xs t'"
using a by (induct) (auto)

text {*
  The next lemma shows by induction on xs that if x is a free 
  variable in t and x does not occur in xs, then x is a free 
  variable in bind xs t. In the nominal tradition we formulate    
  'is a free variable in' as 'is not fresh for'. *}
lemma free_variable:
  fixes x::"name"
  assumes a: "\<not>(x\<sharp>t)" and b: "x\<sharp>xs"
  shows "\<not>(x\<sharp>bind xs t)"
using a b
by (induct xs)
   (auto simp add: fresh_list_cons abs_fresh fresh_atm)

text {*
  Now comes the first faulty lemma. It is derived using the     
  variable convention (i.e. our strong induction principle). 
  This faulty lemma states that if t unbinds to x::xs and t', 
  and x is a free variable in t', then it is also a free 
  variable in bind xs t'. We show this lemma by assuming that 
  the binder x is fresh w.r.t. to the xs unbound previously. *}   

lemma faulty1:
  assumes a: "t\<mapsto>(x#xs),t'"
  shows "\<not>(x\<sharp>t') \<Longrightarrow> \<not>(x\<sharp>bind xs t')"
using a
by (nominal_induct t xs'\<equiv>"x#xs" t' avoiding: xs rule: unbind.strong_induct)
   (simp_all add: free_variable)

text {*
  Obviously this lemma is bogus. For example, in 
  case Lam [x].Lam [x].(Var x) \<mapsto> [x,x],(Var x). 
  As a result, we can prove False. 
*}
lemma false1:
  shows "False"
proof -
  have "Lam [x].Lam [x].(Var x)\<mapsto>[x,x],(Var x)" 
  and  "\<not>(x\<sharp>Var x)" by (simp_all add: unbind_lambda_lambda1 fresh_atm)
  then have "\<not>(x\<sharp>(bind [x] (Var x)))" by (rule faulty1)
  moreover 
  have "x\<sharp>(bind [x] (Var x))" by (simp add: abs_fresh)
  ultimately
  show "False" by simp
qed
   
text {* 
  The next example is slightly simpler, but looks more
  contrived than 'unbind'. This example, called 'strip' just 
  strips off the top-most binders from lambdas. *}

inductive
  strip :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<rightarrow> _" [60,60] 60)
where
  s_var: "(Var a) \<rightarrow> (Var a)"
| s_app: "(App t1 t2) \<rightarrow> (App t1 t2)"
| s_lam: "t \<rightarrow> t' \<Longrightarrow> (Lam [x].t) \<rightarrow> t'"

text {* 
  The relation is equivariant but we have to use again 
  sorry to derive a strong induction principle. 
*}
equivariance strip

nominal_inductive strip
  sorry

text {*
  The second faulty lemma shows that a variable being fresh
  for a term is also fresh for this term after striping. 
*}
lemma faulty2:
  fixes x::"name"
  assumes a: "t \<rightarrow> t'"
  shows "x\<sharp>t \<Longrightarrow> x\<sharp>t'"
using a
by (nominal_induct t t'\<equiv>t' avoiding: t' rule: strip.strong_induct)
   (auto simp add: abs_fresh)

text {* Obviously Lam [x].Var x is a counter example to this lemma. *}
lemma false2:
  shows "False"
proof -
  have "Lam [x].(Var x) \<rightarrow> (Var x)" by (auto intro: strip.intros)
  moreover
  have "x\<sharp>Lam [x].(Var x)" by (simp add: abs_fresh)
  ultimately have "x\<sharp>(Var x)" by (simp only: faulty2)
  then show "False" by (simp add: fresh_atm)
qed 
 
end