(*<*)theory Advanced imports Even begin(*>*)

text \<open>
The premises of introduction rules may contain universal quantifiers and
monotone functions.  A universal quantifier lets the rule 
refer to any number of instances of 
the inductively defined set.  A monotone function lets the rule refer
to existing constructions (such as ``list of'') over the inductively defined
set.  The examples below show how to use the additional expressiveness
and how to reason from the resulting definitions.
\<close>

subsection\<open>Universal Quantifiers in Introduction Rules \label{sec:gterm-datatype}\<close>

text \<open>
\index{ground terms example|(}%
\index{quantifiers!and inductive definitions|(}%
As a running example, this section develops the theory of \textbf{ground
terms}: terms constructed from constant and function 
symbols but not variables. To simplify matters further, we regard a
constant as a function applied to the null argument  list.  Let us declare a
datatype \<open>gterm\<close> for the type of ground  terms. It is a type constructor
whose argument is a type of  function symbols. 
\<close>

datatype 'f gterm = Apply 'f "'f gterm list"

text \<open>
To try it out, we declare a datatype of some integer operations: 
integer constants, the unary minus operator and the addition 
operator.
\<close>

datatype integer_op = Number int | UnaryMinus | Plus

text \<open>
Now the type \<^typ>\<open>integer_op gterm\<close> denotes the ground 
terms built over those symbols.

The type constructor \<open>gterm\<close> can be generalized to a function 
over sets.  It returns 
the set of ground terms that can be formed over a set \<open>F\<close> of function symbols. For
example,  we could consider the set of ground terms formed from the finite 
set \<open>{Number 2, UnaryMinus, Plus}\<close>.

This concept is inductive. If we have a list \<open>args\<close> of ground terms 
over~\<open>F\<close> and a function symbol \<open>f\<close> in \<open>F\<close>, then we 
can apply \<open>f\<close> to \<open>args\<close> to obtain another ground term. 
The only difficulty is that the argument list may be of any length. Hitherto, 
each rule in an inductive definition referred to the inductively 
defined set a fixed number of times, typically once or twice. 
A universal quantifier in the premise of the introduction rule 
expresses that every element of \<open>args\<close> belongs
to our inductively defined set: is a ground term 
over~\<open>F\<close>.  The function \<^term>\<open>set\<close> denotes the set of elements in a given 
list. 
\<close>

inductive_set
  gterms :: "'f set \<Rightarrow> 'f gterm set"
  for F :: "'f set"
where
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> gterms F;  f \<in> F\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> gterms F"

text \<open>
To demonstrate a proof from this definition, let us 
show that the function \<^term>\<open>gterms\<close>
is \textbf{monotone}.  We shall need this concept shortly.
\<close>

lemma gterms_mono: "F\<subseteq>G \<Longrightarrow> gterms F \<subseteq> gterms G"
apply clarify
apply (erule gterms.induct)
apply blast
done
(*<*)
lemma gterms_mono: "F\<subseteq>G \<Longrightarrow> gterms F \<subseteq> gterms G"
apply clarify
apply (erule gterms.induct)
(*>*)
txt\<open>
Intuitively, this theorem says that
enlarging the set of function symbols enlarges the set of ground 
terms. The proof is a trivial rule induction.
First we use the \<open>clarify\<close> method to assume the existence of an element of
\<^term>\<open>gterms F\<close>.  (We could have used \<open>intro subsetI\<close>.)  We then
apply rule induction. Here is the resulting subgoal:
@{subgoals[display,indent=0]}
The assumptions state that \<open>f\<close> belongs 
to~\<open>F\<close>, which is included in~\<open>G\<close>, and that every element of the list \<open>args\<close> is
a ground term over~\<open>G\<close>.  The \<open>blast\<close> method finds this chain of reasoning easily.  
\<close>
(*<*)oops(*>*)
text \<open>
\begin{warn}
Why do we call this function \<open>gterms\<close> instead 
of \<open>gterm\<close>?  A constant may have the same name as a type.  However,
name  clashes could arise in the theorems that Isabelle generates. 
Our choice of names keeps \<open>gterms.induct\<close> separate from 
\<open>gterm.induct\<close>.
\end{warn}

Call a term \textbf{well-formed} if each symbol occurring in it is applied
to the correct number of arguments.  (This number is called the symbol's
\textbf{arity}.)  We can express well-formedness by
generalizing the inductive definition of
\isa{gterms}.
Suppose we are given a function called \<open>arity\<close>, specifying the arities
of all symbols.  In the inductive step, we have a list \<open>args\<close> of such
terms and a function  symbol~\<open>f\<close>. If the length of the list matches the
function's arity  then applying \<open>f\<close> to \<open>args\<close> yields a well-formed
term.
\<close>

inductive_set
  well_formed_gterm :: "('f \<Rightarrow> nat) \<Rightarrow> 'f gterm set"
  for arity :: "'f \<Rightarrow> nat"
where
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> well_formed_gterm arity;  
                length args = arity f\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> well_formed_gterm arity"

text \<open>
The inductive definition neatly captures the reasoning above.
The universal quantification over the
\<open>set\<close> of arguments expresses that all of them are well-formed.%
\index{quantifiers!and inductive definitions|)}
\<close>

subsection\<open>Alternative Definition Using a Monotone Function\<close>

text \<open>
\index{monotone functions!and inductive definitions|(}% 
An inductive definition may refer to the
inductively defined  set through an arbitrary monotone function.  To
demonstrate this powerful feature, let us
change the  inductive definition above, replacing the
quantifier by a use of the function \<^term>\<open>lists\<close>. This
function, from the Isabelle theory of lists, is analogous to the
function \<^term>\<open>gterms\<close> declared above: if \<open>A\<close> is a set then
\<^term>\<open>lists A\<close> is the set of lists whose elements belong to
\<^term>\<open>A\<close>.  

In the inductive definition of well-formed terms, examine the one
introduction rule.  The first premise states that \<open>args\<close> belongs to
the \<open>lists\<close> of well-formed terms.  This formulation is more
direct, if more obscure, than using a universal quantifier.
\<close>

inductive_set
  well_formed_gterm' :: "('f \<Rightarrow> nat) \<Rightarrow> 'f gterm set"
  for arity :: "'f \<Rightarrow> nat"
where
step[intro!]: "\<lbrakk>args \<in> lists (well_formed_gterm' arity);  
                length args = arity f\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> well_formed_gterm' arity"
monos lists_mono

text \<open>
We cite the theorem \<open>lists_mono\<close> to justify 
using the function \<^term>\<open>lists\<close>.%
\footnote{This particular theorem is installed by default already, but we
include the \isakeyword{monos} declaration in order to illustrate its syntax.}
@{named_thms [display,indent=0] lists_mono [no_vars] (lists_mono)}
Why must the function be monotone?  An inductive definition describes
an iterative construction: each element of the set is constructed by a
finite number of introduction rule applications.  For example, the
elements of \isa{even} are constructed by finitely many applications of
the rules
@{thm [display,indent=0] even.intros [no_vars]}
All references to a set in its
inductive definition must be positive.  Applications of an
introduction rule cannot invalidate previous applications, allowing the
construction process to converge.
The following pair of rules do not constitute an inductive definition:
\begin{trivlist}
\item \<^term>\<open>0 \<in> even\<close>
\item \<^term>\<open>n \<notin> even \<Longrightarrow> (Suc n) \<in> even\<close>
\end{trivlist}
Showing that 4 is even using these rules requires showing that 3 is not
even.  It is far from trivial to show that this set of rules
characterizes the even numbers.  

Even with its use of the function \isa{lists}, the premise of our
introduction rule is positive:
@{thm [display,indent=0] (prem 1) step [no_vars]}
To apply the rule we construct a list \<^term>\<open>args\<close> of previously
constructed well-formed terms.  We obtain a
new term, \<^term>\<open>Apply f args\<close>.  Because \<^term>\<open>lists\<close> is monotone,
applications of the rule remain valid as new terms are constructed.
Further lists of well-formed
terms become available and none are taken away.%
\index{monotone functions!and inductive definitions|)} 
\<close>

subsection\<open>A Proof of Equivalence\<close>

text \<open>
We naturally hope that these two inductive definitions of ``well-formed'' 
coincide.  The equality can be proved by separate inclusions in 
each direction.  Each is a trivial rule induction. 
\<close>

lemma "well_formed_gterm arity \<subseteq> well_formed_gterm' arity"
apply clarify
apply (erule well_formed_gterm.induct)
apply auto
done
(*<*)
lemma "well_formed_gterm arity \<subseteq> well_formed_gterm' arity"
apply clarify
apply (erule well_formed_gterm.induct)
(*>*)
txt \<open>
The \<open>clarify\<close> method gives
us an element of \<^term>\<open>well_formed_gterm arity\<close> on which to perform 
induction.  The resulting subgoal can be proved automatically:
@{subgoals[display,indent=0]}
This proof resembles the one given in
{\S}\ref{sec:gterm-datatype} above, especially in the form of the
induction hypothesis.  Next, we consider the opposite inclusion:
\<close>
(*<*)oops(*>*)
lemma "well_formed_gterm' arity \<subseteq> well_formed_gterm arity"
apply clarify
apply (erule well_formed_gterm'.induct)
apply auto
done
(*<*)
lemma "well_formed_gterm' arity \<subseteq> well_formed_gterm arity"
apply clarify
apply (erule well_formed_gterm'.induct)
(*>*)
txt \<open>
The proof script is virtually identical,
but the subgoal after applying induction may be surprising:
@{subgoals[display,indent=0,margin=65]}
The induction hypothesis contains an application of \<^term>\<open>lists\<close>.  Using a
monotone function in the inductive definition always has this effect.  The
subgoal may look uninviting, but fortunately 
\<^term>\<open>lists\<close> distributes over intersection:
@{named_thms [display,indent=0] lists_Int_eq [no_vars] (lists_Int_eq)}
Thanks to this default simplification rule, the induction hypothesis 
is quickly replaced by its two parts:
\begin{trivlist}
\item \<^term>\<open>args \<in> lists (well_formed_gterm' arity)\<close>
\item \<^term>\<open>args \<in> lists (well_formed_gterm arity)\<close>
\end{trivlist}
Invoking the rule \<open>well_formed_gterm.step\<close> completes the proof.  The
call to \<open>auto\<close> does all this work.

This example is typical of how monotone functions
\index{monotone functions} can be used.  In particular, many of them
distribute over intersection.  Monotonicity implies one direction of
this set equality; we have this theorem:
@{named_thms [display,indent=0] mono_Int [no_vars] (mono_Int)}
\<close>
(*<*)oops(*>*)


subsection\<open>Another Example of Rule Inversion\<close>

text \<open>
\index{rule inversion|(}%
Does \<^term>\<open>gterms\<close> distribute over intersection?  We have proved that this
function is monotone, so \<open>mono_Int\<close> gives one of the inclusions.  The
opposite inclusion asserts that if \<^term>\<open>t\<close> is a ground term over both of the
sets
\<^term>\<open>F\<close> and~\<^term>\<open>G\<close> then it is also a ground term over their intersection,
\<^term>\<open>F \<inter> G\<close>.
\<close>

lemma gterms_IntI:
     "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
(*<*)oops(*>*)
text \<open>
Attempting this proof, we get the assumption 
\<^term>\<open>Apply f args \<in> gterms G\<close>, which cannot be broken down. 
It looks like a job for rule inversion:\cmmdx{inductive\protect\_cases}
\<close>

inductive_cases gterm_Apply_elim [elim!]: "Apply f args \<in> gterms F"

text \<open>
Here is the result.
@{named_thms [display,indent=0,margin=50] gterm_Apply_elim [no_vars] (gterm_Apply_elim)}
This rule replaces an assumption about \<^term>\<open>Apply f args\<close> by 
assumptions about \<^term>\<open>f\<close> and~\<^term>\<open>args\<close>.  
No cases are discarded (there was only one to begin
with) but the rule applies specifically to the pattern \<^term>\<open>Apply f args\<close>.
It can be applied repeatedly as an elimination rule without looping, so we
have given the \<open>elim!\<close> attribute. 

Now we can prove the other half of that distributive law.
\<close>

lemma gterms_IntI [rule_format, intro!]:
     "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
apply (erule gterms.induct)
apply blast
done
(*<*)
lemma "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
apply (erule gterms.induct)
(*>*)
txt \<open>
The proof begins with rule induction over the definition of
\<^term>\<open>gterms\<close>, which leaves a single subgoal:  
@{subgoals[display,indent=0,margin=65]}
To prove this, we assume \<^term>\<open>Apply f args \<in> gterms G\<close>.  Rule inversion,
in the form of \<open>gterm_Apply_elim\<close>, infers
that every element of \<^term>\<open>args\<close> belongs to 
\<^term>\<open>gterms G\<close>; hence (by the induction hypothesis) it belongs
to \<^term>\<open>gterms (F \<inter> G)\<close>.  Rule inversion also yields
\<^term>\<open>f \<in> G\<close> and hence \<^term>\<open>f \<in> F \<inter> G\<close>. 
All of this reasoning is done by \<open>blast\<close>.

\smallskip
Our distributive law is a trivial consequence of previously-proved results:
\<close>
(*<*)oops(*>*)
lemma gterms_Int_eq [simp]:
     "gterms (F \<inter> G) = gterms F \<inter> gterms G"
by (blast intro!: mono_Int monoI gterms_mono)

text_raw \<open>
\index{rule inversion|)}%
\index{ground terms example|)}


\begin{isamarkuptext}
\begin{exercise}
A function mapping function symbols to their 
types is called a \textbf{signature}.  Given a type 
ranging over type symbols, we can represent a function's type by a
list of argument types paired with the result type. 
Complete this inductive definition:
\begin{isabelle}
\<close>

inductive_set
  well_typed_gterm :: "('f \<Rightarrow> 't list * 't) \<Rightarrow> ('f gterm * 't)set"
  for sig :: "'f \<Rightarrow> 't list * 't"
(*<*)
where
step[intro!]: 
    "\<lbrakk>\<forall>pair \<in> set args. pair \<in> well_typed_gterm sig; 
      sig f = (map snd args, rtype)\<rbrakk>
     \<Longrightarrow> (Apply f (map fst args), rtype) 
         \<in> well_typed_gterm sig"
(*>*)
text_raw \<open>
\end{isabelle}
\end{exercise}
\end{isamarkuptext}
\<close>

(*<*)

text\<open>the following declaration isn't actually used\<close>
primrec
  integer_arity :: "integer_op \<Rightarrow> nat"
where
  "integer_arity (Number n)        = 0"
| "integer_arity UnaryMinus        = 1"
| "integer_arity Plus              = 2"

text\<open>the rest isn't used: too complicated.  OK for an exercise though.\<close>

inductive_set
  integer_signature :: "(integer_op * (unit list * unit)) set"
where
  Number:     "(Number n,   ([], ())) \<in> integer_signature"
| UnaryMinus: "(UnaryMinus, ([()], ())) \<in> integer_signature"
| Plus:       "(Plus,       ([(),()], ())) \<in> integer_signature"

inductive_set
  well_typed_gterm' :: "('f \<Rightarrow> 't list * 't) \<Rightarrow> ('f gterm * 't)set"
  for sig :: "'f \<Rightarrow> 't list * 't"
where
step[intro!]: 
    "\<lbrakk>args \<in> lists(well_typed_gterm' sig); 
      sig f = (map snd args, rtype)\<rbrakk>
     \<Longrightarrow> (Apply f (map fst args), rtype) 
         \<in> well_typed_gterm' sig"
monos lists_mono


lemma "well_typed_gterm sig \<subseteq> well_typed_gterm' sig"
apply clarify
apply (erule well_typed_gterm.induct)
apply auto
done

lemma "well_typed_gterm' sig \<subseteq> well_typed_gterm sig"
apply clarify
apply (erule well_typed_gterm'.induct)
apply auto
done


end
(*>*)
