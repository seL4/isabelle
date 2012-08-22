(*<*)theory Advanced imports Even begin
ML_file "../../antiquote_setup.ML"
setup Antiquote_Setup.setup
(*>*)

text {*
The premises of introduction rules may contain universal quantifiers and
monotone functions.  A universal quantifier lets the rule 
refer to any number of instances of 
the inductively defined set.  A monotone function lets the rule refer
to existing constructions (such as ``list of'') over the inductively defined
set.  The examples below show how to use the additional expressiveness
and how to reason from the resulting definitions.
*}

subsection{* Universal Quantifiers in Introduction Rules \label{sec:gterm-datatype} *}

text {*
\index{ground terms example|(}%
\index{quantifiers!and inductive definitions|(}%
As a running example, this section develops the theory of \textbf{ground
terms}: terms constructed from constant and function 
symbols but not variables. To simplify matters further, we regard a
constant as a function applied to the null argument  list.  Let us declare a
datatype @{text gterm} for the type of ground  terms. It is a type constructor
whose argument is a type of  function symbols. 
*}

datatype 'f gterm = Apply 'f "'f gterm list"

text {*
To try it out, we declare a datatype of some integer operations: 
integer constants, the unary minus operator and the addition 
operator.
*}

datatype integer_op = Number int | UnaryMinus | Plus

text {*
Now the type @{typ "integer_op gterm"} denotes the ground 
terms built over those symbols.

The type constructor @{text gterm} can be generalized to a function 
over sets.  It returns 
the set of ground terms that can be formed over a set @{text F} of function symbols. For
example,  we could consider the set of ground terms formed from the finite 
set @{text "{Number 2, UnaryMinus, Plus}"}.

This concept is inductive. If we have a list @{text args} of ground terms 
over~@{text F} and a function symbol @{text f} in @{text F}, then we 
can apply @{text f} to @{text args} to obtain another ground term. 
The only difficulty is that the argument list may be of any length. Hitherto, 
each rule in an inductive definition referred to the inductively 
defined set a fixed number of times, typically once or twice. 
A universal quantifier in the premise of the introduction rule 
expresses that every element of @{text args} belongs
to our inductively defined set: is a ground term 
over~@{text F}.  The function @{term set} denotes the set of elements in a given 
list. 
*}

inductive_set
  gterms :: "'f set \<Rightarrow> 'f gterm set"
  for F :: "'f set"
where
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> gterms F;  f \<in> F\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> gterms F"

text {*
To demonstrate a proof from this definition, let us 
show that the function @{term gterms}
is \textbf{monotone}.  We shall need this concept shortly.
*}

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
txt{*
Intuitively, this theorem says that
enlarging the set of function symbols enlarges the set of ground 
terms. The proof is a trivial rule induction.
First we use the @{text clarify} method to assume the existence of an element of
@{term "gterms F"}.  (We could have used @{text "intro subsetI"}.)  We then
apply rule induction. Here is the resulting subgoal:
@{subgoals[display,indent=0]}
The assumptions state that @{text f} belongs 
to~@{text F}, which is included in~@{text G}, and that every element of the list @{text args} is
a ground term over~@{text G}.  The @{text blast} method finds this chain of reasoning easily.  
*}
(*<*)oops(*>*)
text {*
\begin{warn}
Why do we call this function @{text gterms} instead 
of @{text gterm}?  A constant may have the same name as a type.  However,
name  clashes could arise in the theorems that Isabelle generates. 
Our choice of names keeps @{text gterms.induct} separate from 
@{text gterm.induct}.
\end{warn}

Call a term \textbf{well-formed} if each symbol occurring in it is applied
to the correct number of arguments.  (This number is called the symbol's
\textbf{arity}.)  We can express well-formedness by
generalizing the inductive definition of
\isa{gterms}.
Suppose we are given a function called @{text arity}, specifying the arities
of all symbols.  In the inductive step, we have a list @{text args} of such
terms and a function  symbol~@{text f}. If the length of the list matches the
function's arity  then applying @{text f} to @{text args} yields a well-formed
term.
*}

inductive_set
  well_formed_gterm :: "('f \<Rightarrow> nat) \<Rightarrow> 'f gterm set"
  for arity :: "'f \<Rightarrow> nat"
where
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> well_formed_gterm arity;  
                length args = arity f\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> well_formed_gterm arity"

text {*
The inductive definition neatly captures the reasoning above.
The universal quantification over the
@{text set} of arguments expresses that all of them are well-formed.%
\index{quantifiers!and inductive definitions|)}
*}

subsection{* Alternative Definition Using a Monotone Function *}

text {*
\index{monotone functions!and inductive definitions|(}% 
An inductive definition may refer to the
inductively defined  set through an arbitrary monotone function.  To
demonstrate this powerful feature, let us
change the  inductive definition above, replacing the
quantifier by a use of the function @{term lists}. This
function, from the Isabelle theory of lists, is analogous to the
function @{term gterms} declared above: if @{text A} is a set then
@{term "lists A"} is the set of lists whose elements belong to
@{term A}.  

In the inductive definition of well-formed terms, examine the one
introduction rule.  The first premise states that @{text args} belongs to
the @{text lists} of well-formed terms.  This formulation is more
direct, if more obscure, than using a universal quantifier.
*}

inductive_set
  well_formed_gterm' :: "('f \<Rightarrow> nat) \<Rightarrow> 'f gterm set"
  for arity :: "'f \<Rightarrow> nat"
where
step[intro!]: "\<lbrakk>args \<in> lists (well_formed_gterm' arity);  
                length args = arity f\<rbrakk>
               \<Longrightarrow> (Apply f args) \<in> well_formed_gterm' arity"
monos lists_mono

text {*
We cite the theorem @{text lists_mono} to justify 
using the function @{term lists}.%
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
\item @{term "0 \<in> even"}
\item @{term "n \<notin> even \<Longrightarrow> (Suc n) \<in> even"}
\end{trivlist}
Showing that 4 is even using these rules requires showing that 3 is not
even.  It is far from trivial to show that this set of rules
characterizes the even numbers.  

Even with its use of the function \isa{lists}, the premise of our
introduction rule is positive:
@{thm [display,indent=0] (prem 1) step [no_vars]}
To apply the rule we construct a list @{term args} of previously
constructed well-formed terms.  We obtain a
new term, @{term "Apply f args"}.  Because @{term lists} is monotone,
applications of the rule remain valid as new terms are constructed.
Further lists of well-formed
terms become available and none are taken away.%
\index{monotone functions!and inductive definitions|)} 
*}

subsection{* A Proof of Equivalence *}

text {*
We naturally hope that these two inductive definitions of ``well-formed'' 
coincide.  The equality can be proved by separate inclusions in 
each direction.  Each is a trivial rule induction. 
*}

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
txt {*
The @{text clarify} method gives
us an element of @{term "well_formed_gterm arity"} on which to perform 
induction.  The resulting subgoal can be proved automatically:
@{subgoals[display,indent=0]}
This proof resembles the one given in
{\S}\ref{sec:gterm-datatype} above, especially in the form of the
induction hypothesis.  Next, we consider the opposite inclusion:
*}
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
txt {*
The proof script is virtually identical,
but the subgoal after applying induction may be surprising:
@{subgoals[display,indent=0,margin=65]}
The induction hypothesis contains an application of @{term lists}.  Using a
monotone function in the inductive definition always has this effect.  The
subgoal may look uninviting, but fortunately 
@{term lists} distributes over intersection:
@{named_thms [display,indent=0] lists_Int_eq [no_vars] (lists_Int_eq)}
Thanks to this default simplification rule, the induction hypothesis 
is quickly replaced by its two parts:
\begin{trivlist}
\item @{term "args \<in> lists (well_formed_gterm' arity)"}
\item @{term "args \<in> lists (well_formed_gterm arity)"}
\end{trivlist}
Invoking the rule @{text well_formed_gterm.step} completes the proof.  The
call to @{text auto} does all this work.

This example is typical of how monotone functions
\index{monotone functions} can be used.  In particular, many of them
distribute over intersection.  Monotonicity implies one direction of
this set equality; we have this theorem:
@{named_thms [display,indent=0] mono_Int [no_vars] (mono_Int)}
*}
(*<*)oops(*>*)


subsection{* Another Example of Rule Inversion *}

text {*
\index{rule inversion|(}%
Does @{term gterms} distribute over intersection?  We have proved that this
function is monotone, so @{text mono_Int} gives one of the inclusions.  The
opposite inclusion asserts that if @{term t} is a ground term over both of the
sets
@{term F} and~@{term G} then it is also a ground term over their intersection,
@{term "F \<inter> G"}.
*}

lemma gterms_IntI:
     "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
(*<*)oops(*>*)
text {*
Attempting this proof, we get the assumption 
@{term "Apply f args \<in> gterms G"}, which cannot be broken down. 
It looks like a job for rule inversion:\cmmdx{inductive\protect\_cases}
*}

inductive_cases gterm_Apply_elim [elim!]: "Apply f args \<in> gterms F"

text {*
Here is the result.
@{named_thms [display,indent=0,margin=50] gterm_Apply_elim [no_vars] (gterm_Apply_elim)}
This rule replaces an assumption about @{term "Apply f args"} by 
assumptions about @{term f} and~@{term args}.  
No cases are discarded (there was only one to begin
with) but the rule applies specifically to the pattern @{term "Apply f args"}.
It can be applied repeatedly as an elimination rule without looping, so we
have given the @{text "elim!"} attribute. 

Now we can prove the other half of that distributive law.
*}

lemma gterms_IntI [rule_format, intro!]:
     "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
apply (erule gterms.induct)
apply blast
done
(*<*)
lemma "t \<in> gterms F \<Longrightarrow> t \<in> gterms G \<longrightarrow> t \<in> gterms (F\<inter>G)"
apply (erule gterms.induct)
(*>*)
txt {*
The proof begins with rule induction over the definition of
@{term gterms}, which leaves a single subgoal:  
@{subgoals[display,indent=0,margin=65]}
To prove this, we assume @{term "Apply f args \<in> gterms G"}.  Rule inversion,
in the form of @{text gterm_Apply_elim}, infers
that every element of @{term args} belongs to 
@{term "gterms G"}; hence (by the induction hypothesis) it belongs
to @{term "gterms (F \<inter> G)"}.  Rule inversion also yields
@{term "f \<in> G"} and hence @{term "f \<in> F \<inter> G"}. 
All of this reasoning is done by @{text blast}.

\smallskip
Our distributive law is a trivial consequence of previously-proved results:
*}
(*<*)oops(*>*)
lemma gterms_Int_eq [simp]:
     "gterms (F \<inter> G) = gterms F \<inter> gterms G"
by (blast intro!: mono_Int monoI gterms_mono)

text_raw {*
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
*}

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
text_raw {*
\end{isabelle}
\end{exercise}
\end{isamarkuptext}
*}

(*<*)

text{*the following declaration isn't actually used*}
primrec
  integer_arity :: "integer_op \<Rightarrow> nat"
where
  "integer_arity (Number n)        = 0"
| "integer_arity UnaryMinus        = 1"
| "integer_arity Plus              = 2"

text{* the rest isn't used: too complicated.  OK for an exercise though.*}

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
