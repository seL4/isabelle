(*<*)theory Overloading1 = Main:(*>*)

subsubsection{*Controlled Overloading with Type Classes*}

text{*
We now start with the theory of ordering relations, which we shall phrase
in terms of the two binary symbols @{text"<<"} and @{text"<<="}
to avoid clashes with @{text"<"} and @{text"\<le>"} in theory @{text
Main}. To restrict the application of @{text"<<"} and @{text"<<="} we
introduce the class @{text ordrel}:
*}

axclass ordrel < type

text{*\noindent
This introduces a new class @{text ordrel} and makes it a subclass of
the predefined class @{text type}, which
is the class of all HOL types.
This is a degenerate form of axiomatic type class without any axioms.
Its sole purpose is to restrict the use of overloaded constants to meaningful
instances:
*}

consts less :: "('a::ordrel) \<Rightarrow> 'a \<Rightarrow> bool"     (infixl "<<"  50)
       le   :: "('a::ordrel) \<Rightarrow> 'a \<Rightarrow> bool"     (infixl "<<=" 50)

text{*\noindent
Note that only one occurrence of a type variable in a type needs to be
constrained with a class; the constraint is propagated to the other
occurrences automatically.

So far there are no types of class @{text ordrel}. To breathe life
into @{text ordrel} we need to declare a type to be an \bfindex{instance} of
@{text ordrel}:
*}

instance bool :: ordrel

txt{*\noindent
Command \isacommand{instance} actually starts a proof, namely that
@{typ bool} satisfies all axioms of @{text ordrel}.
There are none, but we still need to finish that proof, which we do
by invoking the \methdx{intro_classes} method:
*}

by intro_classes

text{*\noindent
More interesting \isacommand{instance} proofs will arise below
in the context of proper axiomatic type classes.

Although terms like @{prop"False <<= P"} are now legal, we still need to say
what the relation symbols actually mean at type @{typ bool}:
*}

defs (overloaded)
le_bool_def:  "P <<= Q \<equiv> P \<longrightarrow> Q"
less_bool_def: "P << Q \<equiv> \<not>P \<and> Q"

text{*\noindent
Now @{prop"False <<= P"} is provable:
*}

lemma "False <<= P"
by(simp add: le_bool_def)

text{*\noindent
At this point, @{text"[] <<= []"} is not even well-typed.
To make it well-typed,
we need to make lists a type of class @{text ordrel}:*}(*<*)end(*>*)
