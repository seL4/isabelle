(*<*)theory Overloading1 = Main:(*>*)

subsubsection{*Controlled overloading with type classes*}

text{*
We now start with the theory of ordering relations, which we want to phrase
in terms of the two binary symbols @{text"<<"} and @{text"<<="}: they have
been chosen to avoid clashes with @{text"\<le>"} and @{text"<"} in theory @{text
Main}. To restrict the application of @{text"<<"} and @{text"<<="} we
introduce the class @{text ordrel}:
*}

axclass ordrel < "term"

text{*\noindent
This is a degenerate form of axiomatic type class without any axioms.
Its sole purpose is to restrict the use of overloaded constants to meaningful
instances:
*}

consts
  "<<"        :: "('a::ordrel) \<Rightarrow> 'a \<Rightarrow> bool"             (infixl 50)
  "<<="       :: "('a::ordrel) \<Rightarrow> 'a \<Rightarrow> bool"             (infixl 50)

instance bool :: ordrel
by intro_classes

defs (overloaded)
le_bool_def:  "P <<= Q \<equiv> P \<longrightarrow> Q"
less_bool_def: "P << Q \<equiv> \<not>P \<and> Q"

text{*
Now @{prop"False <<= False"} is provable
*}

lemma "False <<= False"
by(simp add: le_bool_def)

text{*\noindent
whereas @{text"[] <<= []"} is not even welltyped. In order to make it welltyped
we need to make lists a type of class @{text ordrel}:*}(*<*)end(*>*)
