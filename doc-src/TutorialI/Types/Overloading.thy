(*<*)theory Overloading = Overloading1:(*>*)
instance list :: ("term")ordrel
by intro_classes

text{*\noindent
This \isacommand{instance} declaration can be read like the declaration of
a function on types.  The constructor @{text list} maps types of class @{text
term} (all HOL types), to types of class @{text ordrel};
in other words,
if @{text"ty :: term"} then @{text"ty list :: ordrel"}.
Of course we should also define the meaning of @{text <<=} and
@{text <<} on lists:
*}

defs (overloaded)
prefix_def:
  "xs <<= (ys::'a::ordrel list)  \<equiv>  \<exists>zs. ys = xs@zs"
strict_prefix_def:
  "xs << (ys::'a::ordrel list)   \<equiv>  xs <<= ys \<and> xs \<noteq> ys"
(*<*)end(*>*)
