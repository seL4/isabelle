(*<*)theory Overloading2 = Overloading1:(*>*)

text{*
Of course this is not the only possible definition of the two relations.
Componentwise
*}

instance list :: (ordrel)ordrel
by intro_classes

defs (overloaded)
le_list_def: "xs <<= (ys::'a::ordrel list) \<equiv>
              size xs = size ys \<and> (\<forall>i<size xs. xs!i <<= ys!i)"

text{*
%However, we retract the componetwise comparison of lists and return

Note: only one definition because based on name.
*}
(*<*)end(*>*)

