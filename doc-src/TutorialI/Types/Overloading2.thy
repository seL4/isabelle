(*<*)theory Overloading2 = Overloading1:(*>*)

text{*
Of course this is not the only possible definition of the two relations.
Componentwise comparison of lists of equal length also makes sense. This time
the elements of the list must also be of class @{text ordrel} to permit their
comparison:
*}

instance list :: (ordrel)ordrel
by intro_classes

defs (overloaded)
le_list_def: "xs <<= (ys::'a::ordrel list) \<equiv>
              size xs = size ys \<and> (\<forall>i<size xs. xs!i <<= ys!i)"

text{*\noindent
The infix function @{text"!"} yields the nth element of a list.
%However, we retract the componetwise comparison of lists and return
%Note: only one definition because based on name.
*}(*<*)end(*>*)
