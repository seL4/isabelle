(*<*)
theory fakenat = Main:;
(*>*)

text{*\noindent
The type \isaindexbold{nat} of natural numbers is predefined and
behaves like
*}

datatype nat = "0" | Suc nat
(*<*)
end
(*>*)
