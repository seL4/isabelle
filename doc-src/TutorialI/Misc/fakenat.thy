(*<*)
theory fakenat = Main:;
(*>*)

text{*\noindent
The type \isaindexbold{nat}\index{*0|bold}\index{*Suc|bold} of natural
numbers is predefined and behaves like
*}

datatype nat = "0" | Suc nat
(*<*)
end
(*>*)
