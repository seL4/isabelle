(*<*)
theory unfoldnested = Main:;
(*>*)
datatype ('v,'f)"term" = Var 'v | App 'f "('v,'f)term_list"
and ('v,'f)term_list = Nil | Cons "('v,'f)term" "('v,'f)term_list"
(*<*)
end
(*>*)
