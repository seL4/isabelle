(*<*)
theory unfoldnested = Main:;
(*>*)
datatype ('a,'b)"term" = Var 'a | App 'b "('a,'b)term_list"
and ('a,'b)term_list = Nil | Cons "('a,'b)term" "('a,'b)term_list"
(*<*)
end
(*>*)
