(*<*)
theory pairs = Main:;
term(*>*) "let (x,y) = f z in (y,x)";
(*<*)
term(*>*) "case xs of [] \\<Rightarrow> 0 | (x,y)#zs \\<Rightarrow> x+y"
(**)(*<*)
end
(*>*)
