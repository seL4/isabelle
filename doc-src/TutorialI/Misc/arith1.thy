(*<*)
theory arith1 = Main:;
(*>*)
lemma "\\<lbrakk> \\<not> m < n; m < n+1 \\<rbrakk> \\<Longrightarrow> m = n";
(**)(*<*)
by(auto);
end
(*>*)
