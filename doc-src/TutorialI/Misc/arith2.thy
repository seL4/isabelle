(*<*)
theory arith2 = Main:;
(*>*)
lemma "min i (max j (k*k)) = max (min (k*k) i) (min i (j::nat))";
by(arith);
(**)(*<*)
end
(*>*)
