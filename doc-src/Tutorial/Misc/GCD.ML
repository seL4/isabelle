Goal "gcd(m,0) = m";
by(resolve_tac [trans] 1);
by(resolve_tac gcd.rules 1);
by(Simp_tac 1);
qed "gcd_0";
Addsimps [gcd_0];

Goal "!!n. n ~= 0 ==> gcd(m,n) = gcd(n, m mod n)";
by(resolve_tac [trans] 1);
by(resolve_tac gcd.rules 1);
by(Asm_simp_tac 1);
qed "gcd_not_0";
Addsimps [gcd_not_0];

