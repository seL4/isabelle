
header {* The mimimality principle *};

theory Minimal = Main:;

consts
  rel :: "'a => 'a => bool"  (infixl "<<" 50);
axioms
  induct: "(ALL m. m << n --> P m ==> P n) ==> P n";

theorem "A ~= {} ==> EX n. n:A & (ALL m. m << n --> m ~: A)"
  (concl is "Ex ?minimal");
proof -;
  assume "A ~= {}";
  hence "EX n. n:A"; by blast;
  thus ?thesis;
  proof;
    fix n; assume h: "n:A";
    have "n:A --> Ex ?minimal" (is "?P n");
    proof (rule induct [of n]);
      fix m;
      assume hyp: "ALL m. m << n --> ?P m";
      show "?P n";
      proof;
	show "Ex ?minimal";
	proof (rule case_split);
	  assume "EX m. m << n & m:A";
	  with hyp; show ?thesis; by blast;
	next;
	  assume "~ (EX m. m << n & m:A)";
	  with h; have "?minimal n"; by blast;
	  thus ?thesis; ..;
	qed;
      qed;
    qed;
    thus ?thesis; ..;
  qed;
qed;

text {* \medskip Prefer a short, tactic script-style proof? *};

theorem "A ~= {} ==> EX n. n:A & (ALL m. m << n --> m ~: A)";
proof -;
  assume "A ~= {}";
  {{; fix n; have "n:A --> ?thesis"; by (rule induct [of n]) blast; }};
  thus ?thesis; by (force! simp add: not_empty);
qed;

end;
