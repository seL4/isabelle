(*  Title:	IntPrimes.ML
    ID:         $Id$
    Author:	Thomas M. Rasmussen & L C Paulson
    Copyright	2000  University of Cambridge

dvd relation, GCD, Euclid's extended algorithm, primes, congruences
(all on the Integers)

Comparable to Primes theory, but dvd is included here as it is not present in
IntDiv.  Also includes extended GCD and congruences -- not present in Primes. 
*)

eta_contract:=false;


Goal "(abs (z::int) = w) = (z=w & #0 <= z | z=-w & z < #0)";
by (auto_tac (claset(), simpset() addsimps [zabs_def]));  
qed "zabs_eq_iff";


(** gcd lemmas **)

val gcd_non_0 = thm "gcd_non_0";
val gcd_add1 = thm "gcd_add1";
val gcd_commute = thm "gcd_commute";

Goal "gcd (m+k, k) = gcd (m+k, m)";
by (simp_tac (simpset() addsimps [gcd_commute]) 1); 
qed "gcd_add1_eq";

Goal "m <= n ==> gcd (n, n - m) = gcd (n, m)";
by (subgoal_tac "n = m + (n-m)" 1);
by (etac ssubst 1 THEN rtac gcd_add1_eq 1);
by (Asm_simp_tac 1);
qed "gcd_diff2";


(************************************************)
(** Divides relation 'dvd'                     **)
(************************************************)

Goalw [dvd_def] "(m::int) dvd #0";
by (blast_tac (claset() addIs [zmult_0_right RS sym]) 1);
qed "zdvd_0_right";
AddIffs [zdvd_0_right];

Goalw [dvd_def] "(#0 dvd (m::int)) = (m = #0)";
by Auto_tac;
qed "zdvd_0_left";
AddIffs [zdvd_0_left];

Goalw [dvd_def] "#1 dvd (m::int)";
by (Simp_tac 1);
qed "zdvd_1_left";
AddIffs [zdvd_1_left];

Goalw [dvd_def] "m dvd (m::int)";
by (blast_tac (claset() addIs [zmult_1_right RS sym]) 1);
qed "zdvd_refl";
Addsimps [zdvd_refl];

Goalw [dvd_def] "[| m dvd n; n dvd k |] ==> m dvd (k::int)";
by (blast_tac (claset() addIs [zmult_assoc] ) 1);
qed "zdvd_trans";

Goalw [dvd_def] "(m dvd -n) = (m dvd (n::int))";
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zdvd_zminus_iff";  

Goalw [dvd_def] "(-m dvd n) = (m dvd (n::int))";
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zdvd_zminus2_iff";  

Goalw [dvd_def] "[| #0<m; #0<n; m dvd n; n dvd m |] ==> m = (n::int)";
by Auto_tac;
by (asm_full_simp_tac
    (simpset() addsimps [zmult_assoc,zmult_eq_self_iff,
                         int_0_less_mult_iff, zmult_eq_1_iff]) 1);
qed "zdvd_anti_sym";

Goalw [dvd_def] "[| k dvd m; k dvd n |] ==> k dvd (m+n :: int)";
by (blast_tac (claset() addIs [zadd_zmult_distrib2 RS sym]) 1);
qed "zdvd_zadd";

Goalw [dvd_def] "[| k dvd m; k dvd n |] ==> k dvd (m-n :: int)";
by (blast_tac (claset() addIs [zdiff_zmult_distrib2 RS sym]) 1);
qed "zdvd_zdiff";

Goal "[| k dvd m-n; k dvd n |] ==> k dvd (m::int)";
by (subgoal_tac "m=n+(m-n)" 1);
by (etac ssubst 1);
by (blast_tac (claset() addIs [zdvd_zadd]) 1);
by (Simp_tac 1);
qed "zdvd_zdiffD";

Goalw [dvd_def] "k dvd (n::int) ==> k dvd m*n";
by (blast_tac (claset() addIs [zmult_left_commute]) 1);
qed "zdvd_zmult";

Goal "k dvd (m::int) ==> k dvd m*n";
by (stac zmult_commute 1);
by (etac zdvd_zmult 1);
qed "zdvd_zmult2";

(* k dvd m*k *)
AddIffs [zdvd_refl RS zdvd_zmult, zdvd_refl RS zdvd_zmult2];

Goalw [dvd_def] "j*k dvd n ==> j dvd (n::int)";
by (full_simp_tac (simpset() addsimps [zmult_assoc]) 1);
by (Blast_tac 1);
qed "zdvd_zmultD2";

Goal "j*k dvd n ==> k dvd (n::int)";
by (rtac zdvd_zmultD2 1);
by (stac zmult_commute 1);
by (assume_tac 1);
qed "zdvd_zmultD";

Goalw [dvd_def] "[| i dvd m; j dvd (n::int) |] ==> i*j dvd m*n";
by (Clarify_tac 1);
by (res_inst_tac [("x","k*ka")] exI 1);
by (asm_simp_tac (simpset() addsimps zmult_ac) 1);
qed "zdvd_zmult_mono";

Goal "(k dvd n + k*m) = (k dvd (n::int))";
by (rtac iffI 1);
by (etac zdvd_zadd 2);
by (subgoal_tac "n = (n+k*m)-k*m" 1);
by (etac ssubst 1);
by (etac zdvd_zdiff 1);
by (ALLGOALS Simp_tac);
qed "zdvd_reduce";

Goalw [dvd_def] "[| f dvd m; f dvd (n::int) |] ==> f dvd m mod n";
by (auto_tac (claset(), simpset() addsimps [zmod_zmult_zmult1]));
qed "zdvd_zmod";

Goal "[| k dvd m mod n;  k dvd n |] ==> k dvd (m::int)";
by (subgoal_tac "k dvd n*(m div n) + m mod n" 1);
by (asm_simp_tac (simpset() addsimps [zdvd_zadd, zdvd_zmult2]) 2);
by (asm_full_simp_tac (simpset() addsimps [zmod_zdiv_equality RS sym]) 1);
qed "zdvd_zmod_imp_zdvd";

Goalw [dvd_def] "(k dvd n) = (n mod (k::int) = #0)";
by (auto_tac (claset(), simpset() addsimps [zmod_zmult_self2]));  
qed "zdvd_iff_zmod_eq_0";

Goal "[| ~k<#0; k~=#0 |] ==> #0<(k::int)";
by (arith_tac 1);
val lemma = result();

Goalw [dvd_def] "[| #0<m; m<n |] ==> ~n dvd (m::int)";
by Auto_tac;
by (subgoal_tac "#0<n" 1);
by (blast_tac (claset() addIs [zless_trans]) 2);
by (asm_full_simp_tac (simpset() addsimps [int_0_less_mult_iff]) 1); 
by (subgoal_tac "n*k < n*#1" 1);
by (dtac (zmult_zless_cancel1 RS iffD1) 1); 
by Auto_tac;  
qed "zdvd_not_zless";

Goal "(int m dvd z) = (m dvd nat(abs z))";
by (auto_tac (claset(), 
       simpset() addsimps [dvd_def, nat_abs_mult_distrib]));  
by (auto_tac (claset(), simpset() addsimps [nat_eq_iff, zabs_eq_iff]));  
by (res_inst_tac [("x","-(int k)")] exI 2);
by (auto_tac (claset(), simpset() addsimps [zmult_int RS sym]));  
qed "int_dvd_iff";

Goal "(z dvd int m) = (nat(abs z) dvd m)";
by (auto_tac (claset(), 
       simpset() addsimps [dvd_def, zabs_def, zmult_int RS sym]));  
by (res_inst_tac [("x","nat k")] exI 3); 
by (res_inst_tac [("x","-(int k)")] exI 2);
by (res_inst_tac [("x","nat (-k)")] exI 1);
by (cut_inst_tac [("k","m")] int_less_0_conv 3);
by (cut_inst_tac [("k","m")] int_less_0_conv 1);
by (auto_tac (claset(), 
         simpset() addsimps [int_0_le_mult_iff, zmult_less_0_iff,
                             nat_mult_distrib RS sym, nat_eq_iff2]));  
qed "dvd_int_iff";

Goal "(nat z dvd m) = (if #0 <= z then (z dvd int m) else m=0)";
by (auto_tac (claset(), simpset() addsimps [dvd_def, zmult_int RS sym]));  
by (res_inst_tac [("x","nat k")] exI 1);
by (cut_inst_tac [("k","m")] int_less_0_conv 1);
by (auto_tac (claset(), 
         simpset() addsimps [int_0_le_mult_iff, zmult_less_0_iff,
                             nat_mult_distrib RS sym, nat_eq_iff2]));  
qed "nat_dvd_iff";

Goal "(-z dvd w) = (z dvd (w::int))";
by (auto_tac (claset(), simpset() addsimps [dvd_def]));  
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;  
qed "zminus_dvd_iff";

Goal "(z dvd -w) = (z dvd (w::int))";
by (auto_tac (claset(), simpset() addsimps [dvd_def]));  
by (dtac (zminus_equation RS iffD1) 1);
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;  
qed "dvd_zminus_iff";
AddIffs [zminus_dvd_iff, dvd_zminus_iff];


(************************************************)
(** Euclid's Algorithm and GCD                 **)
(************************************************)

Goal "zgcd(m,#0) = abs m";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def]) 1); 
qed "zgcd_0";
Addsimps [zgcd_0];

Goal"zgcd(#0,m) = abs m";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def]) 1); 
qed "zgcd_0_left";
Addsimps [zgcd_0_left];

Goal "zgcd(-m,n) = zgcd(m,n)";
by (simp_tac (simpset() addsimps [zgcd_def]) 1); 
qed "zgcd_zminus";
Addsimps [zgcd_zminus];

Goal "zgcd(m,-n) = zgcd(m,n)";
by (simp_tac (simpset() addsimps [zgcd_def]) 1); 
qed "zgcd_zminus2";
Addsimps [zgcd_zminus2];

Goal "#0<n ==> zgcd(m,n) = zgcd (n, m mod n)";
by (forw_inst_tac [("b","n"), ("a","m")] pos_mod_sign 1);
by (asm_simp_tac (simpset() addsimps [zgcd_def, zabs_def, nat_mod_distrib]) 1);
by (cut_inst_tac [("a","-m"),("b","n")] zmod_zminus1_eq_if 1);
by (auto_tac (claset(), 
              simpset() addsimps [gcd_non_0, nat_mod_distrib RS sym,
                                  zmod_zminus1_eq_if]));
by (forw_inst_tac [("a","m")] pos_mod_bound 1);
by (asm_simp_tac (simpset() addsimps [nat_diff_distrib]) 1);  
by (rtac gcd_diff2 1);
by (asm_full_simp_tac (simpset() addsimps [nat_le_eq_zle]) 1); 
qed "zgcd_non_0";

Goal "zgcd(m,n) = zgcd (n, m mod n)";
by (zdiv_undefined_case_tac "n = #0" 1);
by (auto_tac
    (claset(),
     simpset() addsimps [linorder_neq_iff, zgcd_non_0]));
by (cut_inst_tac [("m","-m"),("n","-n")] zgcd_non_0 1);
by Auto_tac;  
qed "zgcd_eq";

Goal "zgcd(m,#1) = #1";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def]) 1); 
qed "zgcd_1";
Addsimps [zgcd_1];

Goal "(zgcd(#0,m) = #1) = (abs m = #1)";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def]) 1); 
qed "zgcd_0_1_iff";
Addsimps [zgcd_0_1_iff];

Goal "zgcd(m,n) dvd m";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def, int_dvd_iff]) 1); 
qed "zgcd_zdvd1";

Goal "zgcd(m,n) dvd n";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def, int_dvd_iff]) 1); 
qed "zgcd_zdvd2";
AddIffs [zgcd_zdvd1, zgcd_zdvd2];

Goal "k dvd zgcd(m,n) = (k dvd m & k dvd n)";
by (simp_tac (simpset() addsimps [zgcd_def, zabs_def, int_dvd_iff, 
                                  dvd_int_iff, nat_dvd_iff]) 1); 
qed "zgcd_greatest_iff";

Goal "zgcd(m,n) = zgcd(n,m)";
by (simp_tac (simpset() addsimps [zgcd_def, thm"gcd_commute"]) 1); 
qed "zgcd_commute";

Goal "zgcd(#1,m) = #1";
by (simp_tac (simpset() addsimps [zgcd_def, thm"gcd_1_left"]) 1); 
qed "zgcd_1_left";
Addsimps [zgcd_1_left];

Goal "zgcd(zgcd(k,m),n) = zgcd(k,zgcd(m,n))";
by (simp_tac (simpset() addsimps [zgcd_def, thm"gcd_assoc"]) 1); 
qed "zgcd_assoc";

Goal "zgcd(k,zgcd(m,n)) = zgcd(m,zgcd(k,n))";
by (rtac (zgcd_commute RS trans) 1);
by (rtac (zgcd_assoc RS trans) 1);
by (rtac (zgcd_commute RS arg_cong) 1);
qed "zgcd_left_commute";

(*Addition is an AC-operator*)
bind_thms ("zgcd_ac", [zgcd_assoc, zgcd_commute, zgcd_left_commute]);

val gcd_mult_distrib2 = thm"gcd_mult_distrib2";

Goal "#0<=k ==> k * zgcd(m,n) = zgcd(k*m, k*n)";
by (asm_simp_tac 
    (simpset() delsimps [zmult_zminus_right] 
	       addsimps [zmult_zminus_right RS sym, 
                         nat_mult_distrib, zgcd_def, zabs_def, 
                         zmult_less_0_iff, gcd_mult_distrib2 RS sym, 
                         zmult_int RS sym]) 1); 
qed "zgcd_zmult_distrib2";

Goal "zgcd(k*m, k*n) = abs k * zgcd(m,n)";
by (simp_tac (simpset() addsimps [zabs_def, zgcd_zmult_distrib2]) 1);
qed "zgcd_zmult_distrib2_abs";


Goal "#0<=m ==> zgcd(m,m) = m";
by (cut_inst_tac [("k","m"),("m","#1"),("n","#1")] zgcd_zmult_distrib2 1);
by (ALLGOALS Asm_full_simp_tac);
qed "zgcd_self";
Addsimps [zgcd_self];

Goal "#0<=k ==> zgcd(k, k*n) = k";
by (cut_inst_tac [("k","k"),("m","#1"),("n","n")] zgcd_zmult_distrib2 1);
by (ALLGOALS Asm_full_simp_tac);
qed "zgcd_zmult_eq_self";
Addsimps [zgcd_zmult_eq_self];

Goal "#0<=k ==> zgcd(k*n, k) = k";
by (cut_inst_tac [("k","k"),("m","n"),("n","#1")] zgcd_zmult_distrib2 1);
by (ALLGOALS Asm_full_simp_tac);
qed "zgcd_zmult_eq_self2";
Addsimps [zgcd_zmult_eq_self2];

Goal "[| zgcd(n,k)=#1; k dvd m*n; #0 <= m |] ==> k dvd m";
by (subgoal_tac "m = zgcd(m*n, m*k)" 1);
by (etac ssubst 1 THEN rtac (zgcd_greatest_iff RS iffD2) 1);
by (ALLGOALS (asm_simp_tac (simpset() 
      addsimps [zgcd_zmult_distrib2 RS sym,int_0_le_mult_iff])));
val lemma = result();

Goal "[| zgcd(n,k)=#1; k dvd m*n |] ==> k dvd m";
by (case_tac "#0 <= m" 1);
by (blast_tac (claset() addIs [lemma]) 1); 
by (subgoal_tac "k dvd -m" 1);
by (rtac lemma 2);
by Auto_tac;  
qed "zrelprime_zdvd_zmult";

Goalw [zprime_def] "[| p:zprime; ~p dvd n |] ==> zgcd(n,p) = #1";
by Auto_tac;  
qed "zprime_imp_zrelprime";

Goal "[| p:zprime; #0<n; n<p |] ==> zgcd(n,p) = #1";
by (etac zprime_imp_zrelprime 1);
by (etac zdvd_not_zless 1);
by (assume_tac 1);
qed "zless_zprime_imp_zrelprime";

Goal "[| #0<=(m::int); p:zprime; p dvd m*n |] ==> p dvd m | p dvd n";
by Safe_tac;
by (rtac zrelprime_zdvd_zmult 1);
by (rtac zprime_imp_zrelprime 1);
by Auto_tac;
qed "zprime_zdvd_zmult";

val gcd_add_mult = thm "gcd_add_mult";

Goal "zgcd(m + n*k, n) = zgcd(m,n)";
by (rtac (zgcd_eq RS trans) 1);
by (simp_tac (simpset() addsimps [zmod_zadd1_eq]) 1);
by (rtac (zgcd_eq RS sym) 1);
qed "zgcd_zadd_zmult";
Addsimps [zgcd_zadd_zmult];


Goal "zgcd(m,n) dvd zgcd(k*m,n)";
by (simp_tac (simpset() addsimps [zgcd_greatest_iff]) 1); 
by (blast_tac (claset() addIs [zdvd_trans]) 1); 
qed "zgcd_zdvd_zgcd_zmult";

Goal "zgcd(k,n) = #1 ==> zgcd(k*m,n) dvd zgcd(m,n)";
by (simp_tac (simpset() addsimps [zgcd_greatest_iff]) 1); 
by (res_inst_tac [("n","k")] zrelprime_zdvd_zmult 1);
by (simp_tac (simpset() addsimps [zmult_commute]) 2); 
by (subgoal_tac "zgcd (k, zgcd (k * m, n)) =  zgcd (k * m, zgcd (k, n))" 1);
by (Asm_full_simp_tac 1); 
by (simp_tac (simpset() addsimps zgcd_ac) 1); 
qed "zgcd_zmult_zdvd_zgcd";

val gcd_mult_cancel = thm "gcd_mult_cancel";

Goal "zgcd(k,n) = #1 ==> zgcd(k*m, n) = zgcd(m,n)";
by (asm_full_simp_tac (simpset() addsimps [zgcd_def, 
                           nat_abs_mult_distrib, gcd_mult_cancel]) 1); 
qed "zgcd_zmult_cancel";

Goal "[| zgcd(k,m) = #1; zgcd(n,m) = #1 |] ==> zgcd(k*n,m) = #1";
by (asm_simp_tac (simpset() addsimps [zgcd_zmult_cancel]) 1);
qed "zgcd_zgcd_zmult";

Goal "#0<m ==> (m dvd n) = (zgcd(n,m) = m)";
by Safe_tac;
by (res_inst_tac [("n","zgcd(n,m)")] zdvd_trans 2);
by (rtac zgcd_zdvd1 3);
by (ALLGOALS Asm_simp_tac);
by (rewtac dvd_def);
by Auto_tac;
qed "zdvd_iff_zgcd";


(************************************************)
(** Congruences                                **)
(************************************************)

Goalw [zcong_def] "[a=b](mod #1)";
by Auto_tac;
qed "zcong_1";
Addsimps [zcong_1];

Goalw [zcong_def] "[k = k] (mod m)";
by Auto_tac;
qed "zcong_refl";
Addsimps [zcong_refl];

Goalw [zcong_def,dvd_def] "[a = b](mod m) = [b = a](mod m)";
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zcong_sym";

Goalw [zcong_def]
     "[| [a = b] (mod m); [c = d] (mod m) |] ==> [a+c = b+d](mod m)";
by (res_inst_tac [("s","(a-b)+(c-d)")] subst 1);
by (rtac zdvd_zadd 2);
by Auto_tac;
qed "zcong_zadd";

Goalw [zcong_def]
     "[| [a = b] (mod m); [c = d] (mod m) |] ==> [a-c = b-d](mod m)";
by (res_inst_tac [("s","(a-b)-(c-d)")] subst 1);
by (rtac zdvd_zdiff 2);
by Auto_tac;
qed "zcong_zdiff";

Goalw [zcong_def,dvd_def]
     "[| [a = b](mod m); [b = c](mod m) |] ==> [a = c](mod m)";
by Auto_tac;
by (res_inst_tac [("x","k+ka")] exI 1);
by (asm_full_simp_tac (simpset() addsimps zadd_ac@[zadd_zmult_distrib2]) 1);
qed "zcong_trans";
 
Goal "[| [a = b] (mod m); [c = d] (mod m) |] ==> [a*c = b*d](mod m)";
by (res_inst_tac [("b","b*c")] zcong_trans 1);
by (rewtac zcong_def);
by (res_inst_tac [("s","c*(a-b)")] subst 1);
by (res_inst_tac [("s","b*(c-d)")] subst 3);
by (blast_tac (claset() addIs [zdvd_zmult]) 4);
by (blast_tac (claset() addIs [zdvd_zmult]) 2);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [zdiff_zmult_distrib2,
                                                zmult_commute])));
qed "zcong_zmult";

Goal "[a = b] (mod m) ==> [a*k = b*k](mod m)";
by (rtac zcong_zmult 1);
by (ALLGOALS Asm_simp_tac);
qed "zcong_scalar";

Goal "[a = b] (mod m) ==> [k*a = k*b](mod m)";
by (rtac zcong_zmult 1);
by (ALLGOALS Asm_simp_tac);
qed "zcong_scalar2";

Goalw [zcong_def] "[a*m = b*m](mod m)";
by (rtac zdvd_zdiff 1);
by (ALLGOALS Simp_tac);
qed "zcong_zmult_self";

Goalw [zcong_def]
      "[| p:zprime; #0<a; [a*a = #1](mod p) |] \
\     ==> [a=#1](mod p) | [a = p-#1](mod p)";
by (rtac zprime_zdvd_zmult 1);
by (res_inst_tac [("s","a*a - #1 + p*(#1-a)")] subst 3);
by (simp_tac (simpset() addsimps [zdvd_reduce]) 4);
by (ALLGOALS (asm_simp_tac (simpset() 
      addsimps [zdiff_zmult_distrib,zmult_commute,zdiff_zmult_distrib2])));
qed "zcong_square";

Goal "[| #0<=m; zgcd(k,m) = #1 |] ==> [a*k = b*k](mod m) = [a = b](mod m)";
by Safe_tac;
by (blast_tac (claset() addIs [zcong_scalar]) 2);
by (case_tac "b<a" 1);
by (stac zcong_sym 2);
by (rewrite_goals_tac [zcong_def]);
by (ALLGOALS (rtac zrelprime_zdvd_zmult));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [zdiff_zmult_distrib])));
by (subgoal_tac "m dvd (-(a*k - b*k))" 1);
by (asm_full_simp_tac (simpset() addsimps [zminus_zdiff_eq]) 1);
by (stac zdvd_zminus_iff 1);
by (assume_tac 1);
qed "zcong_cancel";

Goal "[| #0<=m; zgcd(k,m) = #1 |] ==> [k*a = k*b](mod m) = [a = b](mod m)";
by (asm_simp_tac (simpset() addsimps [zmult_commute,zcong_cancel]) 1);
qed "zcong_cancel2";

Goalw [zcong_def,dvd_def]
      "[| [a = b] (mod m);  [a = b] (mod n);  zgcd(m,n) = #1 |] \
\     ==> [a=b](mod m*n)";
by Auto_tac;
by (subgoal_tac "m dvd n*ka" 1);
by (subgoal_tac "m dvd ka" 1);
by (case_tac "#0<=ka" 2);
by (stac (zdvd_zminus_iff RS sym) 3);
by (res_inst_tac [("n","n")] zrelprime_zdvd_zmult 3);
by (asm_simp_tac (simpset() addsimps [zgcd_commute]) 3);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute,zdvd_zminus_iff]) 3);
by (res_inst_tac [("n","n")] zrelprime_zdvd_zmult 2);
by (asm_simp_tac (simpset() addsimps [zgcd_commute]) 2);
by (asm_full_simp_tac (simpset() addsimps [zmult_commute]) 2);
by (auto_tac (claset(), simpset() addsimps [dvd_def]));  
by (blast_tac (claset() addIs [sym]) 1); 
qed "zcong_zgcd_zmult_zmod";

Goalw [zcong_def,dvd_def] 
      "[| #0<=a; a<m; #0<=b; b<m; [a = b] (mod m) |] ==> a = b";
by Auto_tac;  
by (dres_inst_tac [("f", "%z. z mod m")] arg_cong 1);  
by (cut_inst_tac [("z","a"),("w","b")] zless_linear 1);
by Auto_tac;  
by (subgoal_tac "(a - b) mod m = a-b" 2);
by (rtac mod_pos_pos_trivial 3); 
by Auto_tac;
by (subgoal_tac "(m + (a - b)) mod m = m + (a - b)" 1);
by (rtac mod_pos_pos_trivial 2); 
by Auto_tac;  
qed "zcong_zless_imp_eq";

Goal "[| p:zprime; #0<a; a<p; [a*a = #1](mod p) |] ==> a = #1 | a = p-#1";
by (cut_inst_tac [("p","p"),("a","a")] zcong_square 1);
by (full_simp_tac (simpset() addsimps [zprime_def]) 1); 
by (auto_tac (claset() addIs [zcong_zless_imp_eq], simpset())); 
qed "zcong_square_zless";

Goalw [zcong_def] "[| #0<a; a<m; #0<b; b<a |] ==> ~[a = b] (mod m) ";
by (rtac zdvd_not_zless 1);
by Auto_tac;
qed "zcong_not";

Goalw [zcong_def,dvd_def] "[| #0<=a; a<m; [a=#0](mod m) |] ==> a = #0";
by Auto_tac;
by (subgoal_tac "#0<m" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [int_0_le_mult_iff]) 1);
by (subgoal_tac "m*k<m*#1" 1);
by (dtac (zmult_zless_cancel1 RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [linorder_neq_iff]));
qed "zcong_zless_0";

Goal "#0<m ==> (EX! b. #0<=b & b<m & [a = b] (mod m))";
by Auto_tac;
by (subgoal_tac "[b = y] (mod m)" 2);
by (case_tac "b=#0" 2);
by (case_tac "y=#0" 3);
by (auto_tac (claset() addIs [zcong_trans,zcong_zless_0,
                              zcong_zless_imp_eq,order_less_le],
              simpset() addsimps [zcong_sym]));
by (rewrite_goals_tac [zcong_def,dvd_def]);
by (res_inst_tac [("x","a mod m")] exI 1);
by (auto_tac (claset(),simpset() addsimps [pos_mod_sign,pos_mod_bound]));
by (res_inst_tac [("x","-(a div m)")] exI 1);
by (cut_inst_tac [("a","a"),("b","m")] zmod_zdiv_equality 1);
by Auto_tac;
qed "zcong_zless_unique";

Goalw [zcong_def,dvd_def] "([a = b] (mod m)) = (EX k. b = a + m*k)"; 
by Auto_tac;
by (ALLGOALS (res_inst_tac [("x","-k")] exI));
by Auto_tac;
qed "zcong_iff_lin";

Goal "[| #0<m; zgcd(a,m) = #1; [a = b] (mod m) |] ==> zgcd(b,m) = #1";
by (auto_tac (claset(),simpset() addsimps [zcong_iff_lin]));
qed "zgcd_zcong_zgcd";

Goal "[| a=c; b=d |] ==> a-b = c-(d::int)";
by Auto_tac;
val lemma = result();

Goal "a - b = (m::int) * (a div m - b div m) + (a mod m - b mod m)";
by (res_inst_tac [("s","(m * (a div m) + a mod m) - \
\                 (m * (b div m) + b mod m)")] trans 1);
by (simp_tac (simpset() addsimps [zdiff_zmult_distrib2]) 2);
by (rtac lemma 1);
by (ALLGOALS (rtac zmod_zdiv_equality));
val lemma = result();

Goalw [zcong_def] "[a = b] (mod m) = [a mod m = b mod m](mod m)";
by (res_inst_tac [("t","a-b")] ssubst 1);
by (res_inst_tac [("m","m")] lemma 1);
by (rtac trans 1);
by (res_inst_tac [("k","m"),("m","a div m - b div m")] zdvd_reduce 2);
by (simp_tac (simpset() addsimps [zadd_commute]) 1);
qed "zcong_zmod";

Goal "#0<m ==> [a = b] (mod m) = (a mod m = b mod m)";
by Auto_tac;
by (res_inst_tac [("m","m")] zcong_zless_imp_eq 1);
by (stac (zcong_zmod RS sym) 5);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_bound,pos_mod_sign])));
by (rewrite_goals_tac [zcong_def,dvd_def]);
by (res_inst_tac [("x","a div m - b div m")] exI 1);
by (res_inst_tac [("m1","m")] (lemma RS trans) 1);
by Auto_tac;
qed "zcong_zmod_eq";

Goal "[a = b] (mod -m) = [a = b] (mod m)";
by (auto_tac (claset(), simpset() addsimps [zcong_def]));  
qed "zcong_zminus";
AddIffs [zcong_zminus];

Goal "[a = b] (mod #0) = (a = b)";
by (auto_tac (claset(), simpset() addsimps [zcong_def]));  
qed "zcong_zero";
AddIffs [zcong_zero];

Goal "[a = b] (mod m) = (a mod m = b mod m)";
by (zdiv_undefined_case_tac "m = #0" 1);
by (case_tac "#0<m" 1);
by (asm_simp_tac (simpset() addsimps [zcong_zmod_eq]) 1); 
by (res_inst_tac [("t","m")] (zminus_zminus RS subst) 1); 
by (stac zcong_zminus 1);
by (stac zcong_zmod_eq 1);
by (arith_tac 1); 
(*FIXME: finish this proof?*)

(************************************************)
(** Modulo                                     **)
(************************************************)

Goalw [dvd_def] "[| #0<(m::int); m dvd b |] ==> (a mod b mod m) = (a mod m)";
by Auto_tac;
by (stac (zcong_zmod_eq RS sym) 1);
by (stac zcong_iff_lin 2);
by (res_inst_tac [("x","k*(a div (m*k))")] exI 2);
by (stac zadd_commute 2);
by (stac (zmult_assoc RS sym) 2);
by (rtac zmod_zdiv_equality 2);
by (assume_tac 1);
qed "zmod_zdvd_zmod";


(************************************************)
(** Extended GCD                               **)
(************************************************)

val [xzgcda_eq] = xzgcda.simps;
Delsimps xzgcda.simps;

Goal "zgcd(r',r) = k --> #0 < r --> \
\     (EX sn tn. xzgcda (m,n,r',r,s',s,t',t) = (k,sn,tn))";
by (res_inst_tac [("u","m"),("v","n"),("w","r'"),("x","r"),
                  ("y","s'"),("z","s"),("aa","t'"),("ab","t")] 
                  xzgcda.induct 1);
by (stac zgcd_eq 1);
by (stac xzgcda_eq 1);
by Auto_tac;
by (case_tac "r' mod r = #0" 1);
by (forw_inst_tac [("a","r'")] pos_mod_sign 2);
by Auto_tac;  
by (arith_tac 2);
by (rtac exI 1);
by (rtac exI 1);
by (stac xzgcda_eq 1);
by Auto_tac;  
by (asm_full_simp_tac (simpset() addsimps [zabs_def]) 1); 
val lemma1 = result();

Goal "(EX sn tn. xzgcda (m,n,r',r,s',s,t',t) = (k,sn,tn)) --> #0 < r --> \
\     zgcd(r',r) = k";
by (res_inst_tac [("u","m"),("v","n"),("w","r'"),("x","r"),
                  ("y","s'"),("z","s"),("aa","t'"),("ab","t")] 
                  xzgcda.induct 1);
by (stac zgcd_eq 1);
by (stac xzgcda_eq 1);
by (auto_tac (claset(), simpset() addsimps [linorder_not_le]));  
by (case_tac "r' mod r = #0" 1);
by (forw_inst_tac [("a","r'")] pos_mod_sign 2);
by Auto_tac;  
by (arith_tac 2);
by (eres_inst_tac [("P","xzgcda ?u = ?v")] rev_mp 1); 
by (stac xzgcda_eq 1);
by Auto_tac;  
by (asm_full_simp_tac (simpset() addsimps [zabs_def]) 1); 
val lemma2 = result();

Goalw [xzgcd_def] "#0 < n ==> (zgcd(m,n) = k) = (EX s t. xzgcd m n = (k,s,t))"; 
by (rtac iffI 1);
by (rtac (lemma2 RS mp RS mp) 2);
by (rtac (lemma1 RS mp RS mp) 1);
by Auto_tac;
qed "xzgcd_correct";

(* xzgcd linear *)

Goal "(a-r*b)*m + (c-r*d)*(n::int) = (a*m + c*n) - r*(b*m + d*n)";
by (simp_tac (simpset() addsimps [zdiff_zmult_distrib,zadd_zmult_distrib2,
                                  zmult_assoc]) 1);
val lemma = result();

Goal "[| r' = s'*m + t'*n; r = s*m + t*n |] \
\    ==> (r' mod r) = (s' - (r' div r)*s)*m + (t' - (r' div r)*t)*(n::int)"; 
by (rtac trans 1);
by (rtac (lemma RS sym) 2);
by (Asm_simp_tac 1);
by (stac eq_zdiff_eq 1);
by (rtac (trans RS sym) 1);
by (res_inst_tac [("b","s*m + t*n")] zmod_zdiv_equality 1);
by (simp_tac (simpset() addsimps [zmult_commute]) 1);
val lemma = result();

bind_thm ("order_le_neq_implies_less", [order_less_le, conjI] MRS iffD2);

Goal "#0<r --> xzgcda(m,n,r',r,s',s,t',t) = (rn,sn,tn) \
\          --> r' = s'*m + t'*n -->  r = s*m + t*n --> rn = sn*m + tn*n";
by (res_inst_tac [("u","m"),("v","n"),("w","r'"),("x","r"),
                  ("y","s'"),("z","s"),("aa","t'"),("ab","t")] 
                  xzgcda.induct 1);
by (stac xzgcda_eq 1);
by (Simp_tac 1);
by (REPEAT (rtac impI 1));
by (case_tac "r' mod r = #0" 1);
by (asm_full_simp_tac (simpset() addsimps [xzgcda_eq]) 1);
by (SELECT_GOAL Safe_tac 1);
by (subgoal_tac "#0 < r' mod r" 1);
by (rtac order_le_neq_implies_less 2);
by (rtac pos_mod_sign 2);
by (cut_inst_tac [("m","m"),("n","n"),("r'","r'"),("r","r"),
                  ("s'","s'"),("s","s"),("t'","t'"),("t","t")] 
                 lemma 1);
by Auto_tac;
qed_spec_mp "xzgcda_linear";

Goalw [xzgcd_def] "[| #0<n; xzgcd m n = (r,s,t) |] ==> r = s*m + t*n";
by (etac xzgcda_linear 1);
by (assume_tac 1);
by Auto_tac;
qed "xzgcd_linear";

Goal "[| #0<n; zgcd(m,n) = k |] ==> (EX s t. k = s*m + t*n)";
by (asm_full_simp_tac (simpset() addsimps [xzgcd_correct]) 1);
by Safe_tac;
by (REPEAT (rtac exI 1));
by (etac xzgcd_linear 1);
by Auto_tac;
qed "zgcd_ex_linear";

Goal "[| #0<n; zgcd(a,n) = #1 |] ==> EX x. [a*x = #1](mod n)";
by (cut_inst_tac [("m","a"),("n","n"),("k","#1")] zgcd_ex_linear 1);
by Safe_tac;
by (res_inst_tac [("x","s")] exI 1);
by (res_inst_tac [("b","s*a+t*n")] zcong_trans 1);
by (Asm_simp_tac 2);
by (rewtac zcong_def);
by (simp_tac (simpset() addsimps [zmult_commute,zdvd_zminus_iff]) 1);
qed "zcong_lineq_ex";

Goal "[| #0<n; zgcd(a,n) = #1 |] ==> EX! x. #0<=x & x<n & [a*x = b](mod n)";
by Auto_tac;
by (rtac zcong_zless_imp_eq 2);
by (stac (zcong_cancel2 RS sym) 6);
by (rtac zcong_trans 8);
by (ALLGOALS Asm_simp_tac);
by (asm_full_simp_tac (simpset() addsimps [zcong_sym]) 2);
by (cut_inst_tac [("a","a"),("n","n")] zcong_lineq_ex 1);
by Auto_tac;
by (res_inst_tac [("x","x*b mod n")] exI 1);
by Safe_tac;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [pos_mod_bound,pos_mod_sign])));
by (stac zcong_zmod 1);
by (stac (zmod_zmult1_eq RS sym) 1);
by (stac (zcong_zmod RS sym) 1);
by (subgoal_tac "[a*x*b = #1*b](mod n)" 1);
by (rtac zcong_zmult 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [zmult_assoc])));
qed "zcong_lineq_unique";

