theory ExamplesAbort = HoareAbort:

syntax guarded_com :: "'bool \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("_ \<rightarrow> _" 60)
translations "P \<rightarrow> c" == "IF P THEN c ELSE Abort FI"

lemma "VARS x y z::nat
 {y = z & z \<noteq> 0} z \<noteq> 0 \<rightarrow> x := y div z {x = 1}"
by vcg_simp

lemma "VARS (a::int list) i
 {True}
 i := 0;
 WHILE i < length a
 INV {i <= length a}
 DO i < length a \<rightarrow> a := a[i := 7];
    i := i+1
 OD
 {True}"
apply vcg_simp
apply arith
done

end
