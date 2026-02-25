section\<open>Main ZF Theory: Everything Except AC\<close>

theory ZF imports List IntDiv CardinalArith begin

(*The theory of "iterates" logically belongs to Nat, but can't go there because
  primrec isn't available into after Datatype.*)

subsection\<open>Iteration of the function \<^term>\<open>F\<close>\<close>

consts  iterates :: "[i\<Rightarrow>i,i,i] \<Rightarrow> i"  (\<open>(\<open>notation=\<open>mixfix iterates\<close>\<close>_^_ '(_'))\<close> [60,1000,1000] 60)

primrec
    "F^0 (x) = x"
    "F^(succ(n)) (x) = F(F^n (x))"

definition
  iterates_omega :: "[i\<Rightarrow>i,i] \<Rightarrow> i" (\<open>(\<open>notation=\<open>mixfix iterates_omega\<close>\<close>_^\<omega> '(_'))\<close> [60,1000] 60) where
    "F^\<omega> (x) \<equiv> \<Union>n\<in>nat. F^n (x)"

lemma iterates_triv:
     "\<lbrakk>n\<in>nat;  F(x) = x\<rbrakk> \<Longrightarrow> F^n (x) = x"
by (induct n rule: nat_induct, simp_all)

lemma iterates_type [TC]:
     "\<lbrakk>n \<in> nat;  a \<in> A; \<And>x. x \<in> A \<Longrightarrow> F(x) \<in> A\<rbrakk>
      \<Longrightarrow> F^n (a) \<in> A"
by (induct n rule: nat_induct, simp_all)

lemma iterates_omega_triv:
    "F(x) = x \<Longrightarrow> F^\<omega> (x) = x"
by (simp add: iterates_omega_def iterates_triv)

lemma Ord_iterates [simp]:
     "\<lbrakk>n\<in>nat;  \<And>i. Ord(i) \<Longrightarrow> Ord(F(i));  Ord(x)\<rbrakk>
      \<Longrightarrow> Ord(F^n (x))"
by (induct n rule: nat_induct, simp_all)

lemma iterates_commute: "n \<in> nat \<Longrightarrow> F(F^n (x)) = F^n (F(x))"
by (induct_tac n, simp_all)


subsection\<open>Transfinite Recursion\<close>

text\<open>Transfinite recursion for definitions based on the
    three cases of ordinals\<close>

definition
  transrec3 :: "[i, i, [i,i]\<Rightarrow>i, [i,i]\<Rightarrow>i] \<Rightarrow>i" where
    "transrec3(k, a, b, c) \<equiv>
       transrec(k, \<lambda>x r.
         if x=0 then a
         else if Limit(x) then c(x, \<lambda>y\<in>x. r`y)
         else b(Arith.pred(x), r ` Arith.pred(x)))"

lemma transrec3_0 [simp]: "transrec3(0,a,b,c) = a"
by (rule transrec3_def [THEN def_transrec, THEN trans], simp)

lemma transrec3_succ [simp]:
     "transrec3(succ(i),a,b,c) = b(i, transrec3(i,a,b,c))"
by (rule transrec3_def [THEN def_transrec, THEN trans], simp)

lemma transrec3_Limit:
     "Limit(i) \<Longrightarrow>
      transrec3(i,a,b,c) = c(i, \<lambda>j\<in>i. transrec3(j,a,b,c))"
by (rule transrec3_def [THEN def_transrec, THEN trans], force)


declaration \<open>fn _ =>
  Simplifier.map_simpset
    (Simplifier.set_mksimps (fn ctxt => map mk_eq o Ord_atomize o Variable.gen_all ctxt))
\<close>

end
