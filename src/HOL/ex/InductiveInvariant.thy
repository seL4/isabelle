theory InductiveInvariant = Main:

(** Authors: Sava Krsti\'{c} and John Matthews **)
(**    Date: Sep 12, 2003                      **)

text {* A formalization of some of the results in
        \emph{Inductive Invariants for Nested Recursion},
        by Sava Krsti\'{c} and John Matthews.
        Appears in the proceedings of TPHOLs 2003, LNCS vol. 2758, pp. 253-269. *}


text "S is an inductive invariant of the functional F with respect to the wellfounded relation r."

constdefs indinv :: "('a * 'a) set => ('a => 'b => bool) => (('a => 'b) => ('a => 'b)) => bool"
         "indinv r S F == \<forall>f x. (\<forall>y. (y,x) : r --> S y (f y)) --> S x (F f x)"


text "S is an inductive invariant of the functional F on set D with respect to the wellfounded relation r."

constdefs indinv_on :: "('a * 'a) set => 'a set => ('a => 'b => bool) => (('a => 'b) => ('a => 'b)) => bool"
         "indinv_on r D S F == \<forall>f. \<forall>x\<in>D. (\<forall>y\<in>D. (y,x) \<in> r --> S y (f y)) --> S x (F f x)"


text "The key theorem, corresponding to theorem 1 of the paper. All other results
      in this theory are proved using instances of this theorem, and theorems
      derived from this theorem."

theorem indinv_wfrec:
  assumes WF:  "wf r" and
          INV: "indinv r S F"
  shows        "S x (wfrec r F x)"
proof (induct_tac x rule: wf_induct [OF WF])
  fix x
  assume  IHYP: "\<forall>y. (y,x) \<in> r --> S y (wfrec r F y)"
  then have     "\<forall>y. (y,x) \<in> r --> S y (cut (wfrec r F) r x y)" by (simp add: tfl_cut_apply)
  with INV have "S x (F (cut (wfrec r F) r x) x)" by (unfold indinv_def, blast)
  thus "S x (wfrec r F x)" using WF by (simp add: wfrec)
qed

theorem indinv_on_wfrec:
  assumes WF:  "wf r" and
          INV: "indinv_on r D S F" and
          D:   "x\<in>D"
  shows        "S x (wfrec r F x)"
apply (insert INV D indinv_wfrec [OF WF, of "% x y. x\<in>D --> S x y"])
by (simp add: indinv_on_def indinv_def)

theorem ind_fixpoint_on_lemma:
  assumes WF:  "wf r" and
         INV: "\<forall>f. \<forall>x\<in>D. (\<forall>y\<in>D. (y,x) \<in> r --> S y (wfrec r F y) & f y = wfrec r F y)
                               --> S x (wfrec r F x) & F f x = wfrec r F x" and
           D: "x\<in>D"
  shows "F (wfrec r F) x = wfrec r F x & S x (wfrec r F x)"
proof (rule indinv_on_wfrec [OF WF _ D, of "% a b. F (wfrec r F) a = b & wfrec r F a = b & S a b" F, simplified])
  show "indinv_on r D (%a b. F (wfrec r F) a = b & wfrec r F a = b & S a b) F"
  proof (unfold indinv_on_def, clarify)
    fix f x
    assume A1: "\<forall>y\<in>D. (y, x) \<in> r --> F (wfrec r F) y = f y & wfrec r F y = f y & S y (f y)"
    assume D': "x\<in>D"
    from A1 INV [THEN spec, of f, THEN bspec, OF D']
      have "S x (wfrec r F x)" and
           "F f x = wfrec r F x" by auto
    moreover
    from A1 have "\<forall>y\<in>D. (y, x) \<in> r --> S y (wfrec r F y)" by auto
    with D' INV [THEN spec, of "wfrec r F", simplified]
      have "F (wfrec r F) x = wfrec r F x" by blast
    ultimately show "F (wfrec r F) x = F f x & wfrec r F x = F f x & S x (F f x)" by auto
  qed
qed

theorem ind_fixpoint_lemma:
  assumes WF:  "wf r" and
         INV: "\<forall>f x. (\<forall>y. (y,x) \<in> r --> S y (wfrec r F y) & f y = wfrec r F y)
                         --> S x (wfrec r F x) & F f x = wfrec r F x"
  shows "F (wfrec r F) x = wfrec r F x & S x (wfrec r F x)"
apply (rule ind_fixpoint_on_lemma [OF WF _ UNIV_I, simplified])
by (rule INV)

theorem tfl_indinv_wfrec:
"[| f == wfrec r F; wf r; indinv r S F |]
 ==> S x (f x)"
by (simp add: indinv_wfrec)

theorem tfl_indinv_on_wfrec:
"[| f == wfrec r F; wf r; indinv_on r D S F; x\<in>D |]
 ==> S x (f x)"
by (simp add: indinv_on_wfrec)

end