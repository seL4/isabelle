theory Separation = HoareAbort:

types heap = "(nat \<Rightarrow> nat option)"


text{* The semantic definition of a few connectives: *}

constdefs
 R:: "heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool"
"R h h1 h2 == dom h1 \<inter> dom h2 = {} \<and> h = h1 ++ h2"

 star:: "(heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool) \<Rightarrow> (heap \<Rightarrow> bool)"
"star P Q == \<lambda>h. \<exists>h1 h2. R h h1 h2 \<and> P h1 \<and> Q h2"

 singl:: "heap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
"singl h x y == dom h = {x} & h x = Some y"

lemma "VARS x y z w h
 {star (%h. singl h x y) (%h. singl h z w) h}
 SKIP
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def R_def singl_def)
done

text{* To suppress the heap parameter of the connectives, we assume it
is always called H and add/remove it upon parsing/printing. Thus
every pointer program needs to have a program variable H, and
assertions should not contain any locally bound Hs - otherwise they
may bind the implicit H. *}

text{* Nice input syntax: *}

syntax
 "@singl" :: "nat \<Rightarrow> nat \<Rightarrow> bool" ("[_ \<mapsto> _]")
 "@star" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "**" 60)

ML{*
fun singl_tr [p,q] = Syntax.const "singl" $ Syntax.free "H" $ p $ q
  | singl_tr ts = raise TERM ("singl_tr", ts);
fun star_tr [P,Q] = Syntax.const "star" $
      absfree("H",dummyT,P) $ absfree("H",dummyT,Q) $ Syntax.free "H"
  | star_tr ts = raise TERM ("star_tr", ts);
*}

parse_translation {* [("@singl", singl_tr),("@star", star_tr)] *}

lemma "VARS H x y z w
 {[x\<mapsto>y] ** [z\<mapsto>w]}
 SKIP
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def R_def singl_def)
done

text{* Nice output syntax: *}

ML{*
fun singl_tr' [_,p,q] = Syntax.const "@singl" $ p $ q
fun star_tr' [Abs(_,_,P),Abs(_,_,Q),_] = Syntax.const "@star" $ P $ Q
*}

print_translation {* [("singl", singl_tr'),("star", star_tr')] *}

lemma "VARS H x y z w
 {[x\<mapsto>y] ** [z\<mapsto>w]}
 y := w
 {x \<noteq> z}"
apply vcg
apply(auto simp:star_def R_def singl_def)
done


consts llist :: "(heap * nat)set"
inductive llist
intros
empty: "(%n. None, 0) : llist"
cons: "\<lbrakk> R h h1 h2; pto h1 p q; (h2,q):llist \<rbrakk> \<Longrightarrow> (h,p):llist"

lemma "VARS p q h
 {(h,p) : llist}
 h := h(q \<mapsto> p)
 {(h,q) : llist}"
apply vcg
apply(rule_tac "h1.0" = "%n. if n=q then Some p else None" in llist.cons)
prefer 3 apply assumption
prefer 2 apply(simp add:singl_def dom_def)
apply(simp add:R_def dom_def)


