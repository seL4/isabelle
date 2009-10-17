(*  Title:      ZF/Constructible/MetaExists.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header{*The meta-existential quantifier*}

theory MetaExists imports Main begin

text{*Allows quantification over any term having sort @{text logic}.  Used to
quantify over classes.  Yields a proposition rather than a FOL formula.*}

definition
  ex :: "(('a::{}) => prop) => prop"  (binder "?? " 0) where
  "ex(P) == (!!Q. (!!x. PROP P(x) ==> PROP Q) ==> PROP Q)"

notation (xsymbols)
  ex  (binder "\<Or>" 0)

lemma meta_exI: "PROP P(x) ==> (?? x. PROP P(x))"
proof (unfold ex_def)
  assume P: "PROP P(x)"
  fix Q
  assume PQ: "\<And>x. PROP P(x) \<Longrightarrow> PROP Q"
  from P show "PROP Q" by (rule PQ)
qed 

lemma meta_exE: "[| ?? x. PROP P(x);  !!x. PROP P(x) ==> PROP R |] ==> PROP R"
proof (unfold ex_def)
  assume QPQ: "\<And>Q. (\<And>x. PROP P(x) \<Longrightarrow> PROP Q) \<Longrightarrow> PROP Q"
  assume PR: "\<And>x. PROP P(x) \<Longrightarrow> PROP R"
  from PR show "PROP R" by (rule QPQ)
qed

end
