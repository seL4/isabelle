(*  Title:      ZF/Constructible/MetaExists.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header{*The meta-existential quantifier*}

theory MetaExists = Main:

text{*Allows quantification over any term having sort @{text logic}.  Used to
quantify over classes.  Yields a proposition rather than a FOL formula.*}

constdefs
  ex :: "(('a::logic) => prop) => prop"            (binder "?? " 0)
  "ex(P) == (!!Q. (!!x. PROP P(x) ==> PROP Q) ==> PROP Q)"

syntax (xsymbols)
  "?? "        :: "[idts, o] => o"             ("(3\<Or>_./ _)" [0, 0] 0)

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
