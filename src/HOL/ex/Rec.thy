Rec = Fixedpt +
consts
fix	:: ('a=>'a) => 'a
Dom	:: (('a=>'b) => ('a=>'b)) => 'a set
Domf	:: (('a=>'b) => ('a=>'b)) => 'a set => 'a set
rules
Domf_def "Domf(F,D) == {y . !f g. (!x:D. f(x)=g(x)) --> F(f,y)=F(g,y)}"
Dom_def  "Dom(F) == lfp(Domf(F))"
end
