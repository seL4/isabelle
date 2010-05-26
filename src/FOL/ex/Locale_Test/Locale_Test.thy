(*  Title:      FOL/ex/Locale_Test/Locale_Test.thy
    Author:     Clemens Ballarin

Test environment for the locale implementation.
*)

theory Locale_Test
imports Locale_Test1 Locale_Test2 Locale_Test3
begin

text {* Result of theory merge with distinct but identical interpretations *}

context mixin_thy_merge
begin
lemmas less_mixin_thy_merge1 = le.less_def
lemmas less_mixin_thy_merge2 = le'.less_def
end

lemma "gless(x, y) <-> gle(x, y) & x ~= y" (* mixin from first interpretation applied *)
  by (rule le1.less_mixin_thy_merge1)
lemma "gless'(x, y) <-> gle'(x, y) & x ~= y" (* mixin from second interpretation applied *)
  by (rule le1.less_mixin_thy_merge2)

end
