(*  Title:      FOL/ex/Locale_Test/Locale_Test2.thy
    Author:     Clemens Ballarin, TU Muenchen

Test environment for the locale implementation.
*)

theory Locale_Test2
imports Locale_Test1
begin

interpretation le1: mixin_thy_merge gle gle'
  where "reflexive.less(gle, x, y) <-> gless(x, y)"
proof -
  show "mixin_thy_merge(gle, gle')" by unfold_locales
  note reflexive = this[unfolded mixin_thy_merge_def, THEN conjunct1]
  show "reflexive.less(gle, x, y) <-> gless(x, y)"
    by (simp add: reflexive.less_def[OF reflexive] gless_def)
qed

end
