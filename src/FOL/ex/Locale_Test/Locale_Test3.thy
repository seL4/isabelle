(*  Title:      FOL/ex/Locale_Test/Locale_Test3.thy
    Author:     Clemens Ballarin

Test environment for the locale implementation.
*)

theory Locale_Test3
imports Locale_Test1
begin

interpretation le2: mixin_thy_merge \<open>gle\<close> \<open>gle'\<close>
  rewrites \<open>reflexive.less(gle', x, y) \<longleftrightarrow> gless'(x, y)\<close>
proof -
  show \<open>mixin_thy_merge(gle, gle')\<close> by unfold_locales
  note reflexive = this[unfolded mixin_thy_merge_def, THEN conjunct2]
  show \<open>reflexive.less(gle', x, y) \<longleftrightarrow> gless'(x, y)\<close>
    by (simp add: reflexive.less_def[OF reflexive] gless'_def)
qed

end
