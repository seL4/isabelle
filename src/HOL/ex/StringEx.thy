
header {* String examples *}

theory StringEx = Main:

lemma "hd ''ABCD'' = CHR ''A''"
  by simp

lemma "hd ''ABCD'' \<noteq> CHR ''B''"
  by simp

lemma "''ABCD'' \<noteq> ''ABCX''"
  by simp

lemma "''ABCD'' = ''ABCD''"
  by simp

lemma "''ABCDEFGHIJKLMNOPQRSTUVWXYZ'' \<noteq> ''ABCDEFGHIJKLMNOPQRSTUVWXY''"
  by simp

lemma "set ''Foobar'' = {CHR ''F'', CHR ''a'', CHR ''b'', CHR ''o'', CHR ''r''}"
  by (simp add: insert_commute)

lemma "set ''Foobar'' = ?X"
  by (simp add: insert_commute)

end
