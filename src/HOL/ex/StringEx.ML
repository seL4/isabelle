
Goal "hd(''ABCD'') = CHR ''A''";
by (Simp_tac 1);
qed "";

Goal "hd(''ABCD'') ~= CHR ''B''";
by (Simp_tac 1);
qed "";

Goal "''ABCD'' ~= ''ABCX''";
by (Simp_tac 1);
qed "";

Goal "''ABCD'' = ''ABCD''";
by (Simp_tac 1);
qed "";

Goal "''ABCDEFGHIJKLMNOPQRSTUVWXYZ'' ~= ''ABCDEFGHIJKLMNOPQRSTUVWXY''";
by (Simp_tac 1);
qed "";
