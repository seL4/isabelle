Goal "hd(''ABCD'') = CHR ''A''";
by (Simp_tac 1);
result();

Goal "hd(''ABCD'') ~= CHR ''B''";
by (Simp_tac 1);
result();

Goal "''ABCD'' ~= ''ABCX''";
by (Simp_tac 1);
result();

Goal "''ABCD'' = ''ABCD''";
by (Simp_tac 1);
result();

Goal
  "''ABCDEFGHIJKLMNOPQRSTUVWXYZ'' ~= ''ABCDEFGHIJKLMNOPQRSTUVWXY''";
by (Simp_tac 1);
result();
