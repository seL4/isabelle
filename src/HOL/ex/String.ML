goal String.thy "hd(''ABCD'') = CHR ''A''";
by (Simp_tac 1);
result();

goal String.thy "hd(''ABCD'') ~= CHR ''B''";
by (Simp_tac 1);
result();

goal String.thy "''ABCD'' ~= ''ABCX''";
by (Simp_tac 1);
result();

goal String.thy "''ABCD'' = ''ABCD''";
by (Simp_tac 1);
result();

goal String.thy
  "''ABCDEFGHIJKLMNOPQRSTUVWXYZ'' ~= ''ABCDEFGHIJKLMNOPQRSTUVWXY''";
by (Simp_tac 1);
result();
