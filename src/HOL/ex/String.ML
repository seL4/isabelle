val string_ss = list_ss addsimps (String.nibble.simps @ String.char.simps);

goal String.thy "hd(''ABCD'') = CHR ''A''";
by(simp_tac string_ss 1);
result();

goal String.thy "hd(''ABCD'') ~= CHR ''B''";
by(simp_tac string_ss 1);
result();

goal String.thy "''ABCD'' ~= ''ABCX''";
by(simp_tac string_ss 1);
result();

goal String.thy "''ABCD'' = ''ABCD''";
by(simp_tac string_ss 1);
result();

goal String.thy
  "''ABCDEFGHIJKLMNOPQRSTUVWXYZ'' ~= ''ABCDEFGHIJKLMNOPQRSTUVWXY''";
by(simp_tac string_ss 1);
result();
