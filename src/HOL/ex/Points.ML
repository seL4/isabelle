
(** some basic simplifiactions **)

Goal "!!m n p. x (| x = m, y = n, ... = p |) = m";
by (Simp_tac 1);

Goal "!!m n p. (| x = m, y = n, ... = p |) (| x:= 0 |) = (| x = 0, y = n, ... = p |)";
by (Simp_tac 1);



(** splitting **)

Goal "!!r m n. r (| x := n |) (| y := m |) = r (| y := m |) (| x := n |)";
by (record_split_tac 1);
by (Simp_tac 1);

Goal "!!r m n. r (| x := n |) (| x := m |) = r (| x := m |)";
by (record_split_tac 1);
by (Simp_tac 1);



(** Equality **)

Goal "!!r. (| x = n, y = p |) = (| x = n', y = p' |) & n = 0 ==> n' = 0";
by (Asm_full_simp_tac 1);
by (Fast_tac 1);

Goalw [getX_def, setX_def, incX_def] "!!r n. incX r = setX r (Suc (getX r))";
by (record_split_tac 1);
by (Simp_tac 1);