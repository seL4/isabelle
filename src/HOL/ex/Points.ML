
(*Note: any of these goals may be solved by a single stroke of
  auto(); or force 1;*)


(* some basic simplifications *)

Goal "!!m n p. x (| x = m, y = n, ... = p |) = m";
by (Simp_tac 1);
result();

Goal "!!m n p. (| x = m, y = n, ... = p |) (| x:= 0 |) = (| x = 0, y = n, ... = p |)";
by (Simp_tac 1);
result();


(* splitting quantifiers *)

Goal "!!r m n. r (| x := n |) (| y := m |) = r (| y := m |) (| x := n |)";
by (record_split_tac 1);
by (Simp_tac 1);
result();

Goal "!!r m n. r (| x := n |) (| x := m |) = r (| x := m |)";
by (record_split_tac 1);
by (Simp_tac 1);
result();


(* record equality *)

Goal "!!r. (| x = n, y = p |) = (| x = n', y = p' |) & n = 0 ==> n' = 0";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
result();

Goalw [getX_def, setX_def, incX_def] "!!r n. incX r = setX r (Suc (getX r))";
by (record_split_tac 1);
by (Simp_tac 1);
result();
