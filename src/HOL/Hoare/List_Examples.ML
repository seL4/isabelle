goal thy
"{x=X} \
\ y := []; \
\ WHILE x ~= [] \
\ DO { rev(x)@y = rev(X)} \
\    y := hd x # y; x := tl x \
\ END \
\{y=rev(X)}";
by (hoare_tac 1);
by (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "imperative_reverse";

goal thy
"{x=X & y = Y} \
\ x := rev(x); \
\ WHILE x ~= [] \
\ DO { rev(x)@y = X@Y} \
\    y := hd x # y; x := tl x \
\ END \
\{y = X@Y}";
by (hoare_tac 1);
by (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "imperative_append";
