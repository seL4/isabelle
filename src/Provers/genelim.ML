(** Generalized elimination rules **)

(*Generalized elimination for two conclusions*)
val prems = goal pure_thy 
     "[| PROP U ==> PROP VA;  \
\        PROP U ==> PROP VB;  \
\        PROP U;              \
\        [| PROP VA; PROP VB |] ==> PROP W    \
\     |] ==> PROP W";
by (REPEAT (resolve_tac prems 1));
val general_elim2_rl = result();

fun make_elim2 (rl1,rl2) = standard (rl2 COMP rl1 COMP general_elim2_rl);
fun elim2_tac (rl1,rl2) = eresolve_tac [rl2 COMP rl1 COMP general_elim2_rl];


(*For example,  make_elim2(conjunct1,conjunct2)  
  yields conjunction elimination *)
