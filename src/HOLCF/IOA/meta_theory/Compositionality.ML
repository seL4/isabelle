(*  Title:      HOLCF/IOA/meta_theory/Compositionality.ML
    ID:        
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Compositionality of I/O automata
*) 


goal thy "!! A1 A2 B1 B2. \
\         [| is_asig (asig_of A1); is_asig (asig_of A2); \
\            is_asig (asig_of B1); is_asig (asig_of B2); \
\            compat_ioas A1 B1; compat_ioas B1 A1; compat_ioas A2 B2; compat_ioas B2 A2; \
\            A1 =<| A2; \
\            B1 =<| B2 |] \
\        ==> (A1 || B1) =<| (A2 || B2)";
by (asm_full_simp_tac (!simpset addsimps [ioa_implements_def,
                               inputs_of_par,outputs_of_par]) 1);


by (safe_tac set_cs);
by (asm_full_simp_tac (!simpset addsimps [compotraces]) 1);

