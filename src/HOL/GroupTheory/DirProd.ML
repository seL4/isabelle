(*  Title:      HOL/GroupTheory/DirProd
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Direct product of two groups
*)

Open_locale "prodgroup";

val e'_def = thm "e'_def";
val binop'_def = thm "binop'_def";
val inv'_def = thm "inv'_def";
val P_def = thm "P_def";
val Group_G' = thm "Group_G'";


Addsimps [P_def, Group_G', Group_G];

Goal "(P.<cr>) = ((G.<cr>) \\<times> (G'.<cr>))";
by (afs [ProdGroup_def] 1);
qed "P_carrier";

Goal "(P.<f>) = \
\     (%(x, x'): (P.<cr>). %(y, y'): (P.<cr>). ( x ## y, x' ##' y'))";
by (afs [ProdGroup_def, binop_def, binop'_def] 1);
qed "P_bin_op";

Goal "(P.<inv>) = (%(x, y): (P.<cr>). (i x, i' y))";
by (afs [ProdGroup_def, inv_def, inv'_def] 1);
qed "P_inverse";

Goal "(P.<e>) = (G.<e>, G'.<e>)";
by (afs [ProdGroup_def, e_def, e'_def] 1);
qed "P_unit";

Goal "P = (| carrier = P.<cr>, \
\       bin_op = (%(x, x'): (P.<cr>). %(y, y'): (P.<cr>).\
\                  (x ## y, x' ##' y')), \
\       inverse = (%(x, y): (P.<cr>). (i x, i' y)), \
\       unit = P.<e> |)";
by (afs [ProdGroup_def, P_carrier, P_bin_op, P_inverse, P_unit] 1);
by (afs [binop_def, binop'_def, inv_def, inv'_def] 1);
qed "P_defI";
val P_DefI = export P_defI;

Delsimps [P_def];

Goal "(P.<f>) : (P.<cr>) \\<rightarrow> (P.<cr>) \\<rightarrow> (P.<cr>)";
by (auto_tac (claset() addSIs [restrictI], 
              simpset() addsimps  [P_bin_op, P_carrier, binop'_def, 
                                   bin_op_closed])); 
qed "bin_op_prod_closed";

Goal "(P.<inv>) : (P.<cr>) \\<rightarrow> (P.<cr>)";
by (auto_tac (claset() addSIs [restrictI], 
              simpset() addsimps  [P_inverse, P_carrier, inv_closed, 
                    inv'_def, inverse_closed])); 
qed "inverse_prod_closed";

(* MAIN PROOF *)
Goal "P : Group";
by (stac P_defI 1);
by (rtac GroupI 1);
by (auto_tac (claset(), 
       simpset() addsimps ([P_carrier,P_bin_op,P_inverse,P_unit] RL [sym]))); 
(* 1.  *)
by (rtac bin_op_prod_closed 1);
(* 2. *)
by (rtac inverse_prod_closed 1);
(* 3. *)
by (afs [P_carrier, P_unit, export e_closed] 1);
(* 4. *)
by (afs [P_carrier, P_bin_op, P_inverse, P_unit, Group_G' RS inverse_closed,
         inv'_def, e_def, binop'_def, Group_G' RS (export inv_ax2)] 1);
(* 5 *)
by (afs [P_carrier,P_bin_op,P_unit, Group_G' RS unit_closed, export e_ax1,
         binop_def, binop'_def] 1);
(* 6 *)
by (afs [P_carrier,P_bin_op, Group_G' RS bin_op_closed, 
         binop'_def, binop_assoc,export binop_assoc] 1);
qed "prodgroup_is_group";
val ProdGroup_is_Group = export prodgroup_is_group;

Delsimps [P_def, Group_G', Group_G];

Close_locale "prodgroup";
Close_locale "r_group";
Close_locale "group";

Goal "ProdGroup : Group \\<rightarrow> Group \\<rightarrow> Group";
by (REPEAT (ares_tac [funcsetI, ProdGroup_is_Group] 1));
by (auto_tac (claset(), simpset() addsimps [ProdGroup_def])); 
qed "ProdGroup_arity";
