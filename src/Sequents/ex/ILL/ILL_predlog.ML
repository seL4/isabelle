
open ILL_predlog;


fun auto1 x = prove_goal thy x
 (fn prems => [best_tac safe_cs 1]) ;

fun auto2 x = prove_goal thy x
 (fn prems => [best_tac power_cs 1]) ;
