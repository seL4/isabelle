use_thy "ABexp";
use"abgoalind.ML";
use"autotac.ML";
result();

use_thy "Term";
use"tidproof.ML";
result();
use"appmap.ML";
by(induct_tac "ts" 1);
by(Auto_tac);
qed"subst_App_map";
Addsimps [subst_App_map];
result();

use_thy"Trie";
use"lookupempty.ML";
qed "lookup_empty";
Addsimps [lookup_empty];
use"trieAdds.ML";
use"triemain.ML";
use"trieinduct.ML";
use"trieexhaust.ML";
by(Auto_tac);
result();
