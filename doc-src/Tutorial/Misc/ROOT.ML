context Main.thy;
use "arith1.ML";
by(Auto_tac);
use "arith2.ML";
by(arith_tac 1);
use "arith3.ML";
by(arith_tac 1);

use_thy "Tree";

context Main.thy;
use"exhaust.ML";
use"autotac.ML";
result();

use_thy"NatSum";
result();

use_thy"Types";
use_thy"Defs";
use_thy"ConstDefs";

context Main.thy;
Goal "! xs. if xs = [] then rev xs = [] else rev xs ~= []";
use"splitif.ML";

Goal "(case xs of [] => zs | y#ys => y#(ys@zs)) = xs@zs";
use"splitlist.ML";

use_thy "Itrev";
use "itrev1.ML";
use "itrev2.ML";
use "itrev3.ML";
use "induct_auto.ML";
result();
