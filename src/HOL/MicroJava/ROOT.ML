goals_limit := 1;

add_path "J";
add_path "JVM";
add_path "BV";

use_thy "JTypeSafe";
use_thy "Example";
use_thy "JListExample";
use_thy "JVMListExample";
use_thy "BVSpecTypeSafe";
use_thy "JVM";
use_thy "LBVSpec"; 
(* momentarily broken:
use_thy "LBVCorrect";
use_thy "LBVComplete";
*)
