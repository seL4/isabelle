
goals_limit := 1;

Unify.search_bound := 40;
Unify.trace_bound  := 40;

add_path "J";
add_path "JVM";
add_path "BV";

use_thy "JTypeSafe";
use_thy "Example";
use_thy "BVSpecTypeSafe";
use_thy "LBVCorrect";
use_thy "LBVComplete";
use_thy "JVM";
