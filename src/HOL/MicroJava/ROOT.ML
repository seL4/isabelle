
goals_limit := 1;

Unify.search_bound := 40;
Unify.trace_bound  := 40;

with_paths ["J"             ] use_thy "JTypeSafe";
with_paths ["J"             ] use_thy "Example";
with_paths ["J", "JVM", "BV"] use_thy "BVSpecTypeSafe";
with_paths ["J", "JVM", "BV"] use_thy "LBVCorrect";
with_paths ["J", "JVM", "BV"] use_thy "LBVComplete";
