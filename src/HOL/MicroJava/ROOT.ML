
goals_limit:=1;

Unify.search_bound := 40;
Unify.trace_bound  := 40;

with_path "J" (with_path "JVM" (with_path "BV" use_thy)) "JTypeSafe";
with_path "J" (with_path "JVM" (with_path "BV" use_thy)) "BVSpecTypeSafe";
