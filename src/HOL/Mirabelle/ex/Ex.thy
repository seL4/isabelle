theory Ex imports Pure
begin

ML \<open>
  val rc = Isabelle_System.bash
    "cd \"$ISABELLE_HOME/src/HOL/Analysis\"; if isabelle build -n \"$MIRABELLE_LOGIC\"; then isabelle mirabelle arith Inner_Product.thy; fi";
  if rc <> 0 then error ("Mirabelle example failed: " ^ string_of_int rc)
  else ();
\<close> \<comment> \<open>some arbitrary small test case\<close>

end

