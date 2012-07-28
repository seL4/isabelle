theory Ex imports Pure
begin

ML {*
  val rc = Isabelle_System.bash
    "cd \"$ISABELLE_HOME/src/HOL/Library\"; \"$ISABELLE_TOOL\" mirabelle -q arith Inner_Product.thy";
  if rc <> 0 then error ("Mirabelle example failed: " ^ string_of_int rc)
  else ();
*} -- "some arbitrary small test case"

end

