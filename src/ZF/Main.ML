
structure Main =
struct
  val thy = the_context ();
end;

simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o forall_elim_vars_safe);
