
structure FOL =
struct
  val thy = the_context ();
  val classical = classical;
end;

AddXIs [equal_intr_rule, disjI1, disjI2];

open FOL;
