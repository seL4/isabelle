
structure FOL =
struct
  val thy = the_context ();
  val classical = classical;
end;

AddXEs [disjI1, disjI2];

open FOL;
