
structure FOL =
struct
  val thy = the_context ();
  val classical = classical;
end;

AddXIs [disjI1, disjI2];

open FOL;
