
structure FOL =
struct
  val thy = the_context ();
  val classical = classical;
end;

open FOL;
