
structure IFOL =
struct
  val thy = the_context ();
  val refl = refl;
  val subst = subst;
  val conjI = conjI;
  val conjunct1 = conjunct1;
  val conjunct2 = conjunct2;
  val disjI1 = disjI1;
  val disjI2 = disjI2;
  val disjE = disjE;
  val impI = impI;
  val mp = mp;
  val FalseE = FalseE;
  val True_def = True_def;
  val not_def = not_def;
  val iff_def = iff_def;
  val ex1_def = ex1_def;
  val allI = allI;
  val spec = spec;
  val exI = exI;
  val exE = exE;
  val eq_reflection = eq_reflection;
  val iff_reflection = iff_reflection;
end;

open IFOL;
