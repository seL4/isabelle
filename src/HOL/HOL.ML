structure HOL =
struct
  val thy = the_context ();
  val plusI = plusI;
  val minusI = minusI;
  val timesI = timesI;
  val powerI = powerI;
  val eq_reflection = eq_reflection;
  val refl = refl;
  val subst = subst;
  val ext = ext;
  val selectI = selectI;
  val impI = impI;
  val mp = mp;
  val True_def = True_def;
  val All_def = All_def;
  val Ex_def = Ex_def;
  val False_def = False_def;
  val not_def = not_def;
  val and_def = and_def;
  val or_def = or_def;
  val Ex1_def = Ex1_def;
  val iff = iff;
  val True_or_False = True_or_False;
  val Let_def = Let_def;
  val if_def = if_def;
  val arbitrary_def = arbitrary_def;
end;

AddXIs [disjI1, disjI2];

open HOL;
