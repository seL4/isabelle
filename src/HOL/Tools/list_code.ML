(*  Title:  HOL/Tools/list_code.ML
    Author: Florian Haftmann, TU Muenchen

Code generation for list literals.
*)

signature LIST_CODE =
sig
  val implode_list: string -> string -> Code_Thingol.iterm -> Code_Thingol.iterm list option
  val default_list: int * string
    -> (Code_Printer.fixity -> Code_Thingol.iterm -> Pretty.T)
    -> Code_Printer.fixity -> Code_Thingol.iterm -> Code_Thingol.iterm -> Pretty.T
  val add_literal_list: string -> theory -> theory
end;

structure List_Code : LIST_CODE =
struct

open Basic_Code_Thingol;

fun implode_list nil' cons' t =
  let
    fun dest_cons (IConst { name = c, ... } `$ t1 `$ t2) =
          if c = cons'
          then SOME (t1, t2)
          else NONE
      | dest_cons _ = NONE;
    val (ts, t') = Code_Thingol.unfoldr dest_cons t;
  in case t'
   of IConst { name = c, ... } => if c = nil' then SOME ts else NONE
    | _ => NONE
  end;

fun default_list (target_fxy, target_cons) pr fxy t1 t2 =
  Code_Printer.brackify_infix (target_fxy, Code_Printer.R) fxy (
    pr (Code_Printer.INFX (target_fxy, Code_Printer.X)) t1,
    Code_Printer.str target_cons,
    pr (Code_Printer.INFX (target_fxy, Code_Printer.R)) t2
  );

fun add_literal_list target =
  let
    fun pretty literals [nil', cons'] pr thm vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list nil' cons' t2)
       of SOME ts =>
            Code_Printer.literal_list literals (map (pr vars Code_Printer.NOBR) ts)
        | NONE =>
            default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in Code_Target.add_const_syntax target @{const_name Cons}
    (SOME (Code_Printer.complex_const_syntax (2, ([@{const_name Nil}, @{const_name Cons}], pretty))))
  end

end;
