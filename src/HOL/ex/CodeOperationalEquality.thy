(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Operational equality for code generation *}

theory CodeOperationalEquality
imports Main
begin

section {* Operational equality for code generation *}

subsection {* eq class *}

class eq =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

defs
  eq_def: "eq x y == (x = y)"

ML {*
local
  val thy = the_context ();
  val const_eq = Sign.intern_const thy "eq";
  val type_bool = Type (Sign.intern_type thy "bool", []);
in
  val eq_def_sym = Thm.symmetric (thm "eq_def");
  val class_eq = Sign.intern_class thy "eq";
end
*}


subsection {* preprocessor *}

ML {*
fun constrain_op_eq thy thms =
  let
    fun add_eq (Const ("op =", ty)) =
          fold (insert (eq_fst (op = : indexname * indexname -> bool)))
            (Term.add_tvarsT ty [])
      | add_eq _ =
          I
    val eqs = fold (fold_aterms add_eq o Thm.prop_of) thms [];
    val instT = map (fn (v_i, sort) =>
      (Thm.ctyp_of thy (TVar (v_i, sort)),
         Thm.ctyp_of thy (TVar (v_i, Sorts.inter_sort (Sign.classes_of thy) (sort, [class_eq]))))) eqs;
  in
    thms
    |> map (Thm.instantiate (instT, []))
  end;
*}


subsection {* codetypes hook *}

setup {*
let
  fun add_eq_instance specs =
    DatatypeCodegen.prove_codetypes_arities
      (K (ClassPackage.intro_classes_tac []))
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [class_eq] ((K o K o K) []);
  (* fun add_eq_thms dtco thy =
    let
      val thms =
        DatatypeCodegen.get_eq thy dtco
        |> maps ((#mk o #mk_rews o snd o MetaSimplifier.rep_ss o Simplifier.simpset_of) thy)
        |> constrain_op_eq thy
        |> map (Tactic.rewrite_rule [eq_def_sym])
    in fold CodegenTheorems.add_fun thms thy end; *)
  fun hook dtcos =
    add_eq_instance dtcos (* #> fold add_eq_thms dtcos *);
in
  DatatypeCodegen.add_codetypes_hook_bootstrap hook
end
*}


subsection {* extractor *}

setup {*
let
  val lift_not_thm = thm "HOL.Eq_FalseI";
  val lift_thm = thm "HOL.eq_reflection";
  val eq_def_thm = Thm.symmetric (thm "eq_def");
  fun get_eq_thms thy tyco = case DatatypePackage.get_datatype thy tyco
   of SOME _ => DatatypeCodegen.get_eq thy tyco
    | NONE => case TypedefCodegen.get_triv_typedef thy tyco
       of SOME (_ ,(_, thm)) => [thm]
        | NONE => [];
  fun get_eq_thms_eq thy ("CodeOperationalEquality.eq", ty) = (case strip_type ty
       of (Type (tyco, _) :: _, _) =>
             get_eq_thms thy tyco
             |> map (perhaps (try (fn thm => lift_not_thm OF [thm])))
             |> map (perhaps (try (fn thm => lift_thm OF [thm])))
             (*|> tap (writeln o cat_lines o map string_of_thm)*)
             |> constrain_op_eq thy
             (*|> tap (writeln o cat_lines o map string_of_thm)*)
             |> map (Tactic.rewrite_rule [eq_def_thm])
             (*|> tap (writeln o cat_lines o map string_of_thm)*)
        | _ => [])
    | get_eq_thms_eq _ _ = [];
in
  CodegenTheorems.add_fun_extr get_eq_thms_eq
end
*}


subsection {* integers *}

definition
  "eq_integer (k\<Colon>int) l = (k = l)"

instance int :: eq ..

lemma [code fun]:
  "eq k l = eq_integer k l"
unfolding eq_integer_def eq_def ..

code_const eq_integer
  (SML infixl 6 "=")
  (Haskell infixl 4 "==")


subsection {* codegenerator setup *}

setup {*
  CodegenTheorems.add_preproc constrain_op_eq
*}

declare eq_def [symmetric, code inline]


subsection {* haskell setup *}

code_class eq
  (Haskell "Eq" where eq \<equiv> "(==)")

code_instance eq :: bool and eq :: unit and eq :: *
  and eq :: option and eq :: list and eq :: char and eq :: int
  (Haskell - and - and - and - and - and - and -)

code_const "eq \<Colon> bool \<Rightarrow> bool \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq \<Colon> unit \<Rightarrow> unit \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq \<Colon> 'a\<Colon>eq \<times> 'b\<Colon>eq \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq \<Colon> 'a\<Colon>eq option \<Rightarrow> 'a option \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq \<Colon> 'a\<Colon>eq list \<Rightarrow> 'a list \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq \<Colon> char \<Rightarrow> char \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_const "eq"
  (Haskell infixl 4 "==")

end