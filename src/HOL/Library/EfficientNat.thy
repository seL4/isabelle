(*  Title:      HOL/Library/EfficientNat.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of natural numbers by integers *}

theory EfficientNat
imports Main
begin

text {*
When generating code for functions on natural numbers, the canonical
representation using @{term "0::nat"} and @{term "Suc"} is unsuitable for
computations involving large numbers. The efficiency of the generated
code can be improved drastically by implementing natural numbers by
integers. To do this, just include this theory.
*}

subsection {* Logical rewrites *}

text {*
  A int-to-nat conversion with domain
  restricted to non-negative ints (in contrast to @{const nat}).
*}

definition
  nat_of_int :: "int \<Rightarrow> nat" where
  "k \<ge> 0 \<Longrightarrow> nat_of_int k = nat k"

lemma nat_of_int_int:
  "nat_of_int (int n) = n"
  using zero_zle_int nat_of_int_def by simp

text {*
  Case analysis on natural numbers is rephrased using a conditional
  expression:
*}

lemma [code unfold, code noinline]: "nat_case \<equiv> (\<lambda>f g n. if n = 0 then f else g (n - 1))"
proof -
  have rewrite: "\<And>f g n. nat_case f g n = (if n = 0 then f else g (n - 1))"
  proof -
    fix f g n
    show "nat_case f g n = (if n = 0 then f else g (n - 1))"
      by (cases n) simp_all
  qed
  show "nat_case \<equiv> (\<lambda>f g n. if n = 0 then f else g (n - 1))"
    by (rule eq_reflection ext rewrite)+ 
qed

lemma [code inline]:
  "nat_case f g n = (if n = 0 then f else g (nat_of_int (int n - 1)))"
  by (cases n) (simp_all add: nat_of_int_int)

text {*
  Most standard arithmetic functions on natural numbers are implemented
  using their counterparts on the integers:
*}

lemma [code func]: "0 = nat_of_int 0"
  by (simp add: nat_of_int_def)
lemma [code func, code inline]:  "1 = nat_of_int 1"
  by (simp add: nat_of_int_def)
lemma [code func]: "Suc n = n + 1"
  by simp
lemma [code]: "m + n = nat (int m + int n)"
  by arith
lemma [code func, code inline]: "m + n = nat_of_int (int m + int n)"
  by (simp add: nat_of_int_def)
lemma [code, code inline]: "m - n = nat (int m - int n)"
  by arith
lemma [code]: "m * n = nat (int m * int n)"
  unfolding zmult_int by simp
lemma [code func, code inline]: "m * n = nat_of_int (int m * int n)"
proof -
  have "int (m * n) = int m * int n"
    by (induct m) (simp_all add: zadd_zmult_distrib)
  then have "m * n = nat (int m * int n)" by auto
  also have "\<dots> = nat_of_int (int m * int n)"
  proof -
    have "int m \<ge> 0" and "int n \<ge> 0" by auto
    have "int m * int n \<ge> 0" by (rule split_mult_pos_le) auto
    with nat_of_int_def show ?thesis by auto
  qed
  finally show ?thesis .
qed  
lemma [code]: "m div n = nat (int m div int n)"
  unfolding zdiv_int [symmetric] by simp
lemma [code func]: "m div n = fst (Divides.divmod m n)"
  unfolding divmod_def by simp
lemma [code]: "m mod n = nat (int m mod int n)"
  unfolding zmod_int [symmetric] by simp
lemma [code func]: "m mod n = snd (Divides.divmod m n)"
  unfolding divmod_def by simp
lemma [code, code inline]: "(m < n) \<longleftrightarrow> (int m < int n)"
  by simp
lemma [code func, code inline]: "(m \<le> n) \<longleftrightarrow> (int m \<le> int n)"
  by simp
lemma [code func, code inline]: "m = n \<longleftrightarrow> int m = int n"
  by simp
lemma [code func]: "nat k = (if k < 0 then 0 else nat_of_int k)"
proof (cases "k < 0")
  case True then show ?thesis by simp
next
  case False then show ?thesis by (simp add: nat_of_int_def)
qed
lemma [code func]:
  "int_aux i n = (if int n = 0 then i else int_aux (i + 1) (nat_of_int (int n - 1)))"
proof -
  have "0 < n \<Longrightarrow> int n = 1 + int (nat_of_int (int n - 1))"
  proof -
    assume prem: "n > 0"
    then have "int n - 1 \<ge> 0" by auto
    then have "nat_of_int (int n - 1) = nat (int n - 1)" by (simp add: nat_of_int_def)
    with prem show "int n = 1 + int (nat_of_int (int n - 1))" by simp
  qed
  then show ?thesis unfolding int_aux_def by simp
qed


subsection {* Code generator setup for basic functions *}

text {*
  @{typ nat} is no longer a datatype but embedded into the integers.
*}

code_const "0::nat"
  (SML "!(0 : IntInf.int)")
  (Haskell "0")

code_const "Suc"
  (SML "IntInf.+ ((_), 1)")
  (Haskell "!((_) + 1)")

setup {*
  CodegenData.del_datatype "nat"
*}

types_code
  nat ("int")
attach (term_of) {*
val term_of_nat = HOLogic.mk_number HOLogic.natT o IntInf.fromInt;
*}
attach (test) {*
fun gen_nat i = random_range 0 i;
*}

code_type nat
  (SML "IntInf.int")
  (Haskell "Integer")

consts_code
  "HOL.zero" :: nat ("0")
  Suc ("(_ + 1)")

text {*
  Since natural numbers are implemented
  using integers, the coercion function @{const "int"} of type
  @{typ "nat \<Rightarrow> int"} is simply implemented by the identity function,
  likewise @{const nat_of_int} of type @{typ "int \<Rightarrow> nat"}.
  For the @{const "nat"} function for converting an integer to a natural
  number, we give a specific implementation using an ML function that
  returns its input value, provided that it is non-negative, and otherwise
  returns @{text "0"}.
*}

consts_code
  int ("(_)")
  nat ("\<module>nat")
attach {*
fun nat i = if i < 0 then 0 else i;
*}

code_const int
  (SML "_")
  (Haskell "_")

code_const nat_of_int
  (SML "_")
  (Haskell "_")


subsection {* Preprocessors *}

text {*
  In contrast to @{term "Suc n"}, the term @{term "n + (1::nat)"} is no longer
  a constructor term. Therefore, all occurrences of this term in a position
  where a pattern is expected (i.e.\ on the left-hand side of a recursion
  equation or in the arguments of an inductive relation in an introduction
  rule) must be eliminated.
  This can be accomplished by applying the following transformation rules:
*}

theorem Suc_if_eq: "(\<And>n. f (Suc n) = h n) \<Longrightarrow> f 0 = g \<Longrightarrow>
  f n = (if n = 0 then g else h (n - 1))"
  by (case_tac n) simp_all

theorem Suc_clause: "(\<And>n. P n (Suc n)) \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> P (n - 1) n"
  by (case_tac n) simp_all

text {*
  The rules above are built into a preprocessor that is plugged into
  the code generator. Since the preprocessor for introduction rules
  does not know anything about modes, some of the modes that worked
  for the canonical representation of natural numbers may no longer work.
*}

(*<*)

ML {*
local
  val Suc_if_eq = thm "Suc_if_eq";
  val Suc_clause = thm "Suc_clause";
  fun contains_suc t = member (op =) (term_consts t) "Suc";
in

fun remove_suc thy thms =
  let
    val Suc_if_eq' = Thm.transfer thy Suc_if_eq;
    val vname = Name.variant (map fst
      (fold (Term.add_varnames o Thm.full_prop_of) thms [])) "x";
    val cv = cterm_of Main.thy (Var ((vname, 0), HOLogic.natT));
    fun lhs_of th = snd (Thm.dest_comb
      (fst (Thm.dest_comb (snd (Thm.dest_comb (cprop_of th))))));
    fun rhs_of th = snd (Thm.dest_comb (snd (Thm.dest_comb (cprop_of th))));
    fun find_vars ct = (case term_of ct of
        (Const ("Suc", _) $ Var _) => [(cv, snd (Thm.dest_comb ct))]
      | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in 
          map (apfst (fn ct => Thm.capply ct ct2)) (find_vars ct1) @
          map (apfst (Thm.capply ct1)) (find_vars ct2)
        end
      | _ => []);
    val eqs = List.concat (map
      (fn th => map (pair th) (find_vars (lhs_of th))) thms);
    fun mk_thms (th, (ct, cv')) =
      let
        val th' =
          Thm.implies_elim
           (Drule.fconv_rule (Thm.beta_conversion true)
             (Drule.instantiate'
               [SOME (ctyp_of_term ct)] [SOME (Thm.cabs cv ct),
                 SOME (Thm.cabs cv' (rhs_of th)), NONE, SOME cv']
               Suc_if_eq')) (Thm.forall_intr cv' th)
      in
        case map_filter (fn th'' =>
            SOME (th'', singleton
              (Variable.trade (K (fn [th'''] => [th''' RS th'])) (Variable.thm_context th'')) th'')
          handle THM _ => NONE) thms of
            [] => NONE
          | thps =>
              let val (ths1, ths2) = split_list thps
              in SOME (subtract eq_thm (th :: ths1) thms @ ths2) end
      end
  in
    case get_first mk_thms eqs of
      NONE => thms
    | SOME x => remove_suc thy x
  end;

fun eqn_suc_preproc thy ths =
  let
    val dest = fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of
  in
    if forall (can dest) ths andalso
      exists (contains_suc o dest) ths
    then remove_suc thy ths else ths
  end;

fun remove_suc_clause thy thms =
  let
    val Suc_clause' = Thm.transfer thy Suc_clause;
    val vname = Name.variant (map fst
      (fold (Term.add_varnames o Thm.full_prop_of) thms [])) "x";
    fun find_var (t as Const ("Suc", _) $ (v as Var _)) = SOME (t, v)
      | find_var (t $ u) = (case find_var t of NONE => find_var u | x => x)
      | find_var _ = NONE;
    fun find_thm th =
      let val th' = ObjectLogic.atomize_thm th
      in Option.map (pair (th, th')) (find_var (prop_of th')) end
  in
    case get_first find_thm thms of
      NONE => thms
    | SOME ((th, th'), (Sucv, v)) =>
        let
          val cert = cterm_of (Thm.theory_of_thm th);
          val th'' = ObjectLogic.rulify (Thm.implies_elim
            (Drule.fconv_rule (Thm.beta_conversion true)
              (Drule.instantiate' []
                [SOME (cert (lambda v (Abs ("x", HOLogic.natT,
                   abstract_over (Sucv,
                     HOLogic.dest_Trueprop (prop_of th')))))),
                 SOME (cert v)] Suc_clause'))
            (Thm.forall_intr (cert v) th'))
        in
          remove_suc_clause thy (map (fn th''' =>
            if (op = o pairself prop_of) (th''', th) then th'' else th''') thms)
        end
  end;

fun clause_suc_preproc thy ths =
  let
    val dest = fst o HOLogic.dest_mem o HOLogic.dest_Trueprop
  in
    if forall (can (dest o concl_of)) ths andalso
      exists (fn th => member (op =) (foldr add_term_consts
        [] (map_filter (try dest) (concl_of th :: prems_of th))) "Suc") ths
    then remove_suc_clause thy ths else ths
  end;

end; (*local*)

local
  val meta_eq_to_obj_eq = thm "meta_eq_to_obj_eq";
  val eq_reflection = thm "eq_reflection";
in fun lift_obj_eq f thy =
  map (fn thm => thm RS meta_eq_to_obj_eq)
  #> f thy
  #> map (fn thm => thm RS eq_reflection)
end
*}

setup {*
  Codegen.add_preprocessor eqn_suc_preproc
  #> Codegen.add_preprocessor clause_suc_preproc
  #> CodegenData.add_preproc (lift_obj_eq eqn_suc_preproc)
  #> CodegenData.add_preproc (lift_obj_eq clause_suc_preproc)
*}
(*>*)

subsection {* Module names *}

code_modulename SML
  Nat Integer
  EfficientNat Integer

end
