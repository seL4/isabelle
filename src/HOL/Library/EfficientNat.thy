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

subsection {* Basic functions *}

text {*
The implementation of @{term "0::nat"} and @{term "Suc"} using the
ML integers is straightforward. Since natural numbers are implemented
using integers, the coercion function @{term "int"} of type
@{typ "nat \<Rightarrow> int"} is simply implemented by the identity function.
For the @{term "nat"} function for converting an integer to a natural
number, we give a specific implementation using an ML function that
returns its input value, provided that it is non-negative, and otherwise
returns @{text "0"}.
*}

types_code
  nat ("int")
attach (term_of) {*
fun term_of_nat 0 = Const ("0", HOLogic.natT)
  | term_of_nat 1 = Const ("1", HOLogic.natT)
  | term_of_nat i = HOLogic.number_of_const HOLogic.natT $
      HOLogic.mk_bin (IntInf.fromInt i);
*}
attach (test) {*
fun gen_nat i = random_range 0 i;
*}

consts_code
  0 :: nat ("0")
  Suc ("(_ + 1)")
  nat ("\<module>nat")
attach {*
fun nat i = if i < 0 then 0 else i;
*}
  int ("(_)")

text {*
Case analysis on natural numbers is rephrased using a conditional
expression:
*}

lemma [code unfold]: "nat_case \<equiv> (\<lambda>f g n. if n = 0 then f else g (n - 1))"
  apply (rule eq_reflection ext)+
  apply (case_tac n)
  apply simp_all
  done

text {*
Most standard arithmetic functions on natural numbers are implemented
using their counterparts on the integers:
*}

lemma [code]: "m - n = nat (int m - int n)" by arith
lemma [code]: "m + n = nat (int m + int n)" by arith
lemma [code]: "m * n = nat (int m * int n)"
  by (simp add: zmult_int)
lemma [code]: "m div n = nat (int m div int n)"
  by (simp add: zdiv_int [symmetric])
lemma [code]: "m mod n = nat (int m mod int n)"
  by (simp add: zmod_int [symmetric])
lemma [code]: "(m < n) = (int m < int n)"
  by simp

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
val Suc_if_eq = thm "Suc_if_eq";

fun remove_suc thy thms =
  let
    val Suc_if_eq' = Thm.transfer thy Suc_if_eq;
    val vname = variant (map fst
      (fold (add_term_varnames o Thm.full_prop_of) thms [])) "x";
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
        case List.mapPartial (fn th'' =>
            SOME (th'', standard (Drule.freeze_all th'' RS th'))
          handle THM _ => NONE) thms of
            [] => NONE
          | thps =>
              let val (ths1, ths2) = ListPair.unzip thps
              in SOME (gen_rems eq_thm (thms, th :: ths1) @ ths2) end
      end
  in
    case Library.get_first mk_thms eqs of
      NONE => thms
    | SOME x => remove_suc thy x
  end;

fun eqn_suc_preproc thy ths =
  let val dest = fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of
  in
    if forall (can dest) ths andalso
      exists (fn th => "Suc" mem term_consts (dest th)) ths
    then remove_suc thy ths else ths
  end;

val Suc_clause = thm "Suc_clause";

fun remove_suc_clause thy thms =
  let
    val Suc_clause' = Thm.transfer thy Suc_clause;
    val vname = variant (map fst
      (fold (add_term_varnames o Thm.full_prop_of) thms [])) "x";
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
            if th''' = th then th'' else th''') thms)
        end
  end;

fun clause_suc_preproc thy ths =
  let val dest = fst o HOLogic.dest_mem o HOLogic.dest_Trueprop
  in
    if forall (can (dest o concl_of)) ths andalso
      exists (fn th => "Suc" mem foldr add_term_consts
        [] (List.mapPartial (try dest) (concl_of th :: prems_of th))) ths
    then remove_suc_clause thy ths else ths
  end;

val suc_preproc_setup =
  [Codegen.add_preprocessor eqn_suc_preproc,
   Codegen.add_preprocessor clause_suc_preproc];
*}

setup suc_preproc_setup
(*>*)

end
