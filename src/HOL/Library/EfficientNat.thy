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

types_code nat ("int")
consts_code
  0 :: nat ("0")
  Suc ("(_ + 1)")
  nat ("nat")
  int ("(_)")

ML {*
fun nat i = if i < 0 then 0 else i;
*}

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

subsection {* Preprocessors *}

text {*
In contrast to @{term "Suc n"}, the term @{term "n + (1::nat)"} is no longer
a constructor term. Therefore, all occurrences of this term in a position
where a pattern is expected (i.e.\ on the left-hand side of a recursion
equation or in the arguments of an inductive relation in an introduction
rule) must be eliminated.
This can be accomplished by applying the following transformation rules:
*}

theorem Suc_if_eq: "f 0 = g \<Longrightarrow> (\<And>n. f (Suc n) = h n) \<Longrightarrow>
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
    val ctzero = cterm_of (sign_of Main.thy) HOLogic.zero;
    val vname = variant (map fst
      (Library.foldl add_term_varnames ([], map prop_of thms))) "x";
    val cv = cterm_of (sign_of Main.thy) (Var ((vname, 0), HOLogic.natT));
    fun lhs_of th = snd (Thm.dest_comb
      (fst (Thm.dest_comb (snd (Thm.dest_comb (cprop_of th))))));
    fun rhs_of th = snd (Thm.dest_comb (snd (Thm.dest_comb (cprop_of th))));
    fun find_vars ct = (case term_of ct of
        (Const ("Suc", _) $ Var _) => [((cv, ctzero), snd (Thm.dest_comb ct))]
      | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in 
          map (apfst (pairself (fn ct => Thm.capply ct ct2))) (find_vars ct1) @
          map (apfst (pairself (Thm.capply ct1))) (find_vars ct2)
        end
      | _ => []);
    val eqs1 = List.concat (map
      (fn th => map (pair th) (find_vars (lhs_of th))) thms);
    val eqs2 = map (fn x as (_, ((_, ctzero), _)) => (x, List.mapPartial (fn th =>
      SOME (th, Thm.cterm_match (lhs_of th, ctzero))
        handle Pattern.MATCH => NONE) thms)) eqs1;
    fun distinct_vars vs = forall is_Var vs andalso null (duplicates vs);
    val eqs2' = map (apsnd (List.filter (fn (_, (_, s)) =>
      distinct_vars (map (term_of o snd) s)))) eqs2;
    fun mk_thms b ((th, ((ct, _), cv')), (th', s) :: _) =
      let
        val th'' = Thm.instantiate s th';
        val th''' =
          Thm.implies_elim (Thm.implies_elim
           (Drule.fconv_rule (Thm.beta_conversion true)
             (Drule.instantiate'
               [SOME (ctyp_of_term ct)] [SOME (Thm.cabs cv ct),
                 SOME (rhs_of th''), SOME (Thm.cabs cv' (rhs_of th)), SOME cv']
               Suc_if_eq')) th'') (Thm.forall_intr cv' th)
      in
        List.mapPartial (fn thm =>
          if thm = th then SOME th'''
          else if b andalso thm = th' then NONE
          else SOME thm) thms
      end
  in
    case Library.find_first (not o null o snd) eqs2' of
      NONE => (case Library.find_first (not o null o snd) eqs2 of
        NONE => thms
      | SOME x => remove_suc thy (mk_thms false x))
    | SOME x => remove_suc thy (mk_thms true x)
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
      (Library.foldl add_term_varnames ([], map prop_of thms))) "x";
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
          val cert = cterm_of (sign_of_thm th);
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
