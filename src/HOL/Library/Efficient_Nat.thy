(*  Title:      HOL/Library/Efficient_Nat.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of natural numbers by integers *}

theory Efficient_Nat
imports Main Code_Integer
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
  An int-to-nat conversion
  restricted to non-negative ints (in contrast to @{const nat}).
  Note that this restriction has no logical relevance and
  is just a kind of proof hint -- nothing prevents you from 
  writing nonsense like @{term "nat_of_int (-4)"}
*}

definition
  nat_of_int :: "int \<Rightarrow> nat" where
  "k \<ge> 0 \<Longrightarrow> nat_of_int k = nat k"

definition
  int_of_nat :: "nat \<Rightarrow> int" where
  [code func del]: "int_of_nat n = of_nat n"

lemma int_of_nat_Suc [simp]:
  "int_of_nat (Suc n) = 1 + int_of_nat n"
  unfolding int_of_nat_def by simp

lemma int_of_nat_add:
  "int_of_nat (m + n) = int_of_nat m + int_of_nat n"
  unfolding int_of_nat_def by (rule of_nat_add)

lemma int_of_nat_mult:
  "int_of_nat (m * n) = int_of_nat m * int_of_nat n"
  unfolding int_of_nat_def by (rule of_nat_mult)

lemma nat_of_int_of_number_of:
  fixes k
  assumes "k \<ge> 0"
  shows "number_of k = nat_of_int (number_of k)"
  unfolding nat_of_int_def [OF assms] nat_number_of_def number_of_is_id ..

lemma nat_of_int_of_number_of_aux:
  fixes k
  assumes "Numeral.Pls \<le> k \<equiv> True"
  shows "k \<ge> 0"
  using assms unfolding Pls_def by simp

lemma nat_of_int_int:
  "nat_of_int (int_of_nat n) = n"
  using nat_of_int_def int_of_nat_def by simp

lemma eq_nat_of_int: "int_of_nat n = x \<Longrightarrow> n = nat_of_int x"
by (erule subst, simp only: nat_of_int_int)

code_datatype nat_of_int

text {*
  Case analysis on natural numbers is rephrased using a conditional
  expression:
*}

lemma [code unfold, code inline del]:
  "nat_case = (\<lambda>f g n. if n = 0 then f else g (n - 1))"
proof -
  have rewrite: "\<And>f g n. nat_case f g n = (if n = 0 then f else g (n - 1))"
  proof -
    fix f g n
    show "nat_case f g n = (if n = 0 then f else g (n - 1))"
      by (cases n) simp_all
  qed
  show "nat_case = (\<lambda>f g n. if n = 0 then f else g (n - 1))"
    by (rule eq_reflection ext rewrite)+ 
qed

lemma [code inline]:
  "nat_case = (\<lambda>f g n. if n = 0 then f else g (nat_of_int (int_of_nat n - 1)))"
proof (rule ext)+
  fix f g n
  show "nat_case f g n = (if n = 0 then f else g (nat_of_int (int_of_nat n - 1)))"
  by (cases n) (simp_all add: nat_of_int_int)
qed

text {*
  Most standard arithmetic functions on natural numbers are implemented
  using their counterparts on the integers:
*}

lemma [code func]: "0 = nat_of_int 0"
  by (simp add: nat_of_int_def)

lemma [code func, code inline]:  "1 = nat_of_int 1"
  by (simp add: nat_of_int_def)

lemma [code func]: "Suc n = nat_of_int (int_of_nat n + 1)"
  by (simp add: eq_nat_of_int)

lemma [code]: "m + n = nat (int_of_nat m + int_of_nat n)"
  by (simp add: int_of_nat_def nat_eq_iff2)

lemma [code func, code inline]: "m + n = nat_of_int (int_of_nat m + int_of_nat n)"
  by (simp add: eq_nat_of_int int_of_nat_add)

lemma [code, code inline]: "m - n = nat (int_of_nat m - int_of_nat n)"
  by (simp add: int_of_nat_def nat_eq_iff2 of_nat_diff)

lemma [code]: "m * n = nat (int_of_nat m * int_of_nat n)"
  unfolding int_of_nat_def
  by (simp add: of_nat_mult [symmetric] del: of_nat_mult)

lemma [code func, code inline]: "m * n = nat_of_int (int_of_nat m * int_of_nat n)"
  by (simp add: eq_nat_of_int int_of_nat_mult)

lemma [code]: "m div n = nat (int_of_nat m div int_of_nat n)"
  unfolding int_of_nat_def zdiv_int [symmetric] by simp

lemma div_nat_code [code func]:
  "m div k = nat_of_int (fst (divAlg (int_of_nat m, int_of_nat k)))"
  unfolding div_def [symmetric] int_of_nat_def zdiv_int [symmetric]
  unfolding int_of_nat_def [symmetric] nat_of_int_int ..

lemma [code]: "m mod n = nat (int_of_nat m mod int_of_nat n)"
  unfolding int_of_nat_def zmod_int [symmetric] by simp

lemma mod_nat_code [code func]:
  "m mod k = nat_of_int (snd (divAlg (int_of_nat m, int_of_nat k)))"
  unfolding mod_def [symmetric] int_of_nat_def zmod_int [symmetric]
  unfolding int_of_nat_def [symmetric] nat_of_int_int ..

lemma [code, code inline]: "m < n \<longleftrightarrow> int_of_nat m < int_of_nat n"
  unfolding int_of_nat_def by simp

lemma [code func, code inline]: "m \<le> n \<longleftrightarrow> int_of_nat m \<le> int_of_nat n"
  unfolding int_of_nat_def by simp

lemma [code func, code inline]: "m = n \<longleftrightarrow> int_of_nat m = int_of_nat n"
  unfolding int_of_nat_def by simp

lemma [code func]: "nat k = (if k < 0 then 0 else nat_of_int k)"
  by (cases "k < 0") (simp, simp add: nat_of_int_def)

lemma [code func]:
  "int_aux n i = (if int_of_nat n = 0 then i else int_aux (nat_of_int (int_of_nat n - 1)) (i + 1))"
proof -
  have "0 < n \<Longrightarrow> int_of_nat n = 1 + int_of_nat (nat_of_int (int_of_nat n - 1))"
  proof -
    assume prem: "n > 0"
    then have "int_of_nat n - 1 \<ge> 0" unfolding int_of_nat_def by auto
    then have "nat_of_int (int_of_nat n - 1) = nat (int_of_nat n - 1)" by (simp add: nat_of_int_def)
    with prem show "int_of_nat n = 1 + int_of_nat (nat_of_int (int_of_nat n - 1))" unfolding int_of_nat_def by simp
  qed
  then show ?thesis unfolding int_aux_def int_of_nat_def by auto
qed


subsection {* Code generator setup for basic functions *}

text {*
  @{typ nat} is no longer a datatype but embedded into the integers.
*}

code_type nat
  (SML "int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")

types_code
  nat ("int")
attach (term_of) {*
val term_of_nat = HOLogic.mk_number HOLogic.natT;
*}
attach (test) {*
fun gen_nat i =
  let val n = random_range 0 i
  in (n, fn () => term_of_nat n) end;
*}

consts_code
  "0 \<Colon> nat" ("0")
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
  int_of_nat ("(_)")
  nat ("\<module>nat")
attach {*
fun nat i = if i < 0 then 0 else i;
*}

code_const int_of_nat
  (SML "_")
  (OCaml "_")
  (Haskell "_")

code_const index_of_nat
  (SML "_")
  (OCaml "_")
  (Haskell "_")

code_const nat_of_int
  (SML "_")
  (OCaml "_")
  (Haskell "_")

code_const nat_of_index
  (SML "_")
  (OCaml "_")
  (Haskell "_")


text {* Using target language div and mod *}

code_const "op div \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.div ((_), (_))")
  (OCaml "Big'_int.div'_big'_int")
  (Haskell "div")

code_const "op mod \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.mod ((_), (_))")
  (OCaml "Big'_int.mod'_big'_int")
  (Haskell "mod")


subsection {* Preprocessors *}

text {*
  Natural numerals should be expressed using @{const nat_of_int}.
*}

lemmas [code inline del] = nat_number_of_def

ML {*
fun nat_of_int_of_number_of thy cts =
  let
    val simplify_less = Simplifier.rewrite 
      (HOL_basic_ss addsimps (@{thms less_numeral_code} @ @{thms less_eq_numeral_code}));
    fun mk_rew (t, ty) =
      if ty = HOLogic.natT andalso 0 <= HOLogic.dest_numeral t then
        Thm.capply @{cterm "(op \<le>) Numeral.Pls"} (Thm.cterm_of thy t)
        |> simplify_less
        |> (fn thm => @{thm nat_of_int_of_number_of_aux} OF [thm])
        |> (fn thm => @{thm nat_of_int_of_number_of} OF [thm])
        |> (fn thm => @{thm eq_reflection} OF [thm])
        |> SOME
      else NONE
  in
    fold (HOLogic.add_numerals o Thm.term_of) cts []
    |> map_filter mk_rew
  end;
*}

setup {*
  Code.add_inline_proc ("nat_of_int_of_number_of", nat_of_int_of_number_of)
*}

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
fun remove_suc thy thms =
  let
    val vname = Name.variant (map fst
      (fold (Term.add_varnames o Thm.full_prop_of) thms [])) "x";
    val cv = cterm_of thy (Var ((vname, 0), HOLogic.natT));
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
    val eqs = maps
      (fn th => map (pair th) (find_vars (lhs_of th))) thms;
    fun mk_thms (th, (ct, cv')) =
      let
        val th' =
          Thm.implies_elim
           (Conv.fconv_rule (Thm.beta_conversion true)
             (Drule.instantiate'
               [SOME (ctyp_of_term ct)] [SOME (Thm.cabs cv ct),
                 SOME (Thm.cabs cv' (rhs_of th)), NONE, SOME cv']
               @{thm Suc_if_eq})) (Thm.forall_intr cv' th)
      in
        case map_filter (fn th'' =>
            SOME (th'', singleton
              (Variable.trade (K (fn [th'''] => [th''' RS th'])) (Variable.thm_context th'')) th'')
          handle THM _ => NONE) thms of
            [] => NONE
          | thps =>
              let val (ths1, ths2) = split_list thps
              in SOME (subtract Thm.eq_thm (th :: ths1) thms @ ths2) end
      end
  in
    case get_first mk_thms eqs of
      NONE => thms
    | SOME x => remove_suc thy x
  end;

fun eqn_suc_preproc thy ths =
  let
    val dest = fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of;
    fun contains_suc t = member (op =) (term_consts t) @{const_name Suc};
  in
    if forall (can dest) ths andalso
      exists (contains_suc o dest) ths
    then remove_suc thy ths else ths
  end;

fun remove_suc_clause thy thms =
  let
    val vname = Name.variant (map fst
      (fold (Term.add_varnames o Thm.full_prop_of) thms [])) "x";
    fun find_var (t as Const (@{const_name Suc}, _) $ (v as Var _)) = SOME (t, v)
      | find_var (t $ u) = (case find_var t of NONE => find_var u | x => x)
      | find_var _ = NONE;
    fun find_thm th =
      let val th' = Conv.fconv_rule ObjectLogic.atomize th
      in Option.map (pair (th, th')) (find_var (prop_of th')) end
  in
    case get_first find_thm thms of
      NONE => thms
    | SOME ((th, th'), (Sucv, v)) =>
        let
          val cert = cterm_of (Thm.theory_of_thm th);
          val th'' = ObjectLogic.rulify (Thm.implies_elim
            (Conv.fconv_rule (Thm.beta_conversion true)
              (Drule.instantiate' []
                [SOME (cert (lambda v (Abs ("x", HOLogic.natT,
                   abstract_over (Sucv,
                     HOLogic.dest_Trueprop (prop_of th')))))),
                 SOME (cert v)] @{thm Suc_clause}))
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

fun lift_obj_eq f thy =
  map (fn thm => thm RS @{thm meta_eq_to_obj_eq})
  #> f thy
  #> map (fn thm => thm RS @{thm eq_reflection})
  #> map (Conv.fconv_rule Drule.beta_eta_conversion)
*}

setup {*
  Codegen.add_preprocessor eqn_suc_preproc
  #> Codegen.add_preprocessor clause_suc_preproc
  #> Code.add_preproc ("eqn_Suc", lift_obj_eq eqn_suc_preproc)
  #> Code.add_preproc ("clause_Suc", lift_obj_eq clause_suc_preproc)
*}
(*>*)


subsection {* Module names *}

code_modulename SML
  Nat Integer
  Divides Integer
  Efficient_Nat Integer

code_modulename OCaml
  Nat Integer
  Divides Integer
  Efficient_Nat Integer

code_modulename Haskell
  Nat Integer
  Divides Integer
  Efficient_Nat Integer

hide const nat_of_int int_of_nat

end
