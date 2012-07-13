theory Hotel_Example
imports Main "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
begin

datatype guest = Guest0 | Guest1
datatype key = Key0 | Key1 | Key2 | Key3
datatype room = Room0

type_synonym card = "key * key"

datatype event =
   Check_in guest room card | Enter guest room card | Exit guest room

definition initk :: "room \<Rightarrow> key"
  where "initk = (%r. Key0)"

declare initk_def[code_pred_def, code]

primrec owns :: "event list \<Rightarrow> room \<Rightarrow> guest option"
where
  "owns [] r = None"
| "owns (e#s) r = (case e of
    Check_in g r' c \<Rightarrow> if r' = r then Some g else owns s r |
    Enter g r' c \<Rightarrow> owns s r |
    Exit g r' \<Rightarrow> owns s r)"

primrec currk :: "event list \<Rightarrow> room \<Rightarrow> key"
where
  "currk [] r = initk r"
| "currk (e#s) r = (let k = currk s r in
    case e of Check_in g r' (k1, k2) \<Rightarrow> if r' = r then k2 else k
            | Enter g r' c \<Rightarrow> k
            | Exit g r \<Rightarrow> k)"

primrec issued :: "event list \<Rightarrow> key set"
where
  "issued [] = range initk"
| "issued (e#s) = issued s \<union>
  (case e of Check_in g r (k1, k2) \<Rightarrow> {k2} | Enter g r c \<Rightarrow> {} | Exit g r \<Rightarrow> {})"

primrec cards :: "event list \<Rightarrow> guest \<Rightarrow> card set"
where
  "cards [] g = {}"
| "cards (e#s) g = (let C = cards s g in
                    case e of Check_in g' r c \<Rightarrow> if g' = g then insert c C
                                                else C
                            | Enter g r c \<Rightarrow> C
                            | Exit g r \<Rightarrow> C)"

primrec roomk :: "event list \<Rightarrow> room \<Rightarrow> key"
where
  "roomk [] r = initk r"
| "roomk (e#s) r = (let k = roomk s r in
    case e of Check_in g r' c \<Rightarrow> k
            | Enter g r' (x,y) \<Rightarrow> if r' = r (*& x = k*) then y else k
            | Exit g r \<Rightarrow> k)"

primrec isin :: "event list \<Rightarrow> room \<Rightarrow> guest set"
where
  "isin [] r = {}"
| "isin (e#s) r = (let G = isin s r in
                 case e of Check_in g r c \<Rightarrow> G
                 | Enter g r' c \<Rightarrow> if r' = r then {g} \<union> G else G
                 | Exit g r' \<Rightarrow> if r'=r then G - {g} else G)"

primrec hotel :: "event list \<Rightarrow> bool"
where
  "hotel []  = True"
| "hotel (e # s) = (hotel s & (case e of
  Check_in g r (k,k') \<Rightarrow> k = currk s r \<and> k' \<notin> issued s |
  Enter g r (k,k') \<Rightarrow> (k,k') : cards s g & (roomk s r : {k, k'}) |
  Exit g r \<Rightarrow> g : isin s r))"

definition no_Check_in :: "event list \<Rightarrow> room \<Rightarrow> bool" where(*>*)
[code del]: "no_Check_in s r \<equiv> \<not>(\<exists>g c. Check_in g r c \<in> set s)"

definition feels_safe :: "event list \<Rightarrow> room \<Rightarrow> bool"
where
  "feels_safe s r = (\<exists>s\<^isub>1 s\<^isub>2 s\<^isub>3 g c c'.
   s = s\<^isub>3 @ [Enter g r c] @ s\<^isub>2 @ [Check_in g r c'] @ s\<^isub>1 \<and>
   no_Check_in (s\<^isub>3 @ s\<^isub>2) r \<and> isin (s\<^isub>2 @ [Check_in g r c] @ s\<^isub>1) r = {})"


section {* Some setup *}

lemma issued_nil: "issued [] = {Key0}"
by (auto simp add: initk_def)

lemmas issued_simps[code] = issued_nil issued.simps(2)


setup {*  Predicate_Compile_Data.ignore_consts [@{const_name Set.member},
  @{const_name "issued"}, @{const_name "cards"}, @{const_name "isin"},
  @{const_name Collect}, @{const_name insert}] *}
ML {* Core_Data.force_modes_and_compilations *}

fun find_first :: "('a => 'b option) => 'a list => 'b option"
where
  "find_first f [] = None"
| "find_first f (x # xs) = (case f x of Some y => Some y | None => find_first f xs)"

consts cps_of_set :: "'a set => ('a => term list option) => term list option"

lemma
  [code]: "cps_of_set (set xs) f = find_first f xs"
sorry

consts pos_cps_of_set :: "'a set => ('a => (bool * term list) option) => code_numeral => (bool * term list) option"
consts neg_cps_of_set :: "'a set => ('a Quickcheck_Exhaustive.unknown => term list Quickcheck_Exhaustive.three_valued) => code_numeral => term list Quickcheck_Exhaustive.three_valued"

lemma
  [code]: "pos_cps_of_set (set xs) f i = find_first f xs"
sorry

consts find_first' :: "('b Quickcheck_Exhaustive.unknown => 'a Quickcheck_Exhaustive.three_valued)
    => 'b list => 'a Quickcheck_Exhaustive.three_valued"

lemma [code]:
  "find_first' f [] = Quickcheck_Exhaustive.No_value"
  "find_first' f (x # xs) = (case f (Quickcheck_Exhaustive.Known x) of Quickcheck_Exhaustive.No_value => find_first' f xs | Quickcheck_Exhaustive.Value x => Quickcheck_Exhaustive.Value x | Quickcheck_Exhaustive.Unknown_value => (case find_first' f xs of Quickcheck_Exhaustive.Value x => Quickcheck_Exhaustive.Value x | _ => Quickcheck_Exhaustive.Unknown_value))"
sorry

lemma
  [code]: "neg_cps_of_set (set xs) f i = find_first' f xs"
sorry

setup {*
let
  val Fun = Predicate_Compile_Aux.Fun
  val Input = Predicate_Compile_Aux.Input
  val Output = Predicate_Compile_Aux.Output
  val Bool = Predicate_Compile_Aux.Bool
  val oi = Fun (Output, Fun (Input, Bool))
  val ii = Fun (Input, Fun (Input, Bool))
  fun of_set compfuns (Type ("fun", [T, _])) =
    case body_type (Predicate_Compile_Aux.mk_monadT compfuns T) of
      Type ("Quickcheck_Exhaustive.three_valued", _) => 
        Const(@{const_name neg_cps_of_set}, HOLogic.mk_setT T --> (Predicate_Compile_Aux.mk_monadT compfuns T))
    | _ => Const(@{const_name pos_cps_of_set}, HOLogic.mk_setT T --> (Predicate_Compile_Aux.mk_monadT compfuns T))
  fun member compfuns (U as Type ("fun", [T, _])) =
    (absdummy T (absdummy (HOLogic.mk_setT T) (Predicate_Compile_Aux.mk_if compfuns
      (Const (@{const_name "Set.member"}, T --> HOLogic.mk_setT T --> @{typ bool}) $ Bound 1 $ Bound 0))))
 
in
  Core_Data.force_modes_and_compilations @{const_name Set.member}
    [(oi, (of_set, false)), (ii, (member, false))]
end
*}
section {* Property *}

lemma "\<lbrakk> hotel s; g \<in> isin s r \<rbrakk> \<Longrightarrow> owns s r = Some g"
quickcheck[tester = exhaustive, size = 6, expect = counterexample]
quickcheck[tester = smart_exhaustive, depth = 6, expect = counterexample]
oops

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[smart_exhaustive, depth = 10, allow_function_inversion, expect = counterexample]
oops

section {* Refinement *}

fun split_list
where
  "split_list [] = [([], [])]"
| "split_list (z # zs) = (([], z # zs) # [(z # xs', ys'). (xs', ys') <- split_list zs])"

lemma split_list: "((xs, ys) \<in> set (split_list zs)) = (zs = xs @ ys)"
apply (induct zs arbitrary: xs ys)
apply fastforce
apply (case_tac xs)
apply auto
done

lemma [code]: "no_Check_in s r = list_all (%x. case x of Check_in g r' c => r \<noteq> r' | _ => True) s"
unfolding no_Check_in_def list_all_iff
apply auto
apply (case_tac x)
apply auto
done

lemma [code]: "feels_safe s r = list_ex (%(s3, s2, s1, g, c, c'). no_Check_in (s3 @ s2) r &
    isin (s2 @ [Check_in g r c] @ s1) r = {}) ([(s3, s2, s1, g, c, c'). (s3, Enter g' r' c # r3) <- split_list s, r' = r, (s2, Check_in g r'' c' # s1) <- split_list r3, r'' = r, g = g'])"
unfolding feels_safe_def list_ex_iff
by auto (metis split_list)+

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
(* quickcheck[exhaustive, size = 9, timeout = 2000] -- maybe possible with a lot of time *)
quickcheck[narrowing, size = 7, expect = counterexample]
oops

end
