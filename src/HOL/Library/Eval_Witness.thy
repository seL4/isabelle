(*  Title:      HOL/Library/Eval_Witness.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Evaluation Oracle with ML witnesses *}

theory Eval_Witness
imports List Main
begin

text {* 
  We provide an oracle method similar to "eval", but with the
  possibility to provide ML values as witnesses for existential
  statements.

  Our oracle can prove statements of the form @{term "EX x. P x"}
  where @{term "P"} is an executable predicate that can be compiled to
  ML. The oracle generates code for @{term "P"} and applies
  it to a user-specified ML value. If the evaluation
  returns true, this is effectively a proof of  @{term "EX x. P x"}.

  However, this is only sound if for every ML value of the given type
  there exists a corresponding HOL value, which could be used in an
  explicit proof. Unfortunately this is not true for function types,
  since ML functions are not equivalent to the pure HOL
  functions. Thus, the oracle can only be used on first-order
  types.

  We define a type class to mark types that can be safely used
  with the oracle.  
*}

class ml_equiv

text {*
  Instances of @{text "ml_equiv"} should only be declared for those types,
  where the universe of ML values coincides with the HOL values.

  Since this is essentially a statement about ML, there is no
  logical characterization.
*}

instance nat :: ml_equiv .. (* Attention: This conflicts with the "EfficientNat" theory *)
instance bool :: ml_equiv ..
instance list :: (ml_equiv) ml_equiv ..

ML {*
structure Eval_Method = Proof_Data
(
  type T = unit -> bool
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Eval_Method"
)
*}

oracle eval_witness_oracle = {* fn (cgoal, ws) =>
let
  val thy = Thm.theory_of_cterm cgoal;
  val goal = Thm.term_of cgoal;
  fun check_type T = 
    if Sorts.of_sort (Sign.classes_of thy) (T, ["Eval_Witness.ml_equiv"])
    then T
    else error ("Type " ^ quote (Syntax.string_of_typ_global thy T) ^ " not allowed for ML witnesses")

  fun dest_exs  0 t = t
    | dest_exs n (Const (@{const_name Ex}, _) $ Abs (v,T,b)) = 
      Abs (v, check_type T, dest_exs (n - 1) b)
    | dest_exs _ _ = raise Fail "dest_exs";
  val t = dest_exs (length ws) (HOLogic.dest_Trueprop goal);
in
  if Code_Runtime.dynamic_value_strict (Eval_Method.get, Eval_Method.put, "Eval_Method.put") thy NONE (K I) t ws
  then Thm.cterm_of thy goal
  else @{cprop True} (*dummy*)
end
*}


method_setup eval_witness = {*
  Scan.lift (Scan.repeat Args.name) >>
    (fn ws => K (SIMPLE_METHOD'
      (CSUBGOAL (fn (ct, i) => rtac (eval_witness_oracle (ct, ws)) i))))
*} "evaluation with ML witnesses"


subsection {* Toy Examples *}

text {* 
  Note that we must use the generated data structure for the
  naturals, since ML integers are different.
*}

(*lemma "\<exists>n::nat. n = 1"
apply (eval_witness "Suc Zero_nat")
done*)

text {* 
  Since polymorphism is not allowed, we must specify the
  type explicitly:
*}

lemma "\<exists>l. length (l::bool list) = 3"
apply (eval_witness "[true,true,true]")
done

text {* Multiple witnesses *}

lemma "\<exists>k l. length (k::bool list) = length (l::bool list)"
apply (eval_witness "[]" "[]")
done


subsection {* Discussion *}

subsubsection {* Conflicts *}

text {* 
  This theory conflicts with EfficientNat, since the @{text ml_equiv} instance
  for natural numbers is not valid when they are mapped to ML
  integers. With that theory loaded, we could use our oracle to prove
  @{term "\<exists>n. n < 0"} by providing @{text "~1"} as a witness.

  This shows that @{text ml_equiv} declarations have to be used with care,
  taking the configuration of the code generator into account.
*}

subsubsection {* Haskell *}

text {*
  If we were able to run generated Haskell code, the situation would
  be much nicer, since Haskell functions are pure and could be used as
  witnesses for HOL functions: Although Haskell functions are partial,
  we know that if the evaluation terminates, they are ``sufficiently
  defined'' and could be completed arbitrarily to a total (HOL) function.

  This would allow us to provide access to very efficient data
  structures via lookup functions coded in Haskell and provided to HOL
  as witnesses. 
*}

end