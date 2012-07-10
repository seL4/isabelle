theory Needham_Schroeder_No_Attacker_Example
imports Main "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
begin

datatype agent = Alice | Bob | Spy

definition agents :: "agent set"
where
  "agents = {Spy, Alice, Bob}"

definition bad :: "agent set"
where
  "bad = {Spy}"

datatype key = pubEK agent | priEK agent

fun invKey
where
  "invKey (pubEK A) = priEK A"
| "invKey (priEK A) = pubEK A"

datatype
     msg = Agent  agent     --{*Agent names*}
         | Key    key
         | Nonce  nat       --{*Unguessable nonces*}
         | MPair  msg msg   --{*Compound messages*}
         | Crypt  key msg   --{*Encryption, public- or shared-key*}

text{*Concrete syntax: messages appear as {|A,B,NA|}, etc...*}
syntax
  "_MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "_MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "CONST MPair x y"

inductive_set
  parts :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro]:               "X \<in> H ==> X \<in> parts H"
  | Fst:         "{|X,Y|}   \<in> parts H ==> X \<in> parts H"
  | Snd:         "{|X,Y|}   \<in> parts H ==> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H ==> X \<in> parts H"

inductive_set
  analz :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro,simp] :    "X \<in> H ==> X \<in> analz H"
  | Fst:     "{|X,Y|} \<in> analz H ==> X \<in> analz H"
  | Snd:     "{|X,Y|} \<in> analz H ==> Y \<in> analz H"
  | Decrypt [dest]: 
             "[|Crypt K X \<in> analz H; Key(invKey K): analz H|] ==> X \<in> analz H"

inductive_set
  synth :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj    [intro]:   "X \<in> H ==> X \<in> synth H"
  | Agent  [intro]:   "Agent agt \<in> synth H"
  | MPair  [intro]:   "[|X \<in> synth H;  Y \<in> synth H|] ==> {|X,Y|} \<in> synth H"
  | Crypt  [intro]:   "[|X \<in> synth H;  Key(K) \<in> H|] ==> Crypt K X \<in> synth H"

primrec initState
where
  initState_Alice:
    "initState Alice = {Key (priEK Alice)} \<union> (Key ` pubEK ` agents)"
| initState_Bob:
    "initState Bob = {Key (priEK Bob)} \<union> (Key ` pubEK ` agents)"

| initState_Spy:
    "initState Spy        =  (Key ` priEK ` bad) \<union> (Key ` pubEK ` agents)"

datatype
  event = Says  agent agent msg
        | Gets  agent       msg
        | Notes agent       msg


primrec knows :: "agent => event list => msg set"
where
  knows_Nil:   "knows A [] = initState A"
| knows_Cons:
    "knows A (ev # evs) =
       (if A = Spy then 
        (case ev of
           Says A' B X => insert X (knows Spy evs)
         | Gets A' X => knows Spy evs
         | Notes A' X  => 
             if A' \<in> bad then insert X (knows Spy evs) else knows Spy evs)
        else
        (case ev of
           Says A' B X => 
             if A'=A then insert X (knows A evs) else knows A evs
         | Gets A' X    => 
             if A'=A then insert X (knows A evs) else knows A evs
         | Notes A' X    => 
             if A'=A then insert X (knows A evs) else knows A evs))"

abbreviation (input)
  spies  :: "event list => msg set" where
  "spies == knows Spy"

primrec used :: "event list => msg set"
where
  used_Nil:   "used []         = Union (parts ` initState ` agents)"
| used_Cons:  "used (ev # evs) =
                     (case ev of
                        Says A B X => parts {X} \<union> used evs
                      | Gets A X   => used evs
                      | Notes A X  => parts {X} \<union> used evs)"
   (* --{*The case for @{term Gets} seems anomalous, but @{term Gets} always
        follows @{term Says} in real protocols.  Seems difficult to change.
        See @{text Gets_correct} in theory @{text "Guard/Extensions.thy"}. *}*)

inductive_set ns_public :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> ns_public"
         (*Alice initiates a protocol run, sending a nonce to Bob*)
 | NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in>  ns_public"
         (*Bob responds to Alice's message with a further nonce*)
 | NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Says A' B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs2  \<in>  ns_public"

         (*Alice proves her existence by sending NB back to Bob.*)
 | NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Says B' A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) (Nonce NB)) # evs3 \<in> ns_public"


subsection {* Preparations for sets *}

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
    | Type ("Predicate.pred", _) => Const(@{const_name pred_of_set}, HOLogic.mk_setT T --> Predicate_Compile_Aux.mk_monadT compfuns T)
    | _ => Const(@{const_name pos_cps_of_set}, HOLogic.mk_setT T --> (Predicate_Compile_Aux.mk_monadT compfuns T))
  fun member compfuns (U as Type ("fun", [T, _])) =
    (absdummy T (absdummy (HOLogic.mk_setT T) (Predicate_Compile_Aux.mk_if compfuns
      (Const (@{const_name "Set.member"}, T --> HOLogic.mk_setT T --> @{typ bool}) $ Bound 1 $ Bound 0))))
 
in
  Core_Data.force_modes_and_compilations @{const_name Set.member}
    [(oi, (of_set, false)), (ii, (member, false))]
end
*}

subsection {* Derived equations for analz, parts and synth *}

lemma [code]:
  "analz H = (let
     H' = H \<union> (Union ((%m. case m of {|X, Y|} => {X, Y} | Crypt K X => if Key (invKey K) : H then {X} else {} | _ => {}) ` H))
   in if H' = H then H else analz H')"
sorry

lemma [code]:
  "parts H = (let
     H' = H \<union> (Union ((%m. case m of {|X, Y|} => {X, Y} | Crypt K X => {X} | _ => {}) ` H))
   in if H' = H then H else parts H')"
sorry

code_pred [skip_proof] ns_publicp .
thm ns_publicp.equation

code_pred [generator_cps] ns_publicp .
thm ns_publicp.generator_cps_equation

setup {* Predicate_Compile_Data.ignore_consts [@{const_name analz}, @{const_name knows}] *}
declare ListMem_iff[symmetric, code_pred_inline]

declare [[quickcheck_timing]]
setup {* Exhaustive_Generators.setup_exhaustive_datatype_interpretation *}
declare [[quickcheck_full_support = false]]

lemma "ns_publicp evs ==> \<not> (Says Alice Bob (Crypt (pubEK Bob) (Nonce NB))) : set evs"
(*quickcheck[random, iterations = 1000000, size = 20, timeout = 3600, verbose]
quickcheck[exhaustive, size = 8, timeout = 3600, verbose]
quickcheck[narrowing, size = 7, timeout = 3600, verbose]*)
quickcheck[smart_exhaustive, depth = 5, timeout = 30, expect = counterexample]
oops

lemma
  "\<lbrakk>ns_publicp evs\<rbrakk>            
       \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) : set evs
       \<Longrightarrow> A \<noteq> Spy \<Longrightarrow> B \<noteq> Spy \<Longrightarrow> A \<noteq> B 
           \<Longrightarrow> Nonce NB \<notin> analz (spies evs)"
quickcheck[smart_exhaustive, depth = 6, timeout = 30]
quickcheck[narrowing, size = 6, timeout = 30, verbose]
oops

end