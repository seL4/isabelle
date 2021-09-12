theory Needham_Schroeder_Base
imports Main "HOL-Library.Predicate_Compile_Quickcheck"
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
     msg = Agent  agent
         | Key    key
         | Nonce  nat
         | MPair  msg msg
         | Crypt  key msg

syntax
  "_MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")
translations
  "\<lbrace>x, y, z\<rbrace>"   == "\<lbrace>x, \<lbrace>y, z\<rbrace>\<rbrace>"
  "\<lbrace>x, y\<rbrace>"      == "CONST MPair x y"

inductive_set
  parts :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro]:               "X \<in> H ==> X \<in> parts H"
  | Fst:         "\<lbrace>X,Y\<rbrace>   \<in> parts H ==> X \<in> parts H"
  | Snd:         "\<lbrace>X,Y\<rbrace>   \<in> parts H ==> Y \<in> parts H"
  | Body:        "Crypt K X \<in> parts H ==> X \<in> parts H"

inductive_set
  analz :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj [intro,simp] :    "X \<in> H ==> X \<in> analz H"
  | Fst:     "\<lbrace>X,Y\<rbrace> \<in> analz H ==> X \<in> analz H"
  | Snd:     "\<lbrace>X,Y\<rbrace> \<in> analz H ==> Y \<in> analz H"
  | Decrypt [dest]: 
             "[|Crypt K X \<in> analz H; Key(invKey K) \<in> analz H|] ==> X \<in> analz H"

inductive_set
  synth :: "msg set => msg set"
  for H :: "msg set"
  where
    Inj    [intro]:   "X \<in> H ==> X \<in> synth H"
  | Agent  [intro]:   "Agent agt \<in> synth H"
  | MPair  [intro]:   "[|X \<in> synth H;  Y \<in> synth H|] ==> \<lbrace>X,Y\<rbrace> \<in> synth H"
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
  used_Nil:   "used []         = \<Union>(parts ` initState ` agents)"
| used_Cons:  "used (ev # evs) =
                     (case ev of
                        Says A B X => parts {X} \<union> used evs
                      | Gets A X   => used evs
                      | Notes A X  => parts {X} \<union> used evs)"

subsection \<open>Preparations for sets\<close>

fun find_first :: "('a => 'b option) => 'a list => 'b option"
where
  "find_first f [] = None"
| "find_first f (x # xs) = (case f x of Some y => Some y | None => find_first f xs)"

consts cps_of_set :: "'a set => ('a => term list option) => term list option"

lemma
  [code]: "cps_of_set (set xs) f = find_first f xs"
sorry

consts pos_cps_of_set :: "'a set => ('a => (bool * term list) option) => natural => (bool * term list) option"
consts neg_cps_of_set :: "'a set => ('a Quickcheck_Exhaustive.unknown => term list Quickcheck_Exhaustive.three_valued) => natural => term list Quickcheck_Exhaustive.three_valued"

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

setup \<open>
let
  val Fun = Predicate_Compile_Aux.Fun
  val Input = Predicate_Compile_Aux.Input
  val Output = Predicate_Compile_Aux.Output
  val Bool = Predicate_Compile_Aux.Bool
  val oi = Fun (Output, Fun (Input, Bool))
  val ii = Fun (Input, Fun (Input, Bool))
  fun of_set compfuns \<^Type>\<open>fun T _\<close> =
    case body_type (Predicate_Compile_Aux.mk_monadT compfuns T) of
      \<^Type>\<open>Quickcheck_Exhaustive.three_valued _\<close> => 
        Const(\<^const_name>\<open>neg_cps_of_set\<close>, \<^Type>\<open>set T\<close> --> Predicate_Compile_Aux.mk_monadT compfuns T)
    | Type ("Predicate.pred", _) => Const(\<^const_name>\<open>pred_of_set\<close>, \<^Type>\<open>set T\<close> --> Predicate_Compile_Aux.mk_monadT compfuns T)
    | _ => Const(\<^const_name>\<open>pos_cps_of_set\<close>, \<^Type>\<open>set T\<close> --> Predicate_Compile_Aux.mk_monadT compfuns T)
  fun member compfuns (U as \<^Type>\<open>fun T _\<close>) =
    (absdummy T (absdummy \<^Type>\<open>set T\<close> (Predicate_Compile_Aux.mk_if compfuns
      \<^Const>\<open>Set.member T for \<open>Bound 1\<close> \<open>Bound 0\<close>\<close>)))
 
in
  Core_Data.force_modes_and_compilations \<^const_name>\<open>Set.member\<close>
    [(oi, (of_set, false)), (ii, (member, false))]
end
\<close>

subsection \<open>Derived equations for analz, parts and synth\<close>

lemma [code]:
  "analz H = (let
     H' = H \<union> (\<Union>((%m. case m of \<lbrace>X, Y\<rbrace> => {X, Y} | Crypt K X => if Key (invKey K) \<in> H then {X} else {} | _ => {}) ` H))
   in if H' = H then H else analz H')"
sorry

lemma [code]:
  "parts H = (let
     H' = H \<union> (\<Union>((%m. case m of \<lbrace>X, Y\<rbrace> => {X, Y} | Crypt K X => {X} | _ => {}) ` H))
   in if H' = H then H else parts H')"
sorry

definition synth' :: "msg set => msg => bool"
where
  "synth' H m = (m \<in> synth H)"

lemmas [code_pred_intro] = synth.intros[folded synth'_def]

code_pred [generator_cps] synth' unfolding synth'_def by (rule synth.cases) fastforce+

setup \<open>Predicate_Compile_Data.ignore_consts [\<^const_name>\<open>analz\<close>, \<^const_name>\<open>knows\<close>]\<close>
declare ListMem_iff[symmetric, code_pred_inline]
declare [[quickcheck_timing]]

setup Exhaustive_Generators.setup_exhaustive_datatype_interpretation
declare [[quickcheck_full_support = false]]

end
