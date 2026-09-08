theory SMT_Internals_Regressions
  imports HOL.SMT
begin

(* Test smtlib.ML *)
(* Purely syntactical testing! *)

ML\<open>
exception SMT_Regression of string

(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun expect_parsing_error str =
  str |> single |> Timeout.apply (seconds 5.0) SMTLIB.parse |> K (raise (SMT_Regression ("Input expected to raise parsing error but did not: " ^ str)))
  handle SMTLIB.PARSE(_,_) => true

(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun check_tree str tree expected_value =
let
  val tree' = [str] |> SMTLIB.parse |> @{print}
  val match = (expected_value = (tree = tree'))
val _ = (tree', tree) |> @{print}
in 
 case match of
  true => true |
  false => raise (SMT_Regression ("SMTLIB.parse does not give expected output for " ^ str ^ " instead resulted in " ^ SMTLIB.str_of tree'))
end

fun check_dec_to_rat dec expected =
  let
    fun str (i, j) = "(" ^ signed_string_of_int i ^ ", " ^ signed_string_of_int j ^ ")"
    val res = SMTLIB.convert_dec_to_rat dec
  in
    if res = expected then true
    else raise (SMT_Regression ("SMTLIB.convert_dec_to_rat " ^ str dec ^ " gives " ^ str res ^
      " instead of " ^ str expected))
  end


(*Regression Tests*)

val _ = expect_parsing_error "" 
val _ = check_tree "()" (SMTLIB.S []) true


(*Sym*)

val _ = check_tree "x" (SMTLIB.Sym "y") false
val _ = check_tree "x" (SMTLIB.Sym "x") true
val _ = check_tree "(x)" (SMTLIB.Sym "x") false
val _ = check_tree "|x|" (SMTLIB.Sym "x") true
val _ = check_tree "|<|" (SMTLIB.Sym "<") true
val _ = check_tree "@my+var<3" (SMTLIB.Sym "@my+var<3") true
val _ = check_tree "| my test|" (SMTLIB.Sym " my test") true
val _ = check_tree "||" (SMTLIB.Sym "") true

val _ = expect_parsing_error "|s||"


(*Int*)

val _ = check_tree "1" (SMTLIB.Num 1) true
val _ = check_tree "45" (SMTLIB.Num 54) false
val _ = check_tree "00078768" (SMTLIB.Num 78768) true
val _ = check_tree "00078768" (SMTLIB.Num 078768) true
val _ = check_tree "000" (SMTLIB.Num 0) true
val _ = check_tree "-23" (SMTLIB.Num (~23)) true
val _ = check_tree "-23" (SMTLIB.S[SMTLIB.Sym "-", SMTLIB.Num (~23)]) false


(*Dec*)

val _ = check_tree "1/2" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (1,0),SMTLIB.Dec (2,0)]) true
val _ = check_tree "01.234" (SMTLIB.Dec (1,234)) true
val _ = check_tree "01.234" (SMTLIB.Dec (01,234)) true
val _ = check_tree "01.234" (SMTLIB.Dec (201,234)) false
val _ = check_tree "47/28" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (47,0),SMTLIB.Dec (28,0)]) true
val _ = check_tree "-47/28" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.S[SMTLIB.Sym "-", SMTLIB.Dec (47,0)],SMTLIB.Dec (28,0)]) false
val _ = check_tree "-47/28" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (~47,0),SMTLIB.Dec (28,0)]) true
val _ = check_tree "(- 47/28)" (SMTLIB.S[SMTLIB.Sym "-", SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (47,0),SMTLIB.Dec (28,0)]]) true

val _ = expect_parsing_error "01.234.99"
val _ = expect_parsing_error "01."
val _ = expect_parsing_error "47/-28"
val _ = expect_parsing_error "3.2/5"

(*I guess these are allowed?*)
(*val _ = expect_parsing_error ".38"*)
(*val _ = expect_parsing_error "-." *)


(*convert_dec_to_rat*)

val _ = check_dec_to_rat (0, 0) (0, 1)
val _ = check_dec_to_rat (5, 0) (5, 1)
val _ = check_dec_to_rat (0, 5) (5, 10)
val _ = check_dec_to_rat (1, 5) (15, 10)
val _ = check_dec_to_rat (1, 234) (1234, 1000)
val _ = check_dec_to_rat (10, 25) (1025, 100)

(*Key*)

val _ = check_tree ":hi" (SMTLIB.Key "hi") true
val _ = check_tree ":pattern1" (SMTLIB.Key "hi") false
val _ = expect_parsing_error ": spacebeforepattern"


(*Str*)

val _ = check_tree "\"sdf\"" (SMTLIB.Str "sdf") true
val _ = check_tree "\"\"" (SMTLIB.Str "") true
val _ = check_tree "\" \"" (SMTLIB.Str "") false
val _ = check_tree "\"these should be replaced: \\\\\"" (SMTLIB.Str "these should be replaced: \\") true

val _ = expect_parsing_error "\"notclosed"
val _ = expect_parsing_error "notclosedopen\""


(*BVNum*)

val _ = check_tree "#b0" (SMTLIB.BVNum (0,1)) true
val _ = check_tree "#b00100000101" (SMTLIB.BVNum (261,11)) true


(*S*)
val _ = check_tree "()" (SMTLIB.S []) true
val _ = check_tree "( )" (SMTLIB.S []) true
val _ = check_tree "(op)" (SMTLIB.S [SMTLIB.Sym "op"]) true
val _ = check_tree "(op arg1 arg2)" (SMTLIB.S [SMTLIB.Sym "op",SMTLIB.Sym "arg1",SMTLIB.Sym "arg2"]) true
val _ = expect_parsing_error "(01"

(*forall*)
val _ = check_tree "(forall ((X Int)) (= X 12))"
 (SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S [SMTLIB.S [SMTLIB.Sym "X", SMTLIB.Sym "Int"]],
  SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym "X", SMTLIB.Num 12]]) true
val x = SMTLIB.parse ["(forall ((X Int)) (= (f X) 12))"]
\<close>

declare[[show_hyps]]
(* Test alethe_proof.ML *)
(* Purely syntactical testing! *)


ML\<open>
exception SMT_Regression of string
open SMTLIB
open Alethe_Proof

(*expects 
a SMTLIB.tree list, and a raw_alethe_node list, and a boolean indicating
if the SMTLIB.tree list should be parsed into a the raw_alethe_node or not.
The current_anchor_id is set to NONE and the name bindings to the empty name bindings
SMTLIB_Proof.empty_name_binding*)
fun expect_parsing_error trees =
   (Timeout.apply (seconds 5.0) parse_raw_proof_steps) NONE trees SMTLIB_Proof.empty_name_binding|> K (raise (SMT_Regression ("Input expected to raise parsing error but did not")))
  handle ALETHE_PROOF_PARSE _ => true |
   Fail _ => true


(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun check_raw_node trees raw_node expected_value =
let
  val node = Alethe_Proof.parse_raw_proof_steps NONE trees SMTLIB_Proof.empty_name_binding
  val match = (expected_value = ((fn (a,_,_) => a) node =  raw_node))
  (*val _ = @{print}("node",node)*)
in 
 case match of
  true => true |
  false => raise (SMT_Regression ("Alethe_Proof.parse_raw_proof_steps does not give expected output instead resulted in "))
end

(*expects a string and the numerator/denominator the argument should be extracted to.*)
fun check_coefficients str expected =
  let
    fun pair_str (i, j) = "(" ^ signed_string_of_int i ^ ", " ^ signed_string_of_int j ^ ")"
    val res = Alethe_Proof.extract_coefficients (SMTLIB.parse [str])
  in
    if res = expected then true
    else raise (SMT_Regression ("Alethe_Proof.extract_coefficients " ^ str ^ " gives " ^
      pair_str res ^ " instead of " ^ pair_str expected))
  end



(*Regression Tests*)

val missing_concl = SMTLIB.parse ["(step t0  :rule equiv_pos2)"]
val _ = expect_parsing_error [missing_concl]
val missing_id = SMTLIB.parse ["(step (+ 0 1) :rule equiv_pos2)"]
val _ = expect_parsing_error [missing_id]
val invalid_rule = SMTLIB.parse ["(step t0 (+ 0 1) :rule)"]
val _ = expect_parsing_error [invalid_rule]
val missing_rule_name = SMTLIB.parse ["(step t0 (+ 0 1) :rule)"]
val _ = expect_parsing_error [missing_rule_name]
val missing_rule = SMTLIB.parse ["(step t0 (+ 0 1))"]
val _ = expect_parsing_error [missing_rule]
val malformed_args = SMTLIB.parse ["(step t17 (cl) :rule hole :args 0)"]
val _ = expect_parsing_error [malformed_args]


(*steps*)

val testTree = SMTLIB.parse ["(step t99 (cl) :rule resolution)"]
val resTree = 
  Raw_Alethe_Node {concl = Sym "false", context_assignments = [], id = "t99", prems = [],
   rule = "resolution", step_args = [], subproof = [], prop_skeleton = Sym "true"}
val _ = check_raw_node [testTree] [resTree] true

(*Testing step arguments*)


(* No step argument given for argument optional rule *)
val testTree = SMTLIB.parse ["(step t17 (cl (+ @p_517 0)) :rule hole)"]
val resTree = Raw_Alethe_Node
  {concl = S [Sym "or", S [Sym "+", Sym "@p_517",Num 0]], context_assignments = [], id = "t17", 
  prems = [], rule = "hole", step_args = [], subproof = [], prop_skeleton = S [Sym "or", Sym "true"]}
val _ = check_raw_node [testTree] [resTree] true

(* Step argument given but not added *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule hole :args (0))"]
val resTree = Raw_Alethe_Node
  {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "hole",
   step_args = [], subproof = [], prop_skeleton = Sym "true"}
val _ = check_raw_node [testTree] [resTree] false

(* Step argument given and properly added *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule hole :args (0))"]
val resTree = Raw_Alethe_Node
 {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "hole", 
  step_args = [Num 0], subproof = [], prop_skeleton = Sym "true"}
val _ = check_raw_node [testTree] [resTree] true

(* Rule does not allow step argument and none given *)
val testTree = SMTLIB.parse ["(step t17 (cl (not (not (not a))) a) :rule not_not)"]
val resTree = Raw_Alethe_Node
  {concl =  S [Sym "or", S [Sym "not", S [Sym "not", S [Sym "not", Sym "a"]]], Sym "a"],
   context_assignments = [], id = "t17", prems = [], rule = "not_not", step_args = [], 
   subproof = [], prop_skeleton = S [Sym "or", Sym "true", Sym "true"]}
val _ = check_raw_node [testTree] [resTree] true

(* Unexpected step argument given TODO*)
val testTree = SMTLIB.parse ["(step t17 (cl (not (not (not a))) a) :rule not_not :args (0))"]
val _ = check_raw_node [testTree] [resTree] false
val resTree = Raw_Alethe_Node
  {concl =  S [Sym "or", S [Sym "not", S [Sym "not", S [Sym "not", Sym "a"]]], Sym "a"], 
   context_assignments = [], id = "t17", prems = [], rule = "not_not", step_args = [Num 0],
   subproof = [], prop_skeleton = S [Sym "or", Sym "true", Sym "true"]}
val x = check_raw_node [testTree] [resTree] true

(* Step argument is string *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule rare_rewrite :args (\"evaluate\"))"]
val resTree = Raw_Alethe_Node
  {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "rare_rewrite",
   step_args = [Str "evaluate"], subproof = [], prop_skeleton = Sym "true"}
val _ = check_raw_node [testTree] [resTree] true

(* Weird characters in symbol names*)
val testTree = SMTLIB.parse ["(step t17 (cl (exists ((main_~i~6 Int)) (and (<= c_main_~j~6 (+ (* 2 main_~i~6) 2)) (<= main_~i~6 4) (<= main_~i~6 c_main_~k~6)))) :rule rare_rewrite :args (\"evaluate\"))"]
val resTree = Raw_Alethe_Node
      {concl = S [Sym "or",
       S [Sym "exists", S [S [Sym "main_~i~6", Sym "Int"]],
          S [Sym "and", S [Sym "<=", Sym "c_main_~j~6", S [Sym "+", S [Sym "*", Num 2, Sym "main_~i~6"], Num 2]], S [Sym "<=", Sym "main_~i~6", Num 4],
             S [Sym "<=", Sym "main_~i~6", Sym "c_main_~k~6"]]]]
  , context_assignments = [], id = "t17", prems = [], rule = "rare_rewrite", 
  step_args = [Str "evaluate"], subproof = [], prop_skeleton = S [Sym "or", Sym "true"]}
val _ = check_raw_node [testTree] [resTree] true


val testNode = Alethe_Proof.parse_raw_proof_steps NONE [testTree] SMTLIB_Proof.empty_name_binding


(*extract_coefficients*)

val _ = check_coefficients "5" (5, 1)
val _ = check_coefficients "(- 5)" (~5, 1)
val _ = check_coefficients "(/ 1 2)" (1, 2)
val _ = check_coefficients "0.0" (0, 1)
val _ = check_coefficients "5.0" (5, 1)
val _ = check_coefficients "0.5" (5, 10)
val _ = check_coefficients "1.5" (15, 10)
val _ = check_coefficients "10.25" (1025, 100)
val _ = check_coefficients "(- 5.0)" (~5, 1)
val _ = check_coefficients "(- 1.5)" (~15, 10)
val _ = check_coefficients "(- 0.5)" (~5, 10)
val _ = check_coefficients "1/1" (1, 1)
val _ = check_coefficients "47/28" (47, 28)
val _ = check_coefficients "-47/28" (~47, 28)
val _ = check_coefficients "(- 47/28)" (~47, 28)


\<close>


(* Test alethe_replay_methods.ML *)
(* Important: The context can be different than if a step appears inside a proof! E.g., because
of subproofs. Any failure should be double checked carefully. Nonetheless, these regressions are useful
when changes are made to the reconstruction functions. 
Currently only supports indexes as args ^^ This is because the reconstruction of these rules had
some errors.
*)

ML\<open>
datatype token = None | Unfinished of string list * int | Finished of string list * string list
exception TOKEN of string

fun parse_token s [] = s |
  parse_token None ("("::cs) = parse_token (Unfinished(["("],1)) cs |
  parse_token None (" "::cs) = parse_token None cs |
  parse_token None (")"::cs) = Scan.fail cs |
  parse_token None cs = Finished (Scan.catch Scan.many (fn c => c <> " " andalso c <> ")") cs) |
  parse_token (Unfinished (s,i)) ("("::cs) = parse_token (Unfinished ("("::s,i+1)) cs |
  parse_token (Unfinished (_,0)) (")"::_) = raise TOKEN("too many closing parenthesis") |
  parse_token (Unfinished (s,1)) (")"::xs) = Finished(rev (")"::s),xs) |
  parse_token (Unfinished (s,i)) (")"::cs) = parse_token (Unfinished (")"::s,i-1)) cs |
  parse_token (Unfinished (s,i)) (c::cs) = parse_token (Unfinished (c::s,i)) cs |
  parse_token _ _ = raise TOKEN("error parsing token")

fun call_parse_token cs = parse_token (Unfinished ([],0)) cs |> (fn Finished(x,xs) => (x |> implode ,xs))

val scanWhiteSpace = Scan.many (curry (op =) " ")

fun tactic_args_parser ctxt cs =
   ((Scan.this_string "Declarations" |-- $$" " |-- scanWhiteSpace |-- $$"[" |-- scanWhiteSpace
     |-- Scan.repeat (call_parse_token --| scanWhiteSpace --| $$"," --| scanWhiteSpace)
     -- call_parse_token
     --| scanWhiteSpace --| $$"]"
   ) cs 
  |> fst
  |> (fn (xs,x) => x::xs) 
  |> map (Syntax.parse_term ctxt))




fun get_tac n ctxt prems args = 
let
  val ctxt =
    ctxt |> put_simpset (SMT_Replay.make_simpset ctxt [])
  val rule = CVC5_Replay_Methods.cvc5_rule_of n |> @{print}
  val rule_name = rule |> Alethe_Replay_Methods.string_of_alethe_rule
  val _ = @{print}("Found tactic", rule_name)
  val _ = @{print}("args", args  )

  (*FIXME: For some reason this function gets called twice... This definitely should not be necessary*)
  val dummys = Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ (Const ("Pure.term", @{typ "prop \<Rightarrow> prop"}) $ Const ("Pure.dummy_pattern", @{typ "prop"}))

  val prems=prems
  val step_args=[]
  val context_args=[]
  (*arguments are only supported for some rules and are a little brittle*)
  (*maybe I should have parsed tokens, at the time I wrote this I only wanted to test one specific rule*)
  val args= (if member (op =) ["and_pos", "or_neg", "Not_Or", "and"] rule_name andalso Option.isSome args
            then SOME (Index (Option.valOf args |> Syntax.read_term ctxt |> HOLogic.dest_number |> snd))
            else if rule_name = "shuffle" andalso Option.isSome args
            then SOME (CommOp (Option.valOf args |> Syntax.read_term ctxt))
            else if rule_name = "la_generic" andalso Option.isSome args
            (*There has to be an int parser from a string out there...*)
            then 

let
val keyword_list = Keyword.empty_keywords |> Keyword.add_major_keywords [")","("]
 |> Keyword.add_major_keywords ["[","]"] |> Keyword.add_major_keywords [","]

(*TODO: there should be an optional in this for the last comma and can be made far nicer, had to get this working quick*)
val x = (Option.valOf args |> Token.explode keyword_list Position.none
        |> Parse.command_name "["  
        |-- 
 Scan.repeat (Parse.command_name "(" |-- Parse.int --| Parse.command_name "," -- Parse.int --| Parse.command_name ")"
 --| ( Parse.command_name ","))
--  (Parse.command_name "(" |-- Parse.int --| Parse.command_name "," -- Parse.int --| Parse.command_name ")")
 --| ( Parse.command_name "]")
) |> fst |> (fn (ys,z) => ys @ [z])

in 
SOME (Farkas_Coefficients x)
end
            else NONE)|> @{print}
  fun rule_tac ctxt t = CVC5_Replay_Methods.choose (Context.the_generic_context ()) rule ctxt prems step_args context_args t args
  fun term_to_thm t = rule_tac ctxt t

in
  (fn t => 
  if (t |> Thm.concl_of) = dummys
  then Seq.empty
  else
    let
      val thm2 = t |> Thm.concl_of |> (fn Const (_, _) $ x => x | x => x) |> term_to_thm 
    in
      resolve0_tac [thm2] 1 t
    end)
end

val parse_tactic_args : tactic_args parser = (fn ts => let val _ = @{print}("ts",ts) in (Index 0,ts) end)
fun test x = Parse.term (x|> @{print})
val _ =
 Theory.setup
 (Method.setup \<^binding>\<open>ctxt_tactic\<close>
 (Scan.lift (Parse.string
             -- ( (Scan.optional (Scan.option Parse.string) NONE))) >>
   (fn (rule_name,args) => fn ctxt => fn prems => CONTEXT_TACTIC (get_tac rule_name ctxt prems args)))
 "testing tactics <name> ([<step_args>*]) ([<args>*])")
\<close>


(* Rule 1: assume *)

lemma normalized_input_1:
  assumes "a"
  shows "a"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma normalized_input_2:
  assumes "a \<and> (b \<or> c)"
  shows "a \<and> (b \<or> c)"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma normalized_input_3:
  assumes "a \<and> a"
  shows "a \<and> a"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma normalized_input_4:
  assumes "(\<forall>a. a = (3::int))"
  shows "(\<forall>a. a = (3::int))"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma local_input_1:
  assumes "(\<forall>a. a = (3::int))"
  shows "(\<forall>a. a = (3::int))"
  using assms
  by (ctxt_tactic "__local_input")

lemma local_input_2:
  assumes "a \<and> (b \<or> c)"
  shows "a \<and> (b \<or> c)"
  using assms
  by (ctxt_tactic "__local_input")

lemma local_input_3:
  assumes "a \<and> a"
  shows "a \<and> a"
  using assms
  by (ctxt_tactic "__local_input")

lemma local_input_4:
  assumes "(\<forall>a. a = (3::int))"
  shows "(\<forall>a. a = (3::int))"
  using assms
  by (ctxt_tactic "__local_input")

(* Rule 2: hole *)

(* No checking necessary*)

(* Rule 3: true*)

lemma true_1: "True"
  by (ctxt_tactic "true")

(* Rule 4: false*)

lemma false_1: "\<not>False"
  by (ctxt_tactic "false_rule")

(* Rule 5: not_not*)

lemma not_not_1: "\<not>\<not>\<not>a \<or> a"
  by (ctxt_tactic "not_not")

lemma not_not_2: "\<not>\<not>\<not>\<not>a \<or> \<not>a"
  by (ctxt_tactic "not_not")

lemma not_not_3: "\<not>\<not>\<not>(\<not>a \<or> b) \<or> (\<not>a \<or> b)"
  by (ctxt_tactic "not_not")

(* Rule 6 & 7: resolution and th_resolution*)

lemma resolution_1:
  assumes "a" "\<not>a"
  shows "False"
  using assms
  by (ctxt_tactic "resolution")

lemma resolution_2:
  assumes "a \<or> b" "\<not>a"
  shows "b"
  using assms
  by (ctxt_tactic "resolution")

lemma resolution_3:
  assumes "a \<or> b" "\<not>a \<or> c"
  shows "b \<or> c"
  using assms
  by (ctxt_tactic "resolution")


lemma
  assumes \<open>\<not> t1 \<or>
    \<not> t2 \<or>
    \<not> t3 \<or>
    \<not> t4 \<or> \<not> t5 \<or> \<not> t6 \<or> \<not> t7 \<or> \<not> t8 \<or> \<not> t9 \<or> \<not> t10 \<or> \<not> t11 \<or> \<not> t12 \<or> \<not> t13 \<or> \<not> t14 \<or> \<not> t15 \<or>
     \<not> t16 \<or> \<not> t17 \<or> \<not> t18 \<or> \<not> t19 \<or> \<not> t20 \<or> \<not> t21 \<or> \<not> t22 \<or> \<not> t23 \<or> \<not> t24 \<or> \<not> t25 \<or> t26\<close>
    \<open>\<not> t27 \<or> t1\<close>
    \<open>\<not> t27 \<or> t2\<close>
    \<open>\<not> t27 \<or> t3\<close>
    \<open>\<not> t27 \<or> t4\<close>
    \<open>\<not> t27 \<or> t5\<close>
    \<open>\<not> t27 \<or> t6\<close>
    \<open>\<not> t27 \<or> t7\<close>
    \<open>\<not> t27 \<or> t8\<close>
    \<open>\<not> t27 \<or> t9\<close>
    \<open>\<not> t27 \<or> t10\<close>
    \<open>\<not> t27 \<or> t11\<close>
    \<open>\<not> t27 \<or> t12\<close>
    \<open>\<not> t27 \<or> t13\<close>
    \<open>\<not> t27 \<or> t14\<close>
    \<open>\<not> t27 \<or> t15\<close>
    \<open>\<not> t27 \<or> t16\<close>
    \<open>\<not> t27 \<or> t17\<close>
    \<open>\<not> t27 \<or> t18\<close>
    \<open>\<not> t27 \<or> t19\<close>
    \<open>\<not> t27 \<or> t20\<close>
    \<open>\<not> t27 \<or> t21\<close>
    \<open>\<not> t27 \<or> t22\<close>
    \<open>\<not> t27 \<or> t23\<close>
    \<open>\<not> t27 \<or> t24\<close>
    \<open>\<not> t27 \<or> t25\<close>
  shows \<open>t26 \<or>
    \<not> t27 \<or>
    \<not> t27 \<or>
    \<not> t27 \<or>
    \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27 \<or> \<not> t27\<close>
  using assms
  by (ctxt_tactic "resolution")

(* Rule 8: tautology *)

lemma tautology_1:
  assumes "a \<or> b \<or> \<not>a \<or> c"
  shows "True"
  using assms
  by (ctxt_tactic "tautology")

(* Rule 9: contraction *)

lemma contraction_1:
  assumes "a \<or> b"
  shows "a \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_2:
  assumes "a \<or> a"
  shows "a"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_3:
  assumes "a \<or> b \<or> a \<or> c"
  shows "a \<or> b \<or> c"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_4:
  assumes "a \<or> b \<or> a \<or> b"
  shows "a \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_5:
  assumes "a \<or> (b \<longrightarrow> c) \<or> (b \<longrightarrow> c) \<or> b"
  shows "a \<or> (b \<longrightarrow> c) \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_6:
  assumes "a \<or> (b \<or> c) \<or> (b \<or> c) \<or> b"
  shows "a \<or> (b \<or> c) \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_7:
  assumes "(b \<or> c) \<or> a \<or> (b \<or> c)"
  shows "a \<or> (b \<or> c)"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_8:
  assumes "((\<not> y3 \<or> \<not> y689) \<or> \<not> \<not> y689) \<or> (\<not> y3 \<or> \<not> y689) \<or> \<not> \<not> y689"
  shows "(\<not> y3 \<or> \<not> y689) \<or> \<not> \<not> y689"
  using assms
  by (ctxt_tactic "contraction")

context
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
begin
(*cvc5 sometimes produces extremely large goals (6000 lines of Isabelle terms if you print
it as a lemma), so here is an ML version to be able to measure time.*)
ML \<open>
let
  fun build_term n = 
    if n = 0 then @{term \<open>P 0\<close>}
    else HOLogic.mk_disj (@{term \<open>P\<close>} $ HOLogic.mk_nat (n),  build_term (n-1))
  fun build_term2 n = 
    if n = 0 then @{term \<open>P 0\<close>}
    else HOLogic.mk_disj (build_term2 (n-1), 
       HOLogic.mk_disj (@{term \<open>P\<close>} $ HOLogic.mk_nat (n), build_term (n-1)))
  val ctxt = @{context}
  fun measure_time ctxt n =
    let
    val ct = (Thm.cterm_of ctxt) (build_term2 n) |> HOLogic.mk_judgment
    val (prems, ctxt') = Assumption.add_assumes [ct] ctxt
    val start = Timing.start ()
    val thm = Alethe_Replay_Methods.contraction ctxt' prems (@{term Trueprop} $ build_term n)
    val total = Time.toMilliseconds (#elapsed (Timing.result start))
    in
     (thm, total)
    end
in
   map (measure_time ctxt) [10,20,30,50,60]
end
\<close>
end

(* Rule 11: la_generic *)

declare[[smt_debug_arith_verit]]
declare[[show_types=false,show_hyps=false]]
declare[[ML_print_depth=1000]]

lemma la_generic_1:
"
\<not> - 1 * ((x8::int) + - 1 * y8 + x1 + - 1 * y1) \<le> - 1 * 1 \<or>
\<not> x8 + - 1 * y8 + - 1 * x2 + y2 + x1 + - 1 * y1 + - 1 * x0 + y0 \<le> 0 \<or>
\<not> x2 + - 1 * y2 + x0 + - 1 * y0 < 1 \<or>
- 1 * (x8 + - 1 * y8 + x1 + - 1 * y1) + 
  (x8 + - 1 * y8 + - 1 * x2 + y2 + x1 + - 1 * y1 + - 1 * x0 + y0) +
  (x2 + - 1 * y2 + x0 + - 1 * y0)
  < - 1 * 1 + 0 + 1 "
  by (ctxt_tactic "la_generic" "[(1,1),(1,1),(1,1),(1,1)]")


lemma la_generic_2:
  fixes x8::int
  shows 
"
\<not> - x1 + y1 - x8 + y8 \<le> - 1 \<or>
\<not>   x1 - y1 + x8 - y8 - x0 + y0 - x2 + y2 \<le> 0 \<or>
\<not>                       x0 - y0 + x2 - y2 < 1 \<or>
0 < 0 "
  by (ctxt_tactic "la_generic" "[(1,1),(1,1),(1,1),(1,1)]")

(* The original problem had t1,t2 :: real, but int also had the same issue *)
lemma la_generic_3:
  fixes t1::int and t2::int
  shows "(t1 \<noteq> -1) \<or> (t2 \<noteq> (-t2)) \<or> ((-t2) \<noteq> (-t1))"
  by (ctxt_tactic "la_generic" "[(-2,1),(1,1),(2,1)]")

(* Rule 12: lia_generic *)

lemma lia_generic_1:
  shows "\<not>(3*(x::int) = 9) \<or> (x \<ge> 3)"
  by (ctxt_tactic "lia_generic")

(* Rule 13: la_disequality *)

lemma la_disequality_1: "(a::int) = b \<or> \<not> (a::int) \<le> b \<or> \<not> b \<le> (a::int)"
  by (ctxt_tactic "la_disequality")

lemma la_disequality_2: "(1::int) = (5-4) \<or> \<not> (1::int) \<le> (5-4) \<or> \<not> (5-4) \<le> (1::int)"
  by (ctxt_tactic "la_disequality")

lemma la_disequality_3: "(2::int) = (7-2) \<or> \<not> (2::int) \<le> (7-2) \<or> \<not> (7-2) \<le> (2::int)"
  by (ctxt_tactic "la_disequality")

lemma la_disequality_4: "(2::int) = (7-6) \<or> \<not> (2::int) \<le> (7-6) \<or> \<not> (7-6) \<le> (2::int)"
  by (ctxt_tactic "la_disequality")


(* Rule 14: la_totality *)

lemma la_totality_1: "(a::int) \<le> b \<or> b \<le> a"
  by (ctxt_tactic "la_totality")

lemma la_totality_2: "((2::int) - 6) \<le> (3 + 4) \<or> (3 + 4)  \<le> ((2::int) - 6)"
  by (ctxt_tactic "la_totality")


(* Rule 15: la_tautology *)

lemma la_tautology_form1_1: "\<not>((1::int) = 2)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_2: "((2::int) < 5)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_3: "((14::int) \<ge> 6)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_4: "((14::int) \<ge> (6-3+1))"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_5: "\<not>((-14::int) \<ge> -(6-3+1))"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_1: "((a::int) \<le> 11) \<or> \<not>(a \<le> 11)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_2: "(a::int) \<le> 11 \<or> \<not>(a \<le> (66 - 55))"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_3: "\<not>(((5::int) + 4) \<le> 11) \<or> \<not>(((5::int) + 4) \<ge> 11)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_4: "\<not>(((5::int) + 4) \<le> 11) \<or> \<not>(((5::int) + 4) \<ge> 25)"
  by (ctxt_tactic "la_tautology")


(* Rule 16: la_mult_pos*)

lemma la_mult_pos_1: "(0::int) < 3 \<and> (A::int) < 0 \<longrightarrow> 3 * A < 3 * 0 "
  by (ctxt_tactic "la_mult_pos")

lemma la_mult_pos_2: "(0::int) < 3 \<and> (-3::int) < 0 \<longrightarrow> (3::int) * (-3) < 3 * 0"
  by (ctxt_tactic "la_mult_pos")

lemma la_mult_pos_3: "(0::int) < 5 \<and> \<not>((-3::int) = -77) \<longrightarrow> \<not>((5::int) * (-3) = 5 * -77)"
  by (ctxt_tactic "la_mult_pos")


(* Rule 23: trans *)                              

lemma trans_1:
  assumes "a = a"
  shows  "a = a"
  using assms
  by (ctxt_tactic "trans")

lemma trans_2:
  assumes "a = a" "a = b"
  shows  "a = b"
  using assms
  by (ctxt_tactic "trans")

lemma trans_3:
  assumes "(a = f a)" "(f a = b)"
  shows  "a = b"
  using assms
  by (ctxt_tactic "trans")

lemma trans_4:
  assumes "(a = f a)" "(f a = b)" "(b = a)"
  shows  "a = a"
  using assms
  by (ctxt_tactic "trans")

lemma trans_5:
assumes "f a b = f a (g b)"
        "f a (g b) = f a b"
        "f a b = True"
shows   "f a b = True"
  using assms
  by (ctxt_tactic "trans")

(* Rule 24: cong *)

lemma cong_1: 
  assumes "(a = a)"
  shows "(a = a)"
  using assms
  by (ctxt_tactic "eq_congruent")

lemma cong_2:
  assumes "(a = a)" and "(a = b)"
  shows "(f a a) = (f a b)"
  using assms
  by (ctxt_tactic "cong")

lemma cong_3:
  assumes "(3 = 2 + (1::int))" and "(c = g b)"
  shows "((3 + c) = ((2 + (1::int)) + g b))"
  using assms
  by (ctxt_tactic "cong")

lemma cong_4:
  assumes "x = False"
  shows "alethe_id (\<lambda>a b. a = b) x = alethe_id (\<lambda>a b. a = b) False"
  using assms
  by (ctxt_tactic "cong")

lemma cong_5:
  assumes "alethe_id (\<lambda>a. f a x) = alethe_id (\<lambda>a. f a y)" and "s = t"
  shows "alethe_id (\<lambda>a. f a x) s = alethe_id (\<lambda>a. f a y) t"
  using assms
  by (ctxt_tactic "cong")

(* Rule 25: eq_reflexive *)

lemma eq_reflexive_1: "a = a"
  by (ctxt_tactic "eq_reflexive")

lemma eq_reflexive_2: "3 = (3::int)"
  by (ctxt_tactic "eq_reflexive")

lemma eq_reflexive_3: "(a = b) = (a = b)"
  by (ctxt_tactic "eq_reflexive")

(* Rule 26: eq_transitive *)

lemma eq_transitive_1: "\<not> (a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_transitive")

lemma eq_transitive_2: "\<not> (a = a) \<or> \<not>(a = b) \<or> (a = b)"
  by (ctxt_tactic "eq_transitive")

lemma eq_transitive_3: "\<not> (a = f a) \<or> \<not>(f a = b) \<or> (a = b)"
  by (ctxt_tactic "eq_transitive")

lemma eq_transitive_4: "\<not> (a = f a) \<or> \<not>(f a = b) \<or> \<not>(f a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_transitive")

(* Rule 27: eq_congruent *)

lemma eq_congruent_1: "\<not> (a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_congruent")

lemma eq_congruent_2: "\<not> (a = a) \<or> \<not>(a = b) \<or> (f a a = f a b)"
  by (ctxt_tactic "eq_congruent")

lemma eq_congruent_3: "\<not> (3 = 2 + (1::int)) \<or> \<not>(c = g b) \<or> ((3 + c) = ((2 + (1::int)) + g b))"
  by (ctxt_tactic "eq_congruent")

lemma eq_congruent_5:
  shows "\<not>(3 = 2 + (1::int)) \<or> \<not>c = g b \<or> ((3 + c) = ((2 + (1::int)) + g b))"
  by (ctxt_tactic "eq_congruent")


(* Rule 28: eq_congruent_pred *)

lemma eq_congruent_pred_1: "\<not> (a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_congruent_pred")

lemma eq_congruent_pred_2: "\<not> (a = a) \<or> \<not>(a = b) \<or> (P a a = P a b)"
  by (ctxt_tactic "eq_congruent_pred")

(* Rule 29: qnt_cnf *)

lemma qnt_cnf_1: "\<not> (\<forall>x1::'a. \<not>((x1 = 1) \<or> (x1 = 2))) \<or> (\<forall>x1::'a::{numeral}. (\<not>(x1 = 1) \<and> \<not>(x1 = 2)))"
 by (ctxt_tactic "qnt_cnf")

lemma qnt_cnf_2: \<open>\<not> (\<forall>veriT_vr1::'a. \<not> (P::bool \<Rightarrow> 'a \<Rightarrow> bool) False veriT_vr1 \<and> P True veriT_vr1) \<or>
         (\<forall>veriT_vr1::'a. P True veriT_vr1) \<close>
 by (ctxt_tactic "qnt_cnf")

lemma qnt_cnf_3:
  fixes trans
  shows
        "\<not> (\<forall>(veriT_vr756::int) veriT_vr757 veriT_vr758 (veriT_vr759::int) (veriT_vr760::int) veriT_vr761 veriT_vr762.
                (fun_app (t veriT_vr756 veriT_vr757 veriT_vr758) (trans veriT_vr759 veriT_vr760 veriT_vr761 veriT_vr762) \<longrightarrow>
                 (\<exists>veriT_vr763.
                     membera veriT_vr763 veriT_vr756 \<and>
                     membera veriT_vr763 (seta (userIDs veriT_vr762)) \<and>
                     memberb veriT_vr757 (setb (fun_appv (outerPostIDs veriT_vr762) veriT_vr758)) \<and>
                     (veriT_vr763 = admin veriT_vr762 \<or>
                      memberh (pairb veriT_vr758 (fun_appn (fun_appz (outerOwner veriT_vr762) veriT_vr758) veriT_vr757)) (setf (fun_appaa (recvOuterFriendIDs veriT_vr762) veriT_vr763)) \<or>
                      vsb
                       (literal False False False False True True True
                         (literal True False True False True True True
                           (literal False True False False False True True
                             (literal False False True True False True True (literal True False False True False True True (literal True True False False False True True zero)))))) =
                      fun_appl (fun_appy (outerVis veriT_vr762) veriT_vr758) veriT_vr757))) \<and>
                (\<not> (\<forall>veriT_vr764.
                        \<not> (membera veriT_vr764 veriT_vr756 \<and>
                            membera veriT_vr764 (seta (userIDs veriT_vr762)) \<and>
                            memberb veriT_vr757 (setb (fun_appv (outerPostIDs veriT_vr762) veriT_vr758)) \<and>
                            (admin veriT_vr762 = veriT_vr764 \<or>
                             memberh (pairb veriT_vr758 (fun_appn (fun_appz (outerOwner veriT_vr762) veriT_vr758) veriT_vr757)) (setf (fun_appaa (recvOuterFriendIDs veriT_vr762) veriT_vr764)) \<or>
                             vsb
                              (literal False False False False True True True
                                (literal True False True False True True True
                                  (literal False True False False False True True
                                    (literal False False True True False True True (literal True False False True False True True (literal True True False False False True True zero)))))) =
                             fun_appl (fun_appy (outerVis veriT_vr762) veriT_vr758) veriT_vr757))) \<longrightarrow>
                 fun_app (t veriT_vr756 veriT_vr757 veriT_vr758) (trans veriT_vr759 veriT_vr760 veriT_vr761 veriT_vr762))) \<or>
         (\<forall>veriT_vr756 veriT_vr757 veriT_vr758 veriT_vr759 (veriT_vr760::int) veriT_vr761 veriT_vr762 veriT_vr764.
             \<not> membera veriT_vr764 veriT_vr756 \<or>
             \<not> membera veriT_vr764 (seta (userIDs veriT_vr762)) \<or>
             \<not> memberb veriT_vr757 (setb (fun_appv (outerPostIDs veriT_vr762) veriT_vr758)) \<or>
             vsb
              (literal False False False False True True True
                (literal True False True False True True True
                  (literal False True False False False True True
                    (literal False False True True False True True (literal True False False True False True True (literal True True False False False True True zero)))))) \<noteq>
             fun_appl (fun_appy (outerVis veriT_vr762) veriT_vr758) veriT_vr757 \<or>
             fun_app (t veriT_vr756 veriT_vr757 veriT_vr758) (trans veriT_vr759 veriT_vr760 veriT_vr761 veriT_vr762))
"
  by (ctxt_tactic "qnt_cnf")

lemma qnt_cnf_4: \<open> \<not> (\<forall>(veriT_vr13::'a_topoly::type) veriT_vr14::'a::type option set.
                ((Alexandroff_open::'a_topoly::type \<Rightarrow> 'a::type option set \<Rightarrow> bool) veriT_vr13 veriT_vr14 \<longrightarrow>
                 (\<exists>veriT_vr15::'a::type set.
                     veriT_vr14 = Some ` veriT_vr15 \<and> (openin::'a_topoly::type \<Rightarrow> 'a::type set \<Rightarrow> bool) veriT_vr13 veriT_vr15 \<or>
                     veriT_vr14 = insert None (Some ` ((topspace::'a_topoly::type \<Rightarrow> 'a::type set) veriT_vr13 - veriT_vr15)) \<and>
                     (compactin::'a_topoly::type \<Rightarrow> 'a::type set \<Rightarrow> bool) veriT_vr13 veriT_vr15 \<and> (closedin::'a_topoly::type \<Rightarrow> 'a::type set \<Rightarrow> bool) veriT_vr13 veriT_vr15)) \<and>
                (\<not> (\<forall>veriT_vr16::'a::type set.
                        \<not> (veriT_vr14 = Some ` veriT_vr16 \<and> openin veriT_vr13 veriT_vr16 \<or>
                            veriT_vr14 = insert None (Some ` (topspace veriT_vr13 - veriT_vr16)) \<and> compactin veriT_vr13 veriT_vr16 \<and> closedin veriT_vr13 veriT_vr16)) \<longrightarrow>
                 Alexandroff_open veriT_vr13 veriT_vr14)) \<or>
         (\<forall>(veriT_vr13::'a_topoly::type) (veriT_vr14::'a::type option set) veriT_vr16::'a::type set.
             veriT_vr14 \<noteq> insert None (Some ` (topspace veriT_vr13 - veriT_vr16)) \<or>
             \<not> compactin veriT_vr13 veriT_vr16 \<or> \<not> closedin veriT_vr13 veriT_vr16 \<or> Alexandroff_open veriT_vr13 veriT_vr14) \<close>
  by (ctxt_tactic "qnt_cnf")

lemma qnt_cnf_5:
  fixes ACIDZ (infix \<open>~\<close> 64)
  shows
  \<open>\<not> (\<forall>(veriT_vr58::'a_rexp) veriT_vr59::'a_rexp.
        (veriT_vr58 ~ veriT_vr59 \<longrightarrow>
                 (\<exists>(veriT_vr60::'a_rexp) (veriT_vr61::'a_rexp) veriT_vr62::'a_rexp.
                     veriT_vr58 = Alt (Alt veriT_vr60 veriT_vr61) veriT_vr62 \<and> veriT_vr59 = Alt veriT_vr60 (Alt veriT_vr61 veriT_vr62)) \<or>
                 (\<exists>(veriT_vr63::'a_rexp) (veriT_vr64::'a_rexp) veriT_vr65::'a_rexp.
                     veriT_vr58 = Alt veriT_vr63 (Alt veriT_vr64 veriT_vr65) \<and> veriT_vr59 = Alt (Alt veriT_vr63 veriT_vr64) veriT_vr65) \<or>
                 (\<exists>(veriT_vr66::'a_rexp) veriT_vr67::'a_rexp. veriT_vr58 = Alt veriT_vr66 veriT_vr67 \<and> veriT_vr59 = Alt veriT_vr67 veriT_vr66) \<or>
                 veriT_vr59 = Alt veriT_vr58 veriT_vr58 \<or>
                 (\<exists>veriT_vr68::'a_rexp. veriT_vr59 = elim_zeros veriT_vr68 \<and> veriT_vr58 ~ veriT_vr68) \<or>
                 (\<exists>(veriT_vr69::'a_rexp) veriT_vr70::'a_rexp. veriT_vr58 = Conc veriT_vr69 veriT_vr70 \<and> veriT_vr59 = distribute veriT_vr70 veriT_vr69) \<or>
                 veriT_vr58 = veriT_vr59 \<or>
                 (\<exists>(veriT_vr71::'a_rexp) (veriT_vr72::'a_rexp) (veriT_vr73::'a_rexp) veriT_vr74::'a_rexp.
                     veriT_vr58 = Alt veriT_vr71 veriT_vr73 \<and> veriT_vr59 = Alt veriT_vr72 veriT_vr74 \<and> veriT_vr71 ~ veriT_vr72 \<and> veriT_vr73 ~ veriT_vr74) \<or>
                 (\<exists>(veriT_vr75::'a_rexp) (veriT_vr76::'a_rexp) veriT_vr77::'a_rexp.
                     veriT_vr58 = Conc veriT_vr75 veriT_vr77 \<and> veriT_vr59 = Conc veriT_vr76 veriT_vr77 \<and> veriT_vr75 ~ veriT_vr76)) \<and>
        (\<not> (\<forall>(veriT_vr78::'a_rexp) (veriT_vr79::'a_rexp) veriT_vr80::'a_rexp.
                        \<not> (veriT_vr58 = Alt (Alt veriT_vr78 veriT_vr79) veriT_vr80 \<and> veriT_vr59 = Alt veriT_vr78 (Alt veriT_vr79 veriT_vr80))) \<or>
                 \<not> (\<forall>(veriT_vr81::'a_rexp) (veriT_vr82::'a_rexp) veriT_vr83::'a_rexp.
                        \<not> (veriT_vr58 = Alt veriT_vr81 (Alt veriT_vr82 veriT_vr83) \<and> veriT_vr59 = Alt (Alt veriT_vr81 veriT_vr82) veriT_vr83)) \<or>
                 \<not> (\<forall>(veriT_vr84::'a_rexp) veriT_vr85::'a_rexp. \<not> (veriT_vr58 = Alt veriT_vr84 veriT_vr85 \<and> veriT_vr59 = Alt veriT_vr85 veriT_vr84)) \<or>
                 veriT_vr59 = Alt veriT_vr58 veriT_vr58 \<or>
                 \<not> (\<forall>veriT_vr86::'a_rexp. \<not> (veriT_vr59 = elim_zeros veriT_vr86 \<and> veriT_vr58 ~ veriT_vr86)) \<or>
                 \<not> (\<forall>(veriT_vr87::'a_rexp) veriT_vr88::'a_rexp. \<not> (veriT_vr58 = Conc veriT_vr87 veriT_vr88 \<and> veriT_vr59 = distribute veriT_vr88 veriT_vr87)) \<or>
                 veriT_vr58 = veriT_vr59 \<or>
                 \<not> (\<forall>(veriT_vr89::'a_rexp) (veriT_vr90::'a_rexp) (veriT_vr91::'a_rexp) veriT_vr92::'a_rexp.
                        \<not> (veriT_vr58 = Alt veriT_vr89 veriT_vr91 \<and> veriT_vr59 = Alt veriT_vr90 veriT_vr92 \<and> veriT_vr89 ~ veriT_vr90 \<and> veriT_vr91 ~ veriT_vr92)) \<or>
                 \<not> (\<forall>(veriT_vr93::'a_rexp) (veriT_vr94::'a_rexp) veriT_vr95::'a_rexp.
                        \<not> (veriT_vr58 = Conc veriT_vr93 veriT_vr95 \<and> veriT_vr59 = Conc veriT_vr94 veriT_vr95 \<and> veriT_vr93 ~ veriT_vr94)) \<longrightarrow>
                 veriT_vr58 ~ veriT_vr59)) \<or>
    (\<forall>(veriT_vr58::'a_rexp) veriT_vr59::'a_rexp. veriT_vr58 \<noteq> veriT_vr59 \<or> veriT_vr58 ~ veriT_vr59)\<close>
  supply [[show_types]]
  by (ctxt_tactic "qnt_cnf")

lemma
  fixes scaleR :: "'real \<Rightarrow> 'a :: {comm_monoid_add,inverse,times,zero,ord} \<Rightarrow> 'a" (infixr \<open>*\<^sub>R\<close> 75)
  shows \<open>\<not> (\<forall>veriT_vr37.
                veriT_vr37 \<in> space M \<longrightarrow>
                (\<Sum>uua\<in>f ` space M. indicat_real (f -` {uua} \<inter> space M) veriT_vr37 *\<^sub>R uua) = f veriT_vr37) \<or>
         (\<forall>veriT_vr37.
             veriT_vr37 \<notin> space M \<or>
             (\<Sum>uua\<in>f ` space M. indicat_real (f -` {uua} \<inter> space M) veriT_vr37 *\<^sub>R uua) = f veriT_vr37) \<close>
  by (ctxt_tactic "qnt_cnf")

lemma \<open>\<not> (\<forall>veriT_vr7 veriT_vr8 veriT_vr9 :: 'a.
                (veriT_vr7 / veriT_vr8 < veriT_vr9) =
                (if 0 < veriT_vr8 then veriT_vr7 < veriT_vr9 * veriT_vr8
                 else if veriT_vr8 < 0 then veriT_vr9 * veriT_vr8 < veriT_vr7 else 0 < veriT_vr9)) \<or>
         (\<forall>veriT_vr7 veriT_vr8 veriT_vr9 :: 'a:: {comm_monoid_add,inverse,times,zero,ord}.
             \<not> veriT_vr7 / veriT_vr8 < veriT_vr9 \<or> \<not> 0 < veriT_vr8 \<or> veriT_vr7 < veriT_vr9 * veriT_vr8)\<close>
  by (ctxt_tactic "qnt_cnf")

lemma
  fixes Cons :: \<open>'a :: {zero} \<Rightarrow> 'alist \<Rightarrow> 'alist\<close> (infix \<open>#\<close> 70) and Nil :: 'alist
  shows \<open>\<not> (\<forall>veriT_vr18 veriT_vr19. poly Nil \<noteq> poly (veriT_vr18 # veriT_vr19) \<or> 0 = veriT_vr18 \<and> poly Nil = poly veriT_vr19)
    \<or> (\<forall>veriT_vr18. 0 = veriT_vr18 \<or> (\<forall>veriT_vr19. poly Nil \<noteq> poly (veriT_vr18 # veriT_vr19)))\<close>
  supply [[show_types]] by (ctxt_tactic "qnt_cnf")

lemma
  fixes Sum :: "['a,'a,'a,'a,'a,'a] \<Rightarrow> bool" ("Sum _ _ _ _ _ _" [99,99,99,99,99,99] 50) 
  shows
    \<open>\<not> (\<forall>veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 veriT_vr86 veriT_vr87 veriT_vr88.
                Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 \<and>
                Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr84 veriT_vr86 veriT_vr87 \<longrightarrow>
                (Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr87 veriT_vr88) =
                (Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr85 veriT_vr86 veriT_vr88)) \<or>
         (\<forall>veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 veriT_vr86 veriT_vr87 veriT_vr88.
             \<not> Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 \<or>
             \<not> Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr84 veriT_vr86 veriT_vr87 \<or>
             \<not> Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr85 veriT_vr86 veriT_vr88 \<or>
             Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr87 veriT_vr88) \<close>
  by (ctxt_tactic "qnt_cnf")

lemma 
  fixes Sum :: "['a,'a,'a,'a,'a,'a] \<Rightarrow> bool" ("Sum _ _ _ _ _ _" [99,99,99,99,99,99] 50) and
        Opp :: "['a,'a,'a,'a,'a] \<Rightarrow> bool" ("Opp _ _ _ _ _" [99,99,99,99,99] 50) and
        Diff :: "['a,'a,'a,'a,'a,'a] \<Rightarrow> bool" ("Diff _ _ _ _ _ _" [99,99,99,99,99,99] 50)
  shows \<open>\<not> (\<forall>veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 veriT_vr86 veriT_vr87 veriT_vr88.
            Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 \<and>
            Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr84 veriT_vr86 veriT_vr87 \<longrightarrow>
            (Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr87 veriT_vr88) =
            (Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr85 veriT_vr86 veriT_vr88)) \<or>
     (\<forall>veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 veriT_vr86 veriT_vr87 veriT_vr88.
         \<not> Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr84 veriT_vr85 \<or>
         \<not> Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr84 veriT_vr86 veriT_vr87 \<or>
         \<not> Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr85 veriT_vr86 veriT_vr88 \<or>
         Sum veriT_vr80 veriT_vr81 veriT_vr82 veriT_vr83 veriT_vr87 veriT_vr88)\<close>
  by (ctxt_tactic "qnt_cnf")

locale _ =
  fixes order :: "'energy \<Rightarrow> 'energy \<Rightarrow> bool"  (infix \<open>e\<le>\<close> 80) and
        energies :: "'energy set"
begin

abbreviation "incomparable P \<equiv> \<lambda>x y. \<not> P x y \<and> \<not> P y x"

lemma
  fixes P :: \<open>('position \<Rightarrow> 'energy set) set\<close> and veriT_vr29
  defines \<open>Delta \<equiv> \<lambda>veriT_vr29. {uua::'energy. \<exists>F::'position \<Rightarrow> 'energy set. F \<in> P \<and> uua \<in> F veriT_vr29}\<close>
  shows \<open> \<not> (\<forall>(veriT_vr29::'position) veriT_vr30::'energy.
                (veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>x::'energy. x \<in> Delta veriT_vr29 \<and> veriT_vr30 \<noteq> x \<longrightarrow> \<not> x e\<le> veriT_vr30) \<longrightarrow>
                 veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>veriT_vr31::'energy. veriT_vr31 \<in> Delta veriT_vr29 \<and> veriT_vr30 \<noteq> veriT_vr31 \<longrightarrow> \<not> veriT_vr31 e\<le> veriT_vr30)) \<and>
                (veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>veriT_vr32::'energy. veriT_vr32 \<in> Delta veriT_vr29 \<and> veriT_vr30 \<noteq> veriT_vr32 \<longrightarrow> \<not> veriT_vr32 e\<le> veriT_vr30) \<longrightarrow>
                 veriT_vr30 \<in> Delta veriT_vr29 \<and> (\<forall>x::'energy. x \<in> Delta veriT_vr29 \<and> veriT_vr30 \<noteq> x \<longrightarrow> \<not> x e\<le> veriT_vr30))) \<or>
         (\<forall>(veriT_vr29::'position) (veriT_vr30::'energy) veriT_vr31::'energy.
             \<not> (veriT_vr30 \<in> Delta veriT_vr29 \<and> (\<forall>x::'energy. x \<in> Delta veriT_vr29 \<and> veriT_vr30 \<noteq> x \<longrightarrow> \<not> x e\<le> veriT_vr30)) \<or>
             veriT_vr31 \<notin> Delta veriT_vr29 \<or> veriT_vr30 = veriT_vr31 \<or> \<not> veriT_vr31 e\<le> veriT_vr30)\<close>
  by (ctxt_tactic "qnt_cnf")

lemma
  fixes P :: \<open>('position \<Rightarrow> 'energy set) set\<close> and veriT_vr29
  defines \<open>Delta \<equiv> \<lambda>veriT_vr29. {uua::'energy. \<exists>F::'position \<Rightarrow> 'energy set. F \<in> P \<and> uua \<in> F veriT_vr29}\<close>
  shows \<open> \<not> (\<forall>(veriT_vr29::'position) veriT_vr30::'energy.
                (alethe_Box (veriT_vr30 \<in> Delta veriT_vr29) \<and>
                 (\<forall>x::'energy. alethe_Box (x \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = x) \<longrightarrow> \<not> alethe_Box (x e\<le> veriT_vr30)) \<longrightarrow>
                 veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>veriT_vr31::'energy. alethe_Box (veriT_vr31 \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = veriT_vr31) \<longrightarrow> \<not> alethe_Box (veriT_vr31 e\<le> veriT_vr30))) \<and>
                (veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>veriT_vr32::'energy. alethe_Box (veriT_vr32 \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = veriT_vr32) \<longrightarrow> \<not> alethe_Box (veriT_vr32 e\<le> veriT_vr30)) \<longrightarrow>
                 alethe_Box (veriT_vr30 \<in> Delta veriT_vr29) \<and> (\<forall>x::'energy. alethe_Box (x \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = x) \<longrightarrow> \<not> alethe_Box (x e\<le> veriT_vr30)))) \<or>
         (\<forall>(veriT_vr29::'position) (veriT_vr30::'energy) veriT_vr31::'energy.
             \<not> (alethe_Box (veriT_vr30 \<in> Delta veriT_vr29) \<and> (\<forall>x::'energy. alethe_Box (x \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = x) \<longrightarrow> \<not> alethe_Box (x e\<le> veriT_vr30))) \<or>
             \<not>alethe_Box (veriT_vr31 \<in> Delta veriT_vr29) \<or> alethe_Box (veriT_vr30 = veriT_vr31) \<or> \<not> alethe_Box (veriT_vr31 e\<le> veriT_vr30))\<close>
  by (ctxt_tactic "qnt_cnf")

context
  fixes P :: \<open>('position \<Rightarrow> 'energy set) set\<close> and veriT_vr29 :: 'position
begin

abbreviation  \<open>Delta \<equiv> \<lambda>veriT_vr29. {uua::'energy. \<exists>F::'position \<Rightarrow> 'energy set. F \<in> P \<and> uua \<in> F veriT_vr29}\<close>
lemma
  shows \<open> \<not> (\<forall>(veriT_vr29::'position) veriT_vr30::'energy.
                (alethe_Box (veriT_vr30 \<in> Delta veriT_vr29) \<and>
                 (\<forall>x::'energy. alethe_Box (x \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = x) \<longrightarrow> \<not> alethe_Box (x e\<le> veriT_vr30)) \<longrightarrow>
                 veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>veriT_vr31::'energy. alethe_Box (veriT_vr31 \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = veriT_vr31) \<longrightarrow> \<not> alethe_Box (veriT_vr31 e\<le> veriT_vr30))) \<and>
                (veriT_vr30 \<in> Delta veriT_vr29 \<and>
                 (\<forall>veriT_vr32::'energy. alethe_Box (veriT_vr32 \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = veriT_vr32) \<longrightarrow> \<not> alethe_Box (veriT_vr32 e\<le> veriT_vr30)) \<longrightarrow>
                 alethe_Box (veriT_vr30 \<in> Delta veriT_vr29) \<and> (\<forall>x::'energy. alethe_Box (x \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = x) \<longrightarrow> \<not> alethe_Box (x e\<le> veriT_vr30)))) \<or>
         (\<forall>(veriT_vr29::'position) (veriT_vr30::'energy) veriT_vr31::'energy.
             \<not> (alethe_Box (veriT_vr30 \<in> Delta veriT_vr29) \<and> (\<forall>x::'energy. alethe_Box (x \<in> Delta veriT_vr29) \<and> \<not>alethe_Box (veriT_vr30 = x) \<longrightarrow> \<not> alethe_Box (x e\<le> veriT_vr30))) \<or>
             \<not>alethe_Box (veriT_vr31 \<in> Delta veriT_vr29) \<or> alethe_Box (veriT_vr30 = veriT_vr31) \<or> \<not> alethe_Box (veriT_vr31 e\<le> veriT_vr30))\<close>
  by (ctxt_tactic "qnt_cnf")

lemma \<open>  \<not> (\<forall>(veriT_vr34::('a \<Rightarrow> bool) \<Rightarrow> bool) veriT_vr35::'a.
                (\<nexists>x::'a \<Rightarrow> bool. veriT_vr34 x \<and> x veriT_vr35) \<and>
                \<not> (\<forall>veriT_vr36::'a \<Rightarrow> bool.
                       \<not> (\<not> (\<forall>veriT_vr37::'a \<Rightarrow> bool. \<not> (veriT_vr34 veriT_vr37 \<and> veriT_vr36 = (\<phi>::('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool) veriT_vr37)) \<and> veriT_vr36 veriT_vr35)) \<longrightarrow>
                \<phi> (\<lambda>uua::'a. \<exists>x::'a \<Rightarrow> bool. veriT_vr34 x \<and> x uua) veriT_vr35) \<or>
         (\<forall>(veriT_vr34::('a \<Rightarrow> bool) \<Rightarrow> bool) (veriT_vr35::'a) (veriT_vr36::'a \<Rightarrow> bool) veriT_vr37::'a \<Rightarrow> bool.
             (\<exists>x::'a \<Rightarrow> bool. veriT_vr34 x \<and> x veriT_vr35) \<or>
             \<not> veriT_vr34 veriT_vr37 \<or> veriT_vr36 \<noteq> \<phi> veriT_vr37 \<or> \<not> veriT_vr36 veriT_vr35 \<or> \<phi> (\<lambda>uua::'a. \<exists>x::'a \<Rightarrow> bool. veriT_vr34 x \<and> x uua) veriT_vr35)  \<close>
  by (ctxt_tactic "qnt_cnf")


lemma \<open>\<not> (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
           inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) =
           (if 0 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15
            else 5 = veriT_vr14 \<and> inv_tm_skip_first_arg_len_eq_1_s5 veriT_vr13 veriT_vr15)) \<or>
    (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
        \<not> inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) \<or>
        0 \<noteq> veriT_vr14 \<or> inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15) \<close>
  by (ctxt_tactic "qnt_cnf")

lemma \<open>\<not> (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
           inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) =
           (if 0 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15
            else if 1 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s1 veriT_vr13 veriT_vr15
                 else if 2 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s2 veriT_vr13 veriT_vr15
                      else 5 = veriT_vr14 \<and> inv_tm_skip_first_arg_len_eq_1_s5 veriT_vr13 veriT_vr15)) \<or>
    (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
        \<not> inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) \<or>
        0 \<noteq> veriT_vr14 \<or> inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15) \<close>
  by (ctxt_tactic "qnt_cnf")


lemma \<open>\<not> (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
           inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) =
           (if 0 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15
            else if 1 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s1 veriT_vr13 veriT_vr15
                 else if 2 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s2 veriT_vr13 veriT_vr15
                      else if 3 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s3 veriT_vr13 veriT_vr15
                           else 5 = veriT_vr14 \<and> inv_tm_skip_first_arg_len_eq_1_s5 veriT_vr13 veriT_vr15)) \<or>
    (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
        \<not> inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) \<or>
        0 \<noteq> veriT_vr14 \<or> inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15) \<close>
  by (ctxt_tactic "qnt_cnf")

lemma \<open>\<not> (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
           inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) =
           (if 0 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15
            else if 1 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s1 veriT_vr13 veriT_vr15
                 else if 2 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s2 veriT_vr13 veriT_vr15
                      else if 3 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s3 veriT_vr13 veriT_vr15
                           else if 4 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s4 veriT_vr13 veriT_vr15
                                else 5 = veriT_vr14 \<and> inv_tm_skip_first_arg_len_eq_1_s5 veriT_vr13 veriT_vr15)) \<or>
    (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
        \<not> inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) \<or>
        0 \<noteq> veriT_vr14 \<or> inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15) \<close>
  by (ctxt_tactic "qnt_cnf")

typedef\<^marker>\<open>tag important\<close> 'a topology = "{L::('a set) \<Rightarrow> bool. True}"
  morphisms "openin" "topology"
  sorry

definition topspace :: "'a topology \<Rightarrow> 'a set"
  where \<open>topspace = undefined\<close>

definition openin :: \<open>'a topology \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where \<open>openin = undefined\<close>

lemma openin_Int[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<inter> T)"
  sorry

lemma \<open>\<not> (\<forall>veriT_vr79::'a.
                veriT_vr79 \<in> topspace (X::'a topology) \<longrightarrow>
                veriT_vr79 \<in> topspace X \<and>
                (\<forall>veriT_vr80::'a. veriT_vr80 \<in> topspace X \<longrightarrow> (f::'a \<Rightarrow> 'b) veriT_vr80 \<in> topspace (Y::'b topology)) \<and>
                (\<forall>veriT_vr81::'b set.
                    openin Y veriT_vr81 \<and> f veriT_vr79 \<in> veriT_vr81 \<longrightarrow>
                    (\<exists>veriT_vr82::'a set. openin X veriT_vr82 \<and> veriT_vr79 \<in> veriT_vr82 \<and> (\<forall>veriT_vr83::'a. veriT_vr83 \<in> veriT_vr82 \<longrightarrow> f veriT_vr83 \<in> veriT_vr81)))) \<or>
         (\<forall>(veriT_vr79::'a) veriT_vr80::'a. veriT_vr79 \<notin> topspace X \<or> veriT_vr80 \<notin> topspace X \<or> f veriT_vr80 \<in> topspace Y) 
    \<close>
  by (ctxt_tactic "qnt_cnf")

lemma \<open>\<not> (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
                inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) =
                (if 0 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15
                 else if 1 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s1 veriT_vr13 veriT_vr15
                      else if 2 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s2 veriT_vr13 veriT_vr15
                           else if 3 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s3 veriT_vr13 veriT_vr15
                                else if 4 = veriT_vr14 then inv_tm_skip_first_arg_len_eq_1_s4 veriT_vr13 veriT_vr15
                                     else 5 = veriT_vr14 \<and> inv_tm_skip_first_arg_len_eq_1_s5 veriT_vr13 veriT_vr15)) \<or>
         (\<forall>veriT_vr13 veriT_vr14 veriT_vr15.
             \<not> inv_tm_skip_first_arg_len_eq_1 veriT_vr13 (veriT_vr14, veriT_vr15) \<or> 0 \<noteq> veriT_vr14 \<or> inv_tm_skip_first_arg_len_eq_1_s0 veriT_vr13 veriT_vr15)\<close>
  by (ctxt_tactic "qnt_cnf")

end

lemma \<open>\<not> (\<forall>veriT_vr207 veriT_vr208.
                (stfx_rel veriT_vr207 veriT_vr208 \<longrightarrow>
                 fst veriT_vr207 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu} \<and>
                 fst veriT_vr208 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu} \<and>
                 snd veriT_vr207 \<in> \<O>\<^sub>Y (fst veriT_vr207) \<and>
                 snd veriT_vr208 \<in> \<O>\<^sub>Y (fst veriT_vr208) \<and>
                 (\<exists>veriT_vr209. veriT_vr209 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu} \<and> veriT_vr209 \<subseteq> fst veriT_vr207 \<inter> fst veriT_vr208 \<and> \<rho>\<^sub>Y (fst veriT_vr207) veriT_vr209 (snd veriT_vr207) = \<rho>\<^sub>Y (fst veriT_vr208) veriT_vr209 (snd veriT_vr208))) \<and>
                (fst veriT_vr207 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu} \<and>
                 fst veriT_vr208 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu} \<and>
                 snd veriT_vr207 \<in> \<O>\<^sub>Y (fst veriT_vr207) \<and>
                 snd veriT_vr208 \<in> \<O>\<^sub>Y (fst veriT_vr208) \<and>
                 \<not> (\<forall>veriT_vr210. \<not> (veriT_vr210 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu} \<and> veriT_vr210 \<subseteq> fst veriT_vr207 \<inter> fst veriT_vr208 \<and> \<rho>\<^sub>Y (fst veriT_vr207) veriT_vr210 (snd veriT_vr207) = \<rho>\<^sub>Y (fst veriT_vr208) veriT_vr210 (snd veriT_vr208))) \<longrightarrow>
                 stfx_rel veriT_vr207 veriT_vr208)) \<or>
         (\<forall>veriT_vr207 veriT_vr208. \<not> stfx_rel veriT_vr207 veriT_vr208 \<or> fst veriT_vr208 \<in> {uu. is_open\<^sub>Y uu \<and> f x \<in> uu}) \<close>
  by (ctxt_tactic "qnt_cnf")
end

experiment
begin
abbreviation (input)
 "fishburn (a::_::linorder) b v ab ==
  ((ab \<le> a \<longrightarrow> v \<le> ab) \<and> (a < ab \<and> ab < b \<longrightarrow> ab = v) \<and> (b \<le> ab \<longrightarrow> ab \<le> v))"

abbreviation  (input)fishburn2 :: "('a::linorder) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_ \<le>/ _/ '(mod _,_'))\<close> [51,51,0,0])
  where "fishburn2 ab v a b \<equiv> fishburn a b v ab"

abbreviation (input)
 "knuth (a::_::linorder) b x y ==
  ((y \<le> a \<longrightarrow> x \<le> a) \<and> (a < y \<and> y < b \<longrightarrow> y = x) \<and> (b \<le> y \<longrightarrow> b \<le> x))"

abbreviation (input) knuth2 :: "('a::linorder) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_ \<cong>/ _/ '(mod _,_'))\<close> [51,51,0,0])
  where "knuth2 x y a b \<equiv> knuth a b x y"


lemma \<open>\<not> (\<forall>(veriT_vr28::'a::{linorder}) (veriT_vr29::'a) (veriT_vr30::'a) veriT_vr31::'a. veriT_vr28 \<le> veriT_vr30 (mod veriT_vr29,veriT_vr31) \<longrightarrow> veriT_vr30 \<cong> veriT_vr28 (mod veriT_vr29,veriT_vr31)) \<or>
         (\<forall>(veriT_vr28::'a) (veriT_vr30::'a) veriT_vr31::'a. \<not> veriT_vr30 \<le> veriT_vr28 \<or> veriT_vr28 < veriT_vr31 \<or> \<not> veriT_vr28 \<le> veriT_vr30 \<or> \<not> veriT_vr31 \<le> veriT_vr28 \<or> veriT_vr31 \<le> veriT_vr30) \<close>
  supply [[simp_trace=false,simp_trace_depth_limit=5]]  by (ctxt_tactic "qnt_cnf")

lemma \<open>\<not> (\<forall>(veriT_vr2::'a::{one, zero} set) veriT_vr3.
                ((veriT_vr3 \<in> U \<longrightarrow> veriT_vr3 \<in> topspace X \<and> 0 \<in> veriT_vr2) \<and> (veriT_vr3 \<notin> U \<longrightarrow> veriT_vr3 \<in> topspace X \<and> 1 \<in> veriT_vr2)) =
                ((veriT_vr3 \<in> U \<longrightarrow> veriT_vr3 \<in> topspace X \<and> 0 \<in> veriT_vr2) \<and> (veriT_vr3 \<notin> U \<longrightarrow> veriT_vr3 \<in> topspace X \<and> 1 \<in> veriT_vr2))) \<or>
         (\<forall>(veriT_vr2::'a::{one, zero} set) veriT_vr3.
             veriT_vr3 \<in> U \<or>
             veriT_vr3 \<notin> topspace X \<or>
             1 \<notin> veriT_vr2 \<or> (veriT_vr3 \<in> U \<longrightarrow> veriT_vr3 \<in> topspace X \<and> 0 \<in> veriT_vr2) \<and> (veriT_vr3 \<notin> U \<longrightarrow> veriT_vr3 \<in> topspace X \<and> 1 \<in> veriT_vr2)) \<close>
  by (ctxt_tactic "qnt_cnf")

lemma \<open> \<not> (\<forall>(veriT_vr24:: 'a set) veriT_vr25. (veriT_vr24 \<subseteq> veriT_vr25) = (veriT_vr24 = veriT_vr25 \<inter> veriT_vr24)) \<or>
         (\<forall>(veriT_vr24:: 'a set) veriT_vr25. veriT_vr24 \<noteq> veriT_vr25 \<inter> veriT_vr24 \<or> veriT_vr24 \<subseteq> veriT_vr25) \<close>
  by (ctxt_tactic "qnt_cnf")

(* Rule 30: and *)

lemma and_1:
  assumes "a \<and> b \<and> c"
  shows  "a"
  using assms
  by (ctxt_tactic "and" "0::int")

lemma and_2:
  assumes "a \<and> b \<and> c"
  shows  "c"
  using assms
  by (ctxt_tactic "and" "2::int")

lemma and_3:
  assumes "(a \<and> d) \<and> b \<and> c"
  shows  "(a \<and> d)"
  using assms
  by (ctxt_tactic "and" "0::int")

lemma and_4:
  assumes "a \<and> b \<and> (c \<and> d)"
  shows  "c \<and> d"
  using assms
  by (ctxt_tactic "and" "2::int")

lemma and_5:
  assumes "a"
  shows "a"
  using assms
  by (ctxt_tactic "and" "0::int")

(* Rule 31: not_or *)

lemma not_or_1:
  assumes "\<not>(a \<or> b \<or> c)"
  shows  "\<not>a"
  using assms
  by (ctxt_tactic "not_or" "0::int")

lemma not_or_2:
  assumes "\<not>(a)"
  shows  "\<not>a"
  using assms
  by (ctxt_tactic "not_or" "0::int")

lemma not_or_3:
  assumes "\<not>((a \<or> d) \<or> b \<or> c)"
  shows  "\<not>(a \<or> d)"
  using assms
  by (ctxt_tactic "not_or" "0::int")

lemma not_or_4:
  assumes "\<not>(a \<or> b \<or> (c \<or> d))"
  shows  "\<not>(c \<or> d)"
  using assms
  by (ctxt_tactic "not_or" "2::int")

lemma not_or_5:
  assumes "\<not>(a \<or> b \<or> \<not>(c \<or> d))"
  shows  "\<not>(\<not>(c \<or> d))"
  using assms
  by (ctxt_tactic "not_or" "2::int")

lemma not_or_6:
  assumes " \<not> ((\<not> (\<not> 1 \<le> a \<and> 1 \<le> b \<and> 1 \<le> c) \<or>
             1 \<le> b \<or> 1 \<le> c))"
  shows "\<not> \<not> (\<not> 1 \<le> a \<and> 1 \<le> b \<and> 1 \<le> c)"
  using assms
  by (ctxt_tactic "not_or" "0::int")

(* Rule 32: or *)

lemma or_1:
  assumes "(a \<or> b \<or> c)"
  shows  "(a \<or> b \<or> c)"
  using assms
  by (ctxt_tactic "or")

lemma or_2:
  assumes "(a)"
  shows  "a"
  using assms
  by (ctxt_tactic "or")

lemma or_3:
  assumes "((a \<or> d) \<or> b \<or> c)"
  shows  "(a \<or> d) \<or> b \<or> c"
  using assms
  by (ctxt_tactic "or" "0::int")


(* Rule 33: weakening *)

lemma weakening_1: 
  assumes "a"
  shows  "a \<or> b"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_2:
  assumes "a \<or> b \<or> c"
  shows  "a \<or> b \<or> c \<or> d \<or> e"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_3:
  assumes "a \<or> b \<or> c"
  shows  "a \<or> b \<or> c \<or> c \<or> a"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_4:
  assumes "(a \<or> b) \<or> b \<or> c"
  shows  "(a \<or> b) \<or> b \<or> c \<or> (c \<or> a) \<or> e"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_5: 
  assumes "a \<or> \<not>f"
  shows  "a \<or> b \<or> \<not>f"
  using assms
  by (ctxt_tactic "weakening")


(* Rule 34: reordering *)

lemma reordering_1: 
  assumes "b \<or> a"
  shows "a \<or> b"
  using assms
  by (ctxt_tactic "reordering")

lemma reordering_2:
  assumes "a \<or> b \<or> c"
  shows "c \<or> b \<or> a"
  using assms
  by (ctxt_tactic "reordering")

lemma reordering_3:
  assumes "a \<or> b \<or> a"
  shows "a \<or> a \<or> b"
  using assms
  by (ctxt_tactic "reordering")

lemma reordering_4:
  assumes "(a \<or> b) \<or> a \<or> b"
  shows "a \<or> b \<or> (a \<or> b)"
  using assms
  by (ctxt_tactic "reordering")

(* Rule 34: shuffle *)

lemma shuffle_or_1: 
  shows "(b \<or> a) = (a \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_2:
  shows "(a \<or> b) = (a \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_3: 
  shows "(a \<or> b \<or> c) = (c \<or> a \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_4: 
  shows "(a \<or> b \<or> c) = (a \<or> b \<or> c)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_5: 
  shows "(a \<or> b \<or> c \<or> d) = (c \<or> d \<or> b \<or> a)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_6: 
  shows "(a \<or> (b \<or> c) \<or> d) = ((b \<or> c) \<or> d \<or> a)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_7: 
  shows "(a \<or> b \<or> (c \<or> d)) = (a \<or> (c \<or> d) \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_8: 
  shows "(a \<or> b \<or> (c \<and> (d \<or> e))) = (a \<or> (c \<and> (d \<or> e)) \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_and_1: 
  shows "(b \<and> a) = (a \<and> b)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_2: 
  shows "(a \<and> a) = (a \<and> a)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_3: 
  shows "(a \<and> b \<and> c) = (b \<and> a \<and> c)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_4: 
  shows "((a \<longrightarrow> b ) \<and> c) = (c \<and> (a \<longrightarrow> b))"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_5: 
  shows "(d \<and> (a \<or> b ) \<and> c) = (c \<and> d \<and> (a \<or> b))"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_6a:
  shows "(\<not> a \<and> \<not> b \<and> c \<and> d) = (c \<and> d \<and> \<not> a \<and> \<not> b)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_6b:
  shows "(\<not> (c \<and> a) \<and> \<not> (d \<and> b) \<and> c \<and> a) =
         (c \<and> a \<and> \<not> (c \<and> a) \<and> \<not> (d \<and> b))"
  by (ctxt_tactic "shuffle" "HOL.conj")

(* Rule 36: not_and *)

lemma not_and_1: 
  assumes "\<not>(a \<and> b \<and> c)"
  shows "\<not>a \<or> \<not>b \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_2:
  assumes "\<not>a"
  shows "\<not>a"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_3:
  assumes "\<not>((a \<and> d) \<and> b \<and> c)"
  shows "\<not>(a \<and> d) \<or> \<not>b \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_4:
  assumes "\<not>(a \<and> b \<and> c \<and> (a \<and> d))"
  shows "\<not>a \<or> \<not>b \<or> \<not>c \<or> \<not>(a \<and> d)"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_5:
  assumes "\<not>(a \<and> a \<and> a)"
  shows "\<not>a \<or> \<not>a \<or> \<not>a"
  using assms
  by (ctxt_tactic "not_and")


(* Rule 37: xor1 *)

lemma xor1_1: 
  assumes "\<not>(a = b)"
  shows  "a \<or> b"
  using assms
  by (ctxt_tactic "xor1")

lemma xor1_2:
  assumes "\<not>((a \<or> b) = b)"
  shows  "(a \<or> b) \<or> b"
  using assms
  by (ctxt_tactic "xor1")

lemma xor1_3:
  assumes "\<not>((\<not>(a = b)) = b)"
  shows  "(\<not>(a = b)) \<or> b"
  using assms
  by (ctxt_tactic "xor1")

lemma xor1_4:
  assumes "\<not>((a = b) = (\<not>(b = c)))"
  shows  "(a = b) \<or> (\<not>(b = c))"
  using assms
  by (ctxt_tactic "xor1")


(* Rule 38: xor2 *)

lemma xor2_1: 
  assumes "\<not>(a = b)"
  shows  "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "xor2")

lemma xor2_2:
  assumes "\<not>((a \<or> b) = b)"
  shows  "\<not>(a \<or> b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "xor2")

lemma xor2_3:
  assumes "\<not>((a = b) = b)"
  shows  "\<not>(a = b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "xor2")

lemma xor2_4:
  assumes "\<not>((\<not>(a = b)) = (\<not>(b = c)))"
  shows  "\<not>(\<not>(a = b)) \<or> \<not>(\<not>(b = c))"
  using assms
  by (ctxt_tactic "xor2")


(* Rule 39: not_xor1 *)

lemma not_xor1_1: 
  assumes "\<not>(\<not>(a = b))"
  shows  "a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_xor1")

lemma not_xor1_2:
  assumes "\<not>(\<not>((a \<or> b) = b))"
  shows  "(a \<or> b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_xor1")

lemma not_xor1_3:
  assumes "\<not>(\<not>((a = b) = b))"
  shows  "(a = b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_xor1")

lemma not_xor1_4:
  assumes "\<not>(\<not>((\<not>(a = b)) = (\<not>(b = c))))"
  shows  "(\<not>(a = b)) \<or> (\<not>(\<not>(b = c)))"
  using assms
  by (ctxt_tactic "not_xor1")


(* Rule 40: not_xor2 *)

lemma not_xor2_1: 
  assumes "\<not>(\<not>(a = b))"
  shows  "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "not_xor2")

lemma not_xor2_2:
  assumes "\<not>(\<not>((a \<or> b) = b))"
  shows  "\<not>(a \<or> b) \<or> b"
  using assms
  by (ctxt_tactic "not_xor2")

lemma not_xor2_3:
  assumes "\<not>(\<not>((a = b) = b))"
  shows  "\<not>(a = b) \<or> b"
  using assms
  by (ctxt_tactic "not_xor2")

lemma not_xor2_4:
  assumes "\<not>(\<not>((\<not>(a = b)) = (\<not>(b = c))))"
  shows  "(\<not>(\<not>(a = b))) \<or> (\<not>(b = c))"
  using assms
  by (ctxt_tactic "not_xor2")


(* Rule 41: implies *)

lemma implies_1: 
  assumes "(a \<longrightarrow> b)"
  shows  "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "implies")

lemma implies_2:
  assumes "((a\<or>b) \<longrightarrow> b)"
  shows  "\<not>(a\<or>b) \<or> b"
  using assms
  by (ctxt_tactic "implies")

lemma implies_3:
  assumes "((a\<longrightarrow>b) \<longrightarrow> b)"
  shows  "\<not>(a\<longrightarrow>b) \<or> b"
  using assms
  by (ctxt_tactic "implies")

lemma implies_4:
  assumes "((a\<longrightarrow>b) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "\<not>(a\<longrightarrow>b) \<or> (b \<longrightarrow> c)"
  using assms
  by (ctxt_tactic "implies")

lemma implies_5:
  assumes "((\<not>(a\<longrightarrow>b)) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "\<not>(\<not>(a\<longrightarrow>b)) \<or> (b \<longrightarrow> c)"
  using assms
  by (ctxt_tactic "implies")


(* Rule 42: not_implies1 *)

lemma not_implies1_1: 
  assumes "\<not>(a \<longrightarrow> b)"
  shows  "a"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_2:
  assumes "\<not>((a\<or>b) \<longrightarrow> b)"
  shows  "(a\<or>b)"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_3:
  assumes "\<not>((a\<longrightarrow>b) \<longrightarrow> b)"
  shows  "(a\<longrightarrow>b)"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_4:
  assumes "\<not>((a\<longrightarrow>b) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "(a\<longrightarrow>b)"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_5:
  assumes "\<not>((\<not>(a\<longrightarrow>b)) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "(\<not>(a\<longrightarrow>b))"
  using assms
  by (ctxt_tactic "not_implies1")


(* Rule 43: not_implies2 *)

lemma not_implies2_1: 
  assumes "\<not>(a \<longrightarrow> b)"
  shows  "\<not>b"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_2:
  assumes "\<not>((a\<or>b) \<longrightarrow> b)"
  shows  "\<not>b"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_3:
  assumes "\<not>(a \<longrightarrow> (a\<longrightarrow>b))"
  shows  "\<not>(a\<longrightarrow>b)"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_4:
  assumes "\<not>((a \<longrightarrow> b) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "\<not>(b \<longrightarrow> c)"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_5:
  assumes "\<not>((a \<longrightarrow> b) \<longrightarrow> (\<not>(b \<longrightarrow> c)))"
  shows  "\<not>(\<not>(b \<longrightarrow> c))"
  using assms
  by (ctxt_tactic "not_implies2")


(* Rule 44: equiv1 *)

lemma equiv1_1: 
  assumes "(a = b)"
  shows  "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_2:
  assumes "((a\<or>b) = b)"
  shows  "\<not>(a\<or>b) \<or> b"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_3:
  assumes "((a=b) = b)"
  shows  "\<not>(a=b) \<or> b"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_4:
  assumes "((a=b) = (b = c))"
  shows  "\<not>(a=b) \<or> (b = c)"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_5:
  assumes "((\<not>(a=b)) = (b = c))"
  shows  "\<not>(\<not>(a=b)) \<or> (b = c)"
  using assms
  by (ctxt_tactic "equiv1")


(* Rule 44: equiv2 *)

lemma equiv2_1: 
  assumes "(a = b)"
  shows  "a \<or> \<not>b"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_2:
  assumes "((a\<or>b) = b)"
  shows  "(a\<or>b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_3:
  assumes "((a=b) = b)"
  shows  "(a=b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_4:
  assumes "((a=b) = (b = c))"
  shows  "(a=b) \<or> \<not>(b = c)"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_5:
  assumes "((a=b) = (\<not>(b = c)))"
  shows  "(a=b) \<or> \<not>(\<not>(b = c))"
  using assms
  by (ctxt_tactic "equiv2")


(* Rule 46: not_equiv1 *)

lemma not_equiv1_1: 
  assumes "\<not>(a = b)"
  shows  "a \<or> b"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_2:
  assumes "\<not>((a\<or>b) = b)"
  shows  "(a\<or>b) \<or> b"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_3:
  assumes "\<not>((a=b) = b)"
  shows  "(a=b) \<or> b"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_4:
  assumes "\<not>((a=b) = (b = c))"
  shows  "(a=b) \<or> (b = c)"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_5:
  assumes "\<not>((a=b) = (\<not>(b = c)))"
  shows  "(a=b) \<or> \<not>(b = c)"
  using assms
  by (ctxt_tactic "not_equiv1")


(* Rule 47: not_equiv2 *)

lemma not_equiv2_1: 
  assumes "\<not>(a = b)"
  shows  "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_2:
  assumes "\<not>((a\<or>b) = b)"
  shows  "\<not>(a\<or>b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_3:
  assumes "\<not>((a=b) = b)"
  shows  "\<not>(a=b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_4:
  assumes "\<not>((a=b) = (b = c))"
  shows  "\<not>(a=b) \<or> \<not>(b = c)"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_5:
  assumes "\<not>((a=b) = (\<not>(b = c)))"
  shows  "\<not>(a=b) \<or> \<not>(\<not>(b = c))"
  using assms
  by (ctxt_tactic "not_equiv2")


(* Rule 48: and_pos *)

lemma "\<not>(a \<and> b \<and> c) \<or> c"
  by (ctxt_tactic "and_pos" "2")

lemma and_pos_1: "\<not>(a \<and> b \<and> c) \<or> b"
  by (ctxt_tactic "and_pos" "1")

lemma and_pos_2: "\<not>(a \<and> b \<and> c) \<or> c"
  by (ctxt_tactic "and_pos" "2")

lemma and_pos_3: "\<not>(a \<and> (b \<and> c) \<and> d) \<or> (b \<and> c)"
  by (ctxt_tactic "and_pos" "1")

lemma and_pos_4: "\<not>(a \<and> (b \<and> c) \<and> d) \<or> d"
  by (ctxt_tactic "and_pos" "2")

lemma and_pos_5: "\<not>(a \<and> (b \<or> \<not>c \<and> d)) \<or> (b \<or> \<not>c \<and> d)"
  by (ctxt_tactic "and_pos" "1")

lemma and_pos_6: "\<not>(a \<and> (b \<and> c)) \<or> (b \<and> c)"
  by (ctxt_tactic "and_pos" "1")

lemma and_pos_7: "\<not>((\<not>a \<or> b) \<and> c) \<or> (\<not>a \<or> b)"
  by (ctxt_tactic "and_pos" "0")

lemma and_pos_8: "\<not>(a \<and> \<not>b) \<or> \<not>b"
  by (ctxt_tactic "and_pos" "1")

lemma and_pos_9: "\<not>(a) \<or> a"
  by (ctxt_tactic "and_pos" "0")

(* Rule 48: and_neg *)

lemma and_neg_1: "(a \<and> b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "and_neg")

lemma and_neg_2: "(a \<and> b \<and> c) \<or> \<not>a \<or> \<not>b \<or> \<not>c"
  by (ctxt_tactic "and_neg")

lemma and_neg_3: "(a \<and> b \<and> c \<and> d) \<or> \<not>a \<or> \<not>b \<or> \<not>c \<or> \<not>d"
  by (ctxt_tactic "and_neg")

lemma and_neg_4: "(a \<and> (b \<and> c)) \<or> \<not>a \<or> \<not>(b \<and> c)"
  by (ctxt_tactic "and_neg")

lemma and_neg_5: "((a \<and> b) \<and> d) \<or> \<not>(a \<and> b) \<or> \<not>d"
  by (ctxt_tactic "and_neg")

lemma and_neg_6: "(a \<and> d) \<or> \<not>(a \<and> d)"
  by (ctxt_tactic "and_neg")

lemma and_neg_7: "((a = c) \<and> (b \<longrightarrow> \<not>c \<or> d)) \<or> \<not>(a = c) \<or> \<not>(b \<longrightarrow> \<not>c \<or> d)"
  by (ctxt_tactic "and_neg")

lemma and_neg_8: "(\<not>a \<and> \<not>(b \<or> c) \<and> d) \<or> \<not>\<not>a \<or> \<not>\<not>(b \<or> c) \<or> \<not>d"
  by (ctxt_tactic "and_neg")

lemma and_neg_9: "a \<or> (\<not>a)"
  by (ctxt_tactic "and_neg")

(* Rule 50: or_pos *)

lemma or_pos_1: "\<not>(a \<or> b) \<or> a \<or> b"
  by (ctxt_tactic "or_pos")

lemma or_pos_2: "\<not>(a \<or> b \<or> c) \<or> a \<or> b \<or> c"
  by (ctxt_tactic "or_pos")

lemma or_pos_3: "\<not>(a \<or> b \<or> c \<or> d) \<or> a \<or> b \<or> c \<or> d"
  by (ctxt_tactic "or_pos")

lemma or_pos_4: "\<not>(a \<or> (b \<or> c)) \<or> a \<or> b \<or> c"
  by (ctxt_tactic "or_pos")

lemma or_pos_5: "\<not>((a \<or> b) \<or> c) \<or> (a \<or> b) \<or> c"
  by (ctxt_tactic "or_pos")

lemma or_pos_6: "\<not>(\<not>(e \<or> f) \<or> (a \<or> b \<and> c) \<or> d) \<or> \<not>(e \<or> f) \<or> (a \<or> b \<and> c) \<or> d"
  by (ctxt_tactic "or_pos")

lemma or_pos_7: "\<not>(a) \<or> a"
  by (ctxt_tactic "or_pos")

(* Rule 51: or_neg *)

lemma or_neg_1: "(a \<or> b \<or> c) \<or> \<not>a"
  by (ctxt_tactic "or_neg" "0::int")

lemma or_neg_2: "(a \<or> b \<or> c) \<or> \<not>b"
  by (ctxt_tactic "or_neg" "1")

lemma or_neg_3: "(a \<or> b \<or> c) \<or> \<not>c"
  by (ctxt_tactic "or_neg" "2")

lemma or_neg_4: "((a \<or> b) \<or> c) \<or> \<not>(a \<or> b)"
  by (ctxt_tactic "or_neg" "0")

lemma or_neg_5: "(a \<or> (b \<or> c) \<or> d) \<or> \<not>(b \<or> c)"
  by (ctxt_tactic "or_neg" "1")

lemma or_neg_6: "(a \<or> b \<or> (c \<or> d)) \<or> \<not>(c \<or> d)"
  by (ctxt_tactic "or_neg" "2")

lemma or_neg_7: "((a \<and> b) \<or> b \<or> (\<not>c \<longrightarrow> d)) \<or> \<not>(\<not>c \<longrightarrow> d)"
  by (ctxt_tactic "or_neg" "2")

lemma or_neg_8: "((a \<and> b) \<or> b \<or> \<not>(c \<longrightarrow> d)) \<or> \<not>(\<not>(c \<longrightarrow> d))"
  by (ctxt_tactic "or_neg" "2")

lemma or_neg_9: "(\<not>a \<or> b \<or> c) \<or> \<not>(\<not>a)"
  by (ctxt_tactic "or_neg" "0")

lemma or_neg_10: "(\<not>a \<or> b) \<or> \<not>(\<not>a)"
  by (ctxt_tactic "or_neg" "0")

lemma or_neg_11: "(\<not>a \<or> b) \<or> \<not>b"
  by (ctxt_tactic "or_neg" "1")

lemma or_neg_12: "(a) \<or> \<not>a"
  by (ctxt_tactic "or_neg" "0")

(* Rule 52: xor_pos1 *)

lemma xor_pos1_1: "\<not>(a \<noteq> b) \<or> a \<or> b"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_2: "\<not>((a\<or>c) \<noteq> b) \<or> (a\<or>c) \<or> b"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_3: "\<not>((a\<and>c) \<noteq> b) \<or> (a\<and>c) \<or> b"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_4: "\<not>(a \<noteq> (b \<and> c)) \<or> a \<or> (b \<and> c)"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_5: "\<not>((a \<and> b) \<noteq> ((c \<or> d))) \<or> (a \<and> b) \<or> (c \<or> d)"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_6: "\<not>((\<not>a) \<noteq> b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_7: "\<not>(a \<noteq> (\<not>b)) \<or> a \<or> \<not>b"
  by (ctxt_tactic "xor_pos1")

(* Rule 53: xor_pos2 *)

lemma xor_pos2_1: "\<not>(a \<noteq> b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_2: "\<not>((a\<or>c) \<noteq> b) \<or> \<not>(a\<or>c) \<or> \<not>b"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_3: "\<not>((a\<and>c) \<noteq> b) \<or> \<not>(a\<and>c) \<or> \<not>b"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_4: "\<not>(a \<noteq> (b \<or> c)) \<or> \<not>a \<or> \<not>(b \<or> c)"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_5: "\<not>((a \<and> b) \<noteq> (c \<or> d)) \<or> \<not>(a \<and> b) \<or> \<not>(c \<or> d)"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_6: \<open>\<not>((\<not>a) \<noteq> b) \<or> \<not>\<not>a \<or> \<not>b\<close>
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_7: \<open>\<not>(a \<noteq> (\<not>b)) \<or> \<not>a \<or> \<not>\<not>b\<close>
  by (ctxt_tactic "xor_pos2")

(* Rule 54: xor_neg1 *)

lemma xor_neg1_1: "(a \<noteq> b) \<or> a \<or> \<not>b"
  by (ctxt_tactic "xor_neg1")

lemma xor_neg1_2: "((a\<or>c) \<noteq> b) \<or> (a\<or>c) \<or> \<not>b"
  by (ctxt_tactic "xor_neg1")

lemma xor_neg1_3: "(b \<noteq> (a\<and>c)) \<or> b \<or> \<not>(a\<and>c)"
  by (ctxt_tactic "xor_neg1")

lemma xor_neg1_4: "(a \<noteq> (\<not>b)) \<or> a \<or> \<not>\<not>b"
  by (ctxt_tactic "xor_neg1")

lemma xor_neg1_5: "((\<not>a) \<noteq> b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "xor_neg1")

(* Rule 55: xor_neg2 *)

lemma xor_neg2_1: "(a \<noteq> b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "xor_neg2")

lemma xor_neg2_2: "((a\<or>c) \<noteq> b) \<or> \<not>(a\<or>c) \<or> b"
  by (ctxt_tactic "xor_neg2")

lemma xor_neg2_3: "(b \<noteq> (a\<and>c)) \<or> \<not>b \<or> (a\<and>c)"
  by (ctxt_tactic "xor_neg2")

lemma xor_neg2_4: "(a \<noteq> (\<not>b)) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "xor_neg2")

lemma xor_neg2_5: "((\<not>a) \<noteq> b) \<or> \<not>\<not>a \<or> b"
  by (ctxt_tactic "xor_neg2")

(* Rule 56: implies_pos *)

lemma implies_pos_1: "\<not>(a \<longrightarrow> b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_2: "\<not>(p \<longrightarrow> \<not>q) \<or> \<not>p \<or> \<not>q"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_3: \<open>\<not>(\<not>p \<longrightarrow> q) \<or> \<not>\<not>p \<or> q\<close>
  by (ctxt_tactic "implies_pos")

lemma implies_pos_4:  "\<not>((a \<and> b) \<longrightarrow> c) \<or> \<not>(a \<and> b) \<or> c"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_5: "\<not>((a \<longrightarrow> b) \<longrightarrow> c) \<or> \<not>(a \<longrightarrow> b) \<or> c"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_6: "\<not>((a \<longrightarrow> b) \<longrightarrow> (c \<longrightarrow> d)) \<or> \<not>(a \<longrightarrow> b) \<or> (c \<longrightarrow> d)"
  by (ctxt_tactic "implies_pos")

(* Rule 57: implies_neg1 *)

lemma implies_neg1_1: "(a \<longrightarrow> b) \<or> a"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg1_2:  "((a \<and> b) \<longrightarrow> c) \<or> (a \<and> b)"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg1_3: "((a \<longrightarrow> b) \<longrightarrow> c) \<or> (a \<longrightarrow> b)"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg1_4: "((a \<longrightarrow> b) \<longrightarrow> (c \<longrightarrow> d)) \<or> (a \<longrightarrow> b)"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg1_5: "((a = b) \<longrightarrow> b) \<or> (a = b)"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg1_6: "(\<not>(a = b) \<longrightarrow> b) \<or> \<not>(a = b)"
  by (ctxt_tactic "implies_neg1")

(* Rule 58: implies_neg2 *)

lemma implies_neg2_1: "(a \<longrightarrow> b) \<or> \<not>b"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_2:  "((a \<and> b) \<longrightarrow> c) \<or> \<not>c"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_3: "((a \<longrightarrow> b) \<longrightarrow> c) \<or> \<not>c"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_4: "((a \<longrightarrow> b) \<longrightarrow> (c \<longrightarrow> d)) \<or> \<not>(c \<longrightarrow> d)"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_5: "(a \<longrightarrow> \<not>b) \<or> \<not>\<not>b"
  by (ctxt_tactic "implies_neg2")

(* Rule 59: equiv_pos1 *)

lemma equiv_pos1_1: "\<not>(a = b) \<or> a \<or> \<not>b"
  by (ctxt_tactic "equiv_pos1")

lemma equiv_pos1_2: "\<not>(a = (b = c)) \<or> a \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_pos1")

lemma equiv_pos1_3: "\<not>((a = d) = (b = c)) \<or> (a = d) \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_pos1")

lemma equiv_pos1_4: "\<not>((\<not>a) = b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "equiv_pos1")

lemma equiv_pos1_5: "\<not>(a = (\<not>b)) \<or> a \<or> \<not>\<not>b"
  by (ctxt_tactic "equiv_pos1")

(* Rule 60: equiv_pos2 *)

lemma equiv_pos2_1: "\<not>(a = b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "equiv_pos2")

lemma equiv_pos2_2: "\<not>(a = (b = c)) \<or> \<not>a \<or> (b = c)"
  by (ctxt_tactic "equiv_pos2")

lemma equiv_pos2_3: "\<not>((a = d) = (b = c)) \<or> \<not>(a = d) \<or> (b = c)"
  by (ctxt_tactic "equiv_pos2")

lemma equiv_pos2_4: "\<not>((\<not>a) = b) \<or> \<not>\<not>a \<or> b"
  by (ctxt_tactic "equiv_pos2")

lemma equiv_pos2_5: "\<not>(a = (\<not>b)) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "equiv_pos2")
end

experiment
  fixes P :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> and Q :: \<open>nat \<Rightarrow> bool\<close>
begin
ML \<open>
fun generate_term n =
  if n = 0 then @{term \<open>0::nat\<close>}
  else @{term \<open>Suc\<close>} $ generate_term (n-1)

fun disj m n =
  if m = 0 then @{term Q} $  generate_term n
  else @{term \<open>HOL.disj\<close>} $ disj (m-1) n $ disj (m-1) n

val n = 100
val m = 10
val t1 = disj m n
val t2 = @{term Q} $ generate_term n

val ct = 
  @{term \<open>Trueprop\<close>} $ (
  @{term \<open>HOL.disj\<close>} $
    (@{term \<open>Not\<close>} $ (@{term \<open>HOL.eq :: bool \<Rightarrow> bool \<Rightarrow> bool\<close>} $ t1 $ t2)) $
      
    (@{term \<open>HOL.disj\<close>} $ (@{term \<open>Not\<close>} $ t1) $ t2))
  |> Envir.beta_norm

\<close>

ML \<open>
(Alethe_Replay_Methods.equiv_pos2 @{context} [] ct) 
|> Thm.one_prem
\<close>

end
(* Rule 61: equiv_neg1 *)

lemma equiv_neg1_1: "(a = b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_2: "(a = (b = c)) \<or> \<not>a \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_3: "((a = d) = (b = c)) \<or> \<not>(a = d) \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_4: "((\<not>a) = b) \<or> \<not>(\<not>a) \<or> \<not>b"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_5: "(a = (\<not>b)) \<or> \<not>a \<or> \<not>(\<not>b)"
  by (ctxt_tactic "equiv_neg1")

(* Rule 62: equiv_neg2 *)

lemma equiv_neg2_1: "(a = b) \<or> a \<or> b"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_2: "(a = (b = c)) \<or> a \<or> (b = c)"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_3: "((a = d) = (b = c)) \<or> (a = d) \<or> (b = c)"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_4: "((\<not>a) = b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_5: "(a = (\<not>b)) \<or> a \<or> \<not>b"
  by (ctxt_tactic "equiv_neg2")

(* Rule 63: ite1 *)

lemma ite1_1: 
  assumes "(If a b c)"
  shows "a \<or> c"
  using assms
  by (ctxt_tactic "ite1")

lemma ite1_2: 
  assumes "(If (If e d f) b c)"
  shows "(If e d f) \<or> c"
  using assms
  by (ctxt_tactic "ite1")

lemma ite1_3: 
  assumes "(If a b (If e d f))"
  shows "a \<or> (If e d f)"
  using assms
  by (ctxt_tactic "ite1")

(* Rule 64: ite2 *)

lemma ite2_1: 
  assumes "(If a b c)"
  shows "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "ite2")

lemma ite2_2: 
  assumes "(If (If e d f) b c)"
  shows "\<not>(If e d f) \<or> b"
  using assms
  by (ctxt_tactic "ite2")

lemma ite2_3: 
  assumes "(If a b (If e d f))"
  shows "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "ite2")

(* Rule 65: ite_pos1 *)

lemma ite_pos1_1: "\<not>(If a b c) \<or> a \<or> c"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_2: "\<not>(If a b (a \<or> c)) \<or> a \<or> (a \<or> c)"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_3: "\<not>(If a b (d \<or> c)) \<or> a \<or> (d \<or> c)"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_4: "\<not>(If a b (If a b c)) \<or> a \<or> (If a b c)"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_5: "\<not>(If (\<not>a) True (\<not>(b \<or> c))) \<or> \<not>a \<or> \<not>(b \<or> c)"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_6: "\<not>(If (\<not>a) False (b \<and> c)) \<or> \<not>a \<or> (b \<and> c)"
  by (ctxt_tactic "ite_pos1")

(* Rule 66: ite_pos2 *)

lemma ite_pos2_1: "\<not>(If a b c) \<or> \<not>a \<or> b"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_2: "\<not>(If a (a \<or> c) b) \<or> \<not>a \<or> (a \<or> c)"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_3: "\<not>(If a b (d \<or> c)) \<or> \<not>a \<or> b"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_4: "\<not>(If a (If a b c) (If d b c)) \<or> \<not>a \<or> (If a b c)"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_5: "\<not>(If (\<not>a) (\<not>(b \<or> c)) True) \<or> \<not>(\<not>a) \<or> \<not>(b \<or> c)"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_6: "\<not>(If (\<not>a) (b \<and> c) False) \<or> \<not>(\<not>a) \<or> (b \<and> c)"
  by (ctxt_tactic "ite_pos2")

(* Rule 67: ite_neg1 *)

lemma ite_neg1_1: "(If a b c) \<or> a \<or> \<not>c"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_2: "(If a b (a \<or> c)) \<or> a \<or> \<not>(a \<or> c)"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_3: "(If a b (d \<or> c)) \<or> a \<or> \<not>(d \<or> c)"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_4: "(If a (If a b c) (If d b c)) \<or> a \<or> \<not>(If d b c)"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_5: "(If (\<not>a) False (b \<and> c)) \<or> \<not>a \<or> \<not>(b \<and> c)"
  by (ctxt_tactic "ite_neg1")

(* Rule 68: ite_neg2 *)

lemma ite_neg2_1: "(If a b c) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_2: "(If a b (a \<or> c)) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_3: "(If a (d \<or> c)  b) \<or> \<not>a \<or> \<not>(d \<or> c)"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_4: "(If a (If a b c) (If d b c)) \<or> \<not>a \<or> \<not>(If a b c)"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_5: "(If (\<not>a) (b \<and> c) False) \<or> \<not>(\<not>a) \<or> \<not>(b \<and> c)"
  by (ctxt_tactic "ite_neg2")

(* Rule 69: not_ite1 *)

lemma not_ite1_1: 
  assumes "\<not>(If a b c)"
  shows "a \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_ite1")

lemma not_ite1_2: 
  assumes "\<not>(If (If e d f) b c)"
  shows "(If e d f) \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_ite1")

lemma not_ite1_3: 
  assumes "\<not>(If a b (If e d f))"
  shows "a \<or> \<not>(If e d f)"
  using assms
  by (ctxt_tactic "not_ite1")

(* Rule 70: not_ite2 *)

lemma not_ite2_1: 
  assumes "\<not>(If a b c)"
  shows "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_ite2")

lemma not_ite2_2: 
  assumes "\<not>(If (If e d f) b c)"
  shows "\<not>(If e d f) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_ite2")

lemma not_ite2_3: 
  assumes "\<not>(If a b (If e d f))"
  shows "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_ite2")

(* Rule 71: connective_def *)

lemma connective_def_1: "(a \<noteq> b) = ((\<not>a \<and> b) \<or> (a \<and> \<not>b))"
  by (ctxt_tactic "connective_def")

lemma connective_def_2: "((a = c) \<noteq> b) = (((\<not>(a = c)) \<and> b) \<or> ((a = c) \<and> \<not>b))"
  by (ctxt_tactic "connective_def")

lemma connective_def_3: "(a = b) = ((a \<longrightarrow> b) \<and> (b \<longrightarrow> a))"
  by (ctxt_tactic "connective_def")

lemma connective_def_4: "(If a b c) = ((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> c))"
  by (ctxt_tactic "connective_def")

lemma connective_def_5: "(\<forall>x::'a. y) = (\<not>(\<exists>x::'a. \<not>y))"
  by (ctxt_tactic "connective_def")

lemma connective_def_6: "(\<exists>x::'a. p) = (\<not>(\<forall>x::'a. \<not>p))"
  by (ctxt_tactic "connective_def")

lemma connective_def_7: "(\<exists>(x::'a) y. (x = y)) = (\<not>(\<forall>(x::'a) y. \<not>(x = y)))"
  by (ctxt_tactic "connective_def")

lemma connective_def_8: "(\<forall>(x::'a) y. (x = y)) = (\<not>(\<exists>(x::'a) y. \<not>(x = y)))"
  by (ctxt_tactic "connective_def")

lemma connective_def_9: "(\<forall>x. x \<and> a) = (\<not>(\<exists>x. \<not>(x \<and> a)))"
  by (ctxt_tactic "connective_def")

lemma connective_def_10: "(\<forall>x y. x \<and> y) = (\<not>(\<exists>x y. \<not>(x \<and> y)))"
  by (ctxt_tactic "connective_def")

(* Rule 72: and_simplify *)

lemma and_simplify_1: "(True \<and> True) = True"
  by (ctxt_tactic "and_simplify")

lemma and_simplify_2: "(True \<and> a) = a"
  by (ctxt_tactic "and_simplify")

lemma and_simplify_3: "(True \<and> a \<and> False) = False"
  by (ctxt_tactic "and_simplify")

lemma and_simplify_4: "(True \<and> \<not>\<not>a \<and> b \<and> \<not>\<not>\<not>a) = False"
  by (ctxt_tactic "and_simplify")

(* Rule 73: or_simplify *)

lemma or_simplify_1: "(True \<or> True) = True"
  by (ctxt_tactic "or_simplify")

lemma or_simplify_2: "(True \<or> a) = True"
  by (ctxt_tactic "or_simplify")

lemma or_simplify_3: "(True \<or> a \<or> False) = True"
  by (ctxt_tactic "or_simplify")

lemma or_simplify_4: "(False \<or> \<not>\<not>a \<or> b \<or> \<not>\<not>\<not>a) = True"
  by (ctxt_tactic "or_simplify")

(* Rule 74: not_simplify *)

lemma not_simplify_1: "(\<not>False) = True"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_2: "(\<not>True) = False"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_3: "(\<not>\<not>a) = a"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_4: "(\<not>\<not>\<not>a) = (\<not>a)"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_5: "(\<not>\<not>\<not>True) = False"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_6: "(\<not>\<not>\<not>False) = True"
  by (ctxt_tactic "not_simplify")

(* Rule 75: implies_simplify *)

lemma implies_simplify_1: "((\<not>a) \<longrightarrow> \<not>b) = (b \<longrightarrow> a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_2: "False \<longrightarrow> a = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_3: "(a \<longrightarrow> True) = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_4: "True \<longrightarrow> (a = a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_5: "(a \<longrightarrow> False) = (\<not>a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_6: "(a \<longrightarrow> a) = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_7: "(\<not>a \<longrightarrow> a) = a"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_8: "(a \<longrightarrow> \<not>a) = (\<not>a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_9: "((False \<longrightarrow> a) \<longrightarrow> (\<not>a)) = (\<not>a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_10: "(False \<longrightarrow> False) = True" 
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_11: "(False \<longrightarrow> True) = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_12: "(True \<longrightarrow> False) = False"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_13: "(True \<longrightarrow> True) = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_14: "(False \<longrightarrow> \<not>False) = True" 
  by (ctxt_tactic "implies_simplify")

(* Rule 76: equiv_simplify *)

lemma equiv_simplify_1: "(\<not>b = (\<not>b)) = True"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_2: "(b = (\<not>b)) = False"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_3: "(\<not>b = b) = False"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_4: "(True = b) = b"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_5: "(b = True) = b"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_6: "(False = b) = (\<not>b)"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_7: "(False = b) = (\<not>b)"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_8: "((\<not>a) = (\<not>b)) = (a = b)"
  by (ctxt_tactic "equiv_simplify")

(* Rule 77: bool_simplify *)

lemma bool_simplify_1:
  shows "(\<not>(a \<longrightarrow> b)) = (a \<and> \<not>b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_2: 
  shows "\<not>(a \<or> b) = (\<not>a \<and> \<not>b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_3: 
  shows "\<not>(a \<and> b) = (\<not>a \<or> \<not>b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_4:
  shows "(a \<longrightarrow> (b \<longrightarrow> c)) = ((a \<and> b) \<longrightarrow> c)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_5: 
  shows "((a \<longrightarrow> b) \<longrightarrow> b) = (a \<or> b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_6:
  shows "(a \<and> (a \<longrightarrow> b)) = (a \<and> b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_7:
  shows "((a \<longrightarrow> b) \<and> a) = (a \<and> b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_8: (*associativity of \<and> on the LHS.*)
  shows "(a \<longrightarrow> b \<longrightarrow> c \<longrightarrow> d) = (a \<and> b \<and> c \<longrightarrow> d)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_9:
  shows \<open>(a \<longrightarrow> b \<longrightarrow> c \<longrightarrow> d) = ((a \<and> b) \<longrightarrow> c \<longrightarrow> d)\<close>
  by (ctxt_tactic "bool_simplify")

(* Rule 78: ac_simp *)

lemma ac_simp_1: "(b \<and> b) = b"
  by (ctxt_tactic "ac_simp")

lemma ac_simp_2: "(b \<and> a \<and> b) = (a \<and> b)"
  by (ctxt_tactic "ac_simp")

lemma ac_simp_3: "(b \<and> a \<and> b) = (a \<and> b)"
  by (ctxt_tactic "ac_simp")

lemma ac_simp_4: "(b \<and> ((a \<and> c) \<and> (d \<and> a))) = (a \<and> b \<and> c \<and> d)"
  by (ctxt_tactic "ac_simp")

(* Rule 79: ite_simplify *)
           
lemma ite_simplify_1:
  shows "(If True a b) = a"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_2:
  shows "(If False a b) = b"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_3:
  shows "(If c b b) = b"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_4:
  shows "(If (\<not>c) a b) = (If c b a)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_5:
  shows "(If c (If c a b) d) = (If c a d)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_6:
  shows "(If c a (If c b d)) = (If c a d)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_7:
  shows "(If c True False) = c"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_8:
  shows "(If c False True) = (\<not>c)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_9:
  shows "(If c True d) = (c \<or> d)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_10:
  shows "(If c a False) = (c \<and> a)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_11:
  shows "(If c False a) = (\<not>c \<and> a)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_12:
  shows "(If c a True) = (\<not>c \<or> a)"
  by (ctxt_tactic "ite_simplify")

(* Rule 80: qnt_simplify *)

lemma qnt_simplify_1:
  shows "(\<forall>x1. True) = True"
  by (ctxt_tactic "qnt_simplify")

lemma qnt_simplify_2:
  shows "(\<forall>x1 x2. True) = True"
  by (ctxt_tactic "qnt_simplify")

lemma qnt_simplify_3:
  shows "(\<forall>x1. False) = False"
  by (ctxt_tactic "qnt_simplify")

lemma qnt_simplify_4:
  shows "(\<forall>x1 x2. False) = False"
  by (ctxt_tactic "qnt_simplify")

(* Rule 82: qnt_join *)

lemma qnt_join_1:
  shows "(\<forall>x1. a) = (\<forall>x1. a)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_2:
  shows "(\<forall>x1 . (\<forall>x2. a \<and> x1)) = (\<forall>x1 x2. a \<and> x1)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_3:
  shows "(\<forall>x1 (x2::'a). (\<forall>x3 x4. (a \<and> x3 \<or> x4 \<and> x1))) = (\<forall>x1 (x2::'a) x3 x4. (a \<and> x3 \<or> x4 \<and> x1))"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_4:
  shows "(\<forall>x1 x2. (\<forall>x3 . (\<forall>x4. a))) = (\<forall>x1 x2 x3 x4. a)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_5:
  shows "(\<exists>x1. a) = (\<exists>x1. a)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_6:
  shows "(\<exists>x1 . (\<exists>x2. a \<and> x1)) = (\<exists>x1 x2. a \<and> x1)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_7:
  shows "(\<exists>x1 (x2::'a). (\<exists>x3 x4. (a \<and> x3 \<or> x4 \<and> x1))) = (\<exists>x1 (x2::'a) x3 x4. (a \<and> x3 \<or> x4 \<and> x1))"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_8:
  shows "(\<exists>x1 x2. (\<exists>x3 . (\<exists>x4. a))) = (\<forall>x1 x2 x3 x4. a)"
  by (ctxt_tactic "qnt_join")

(* Rule 83: qnt_rm_ununsed *)

lemma qnt_rm_unused_1:
  shows "(\<forall>x1. a) = a"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_2:
  shows "(\<forall>x1 x2. x2) = (\<forall>x2. x2)"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_3:
  shows "(\<forall>x1 x2 x3. x1 \<and> x3) = (\<forall>x1 x3. x1 \<and> x3)"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_4:
  shows "(\<exists>x1. a) = a"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_5:
  shows "(\<exists>x1 x2. x2) = (\<exists>x2. x2)"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_6:
  shows "(\<exists>x1 x2 x3. x1 \<and> x3) = (\<exists>x1 x3. x1 \<and> x3)"
  by (ctxt_tactic "qnt_rm_unused")

lemma
\<open>(\<forall>(v0::'A_literal_multiset_list__a__i) (v1::'Nat__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             (v5::'A_literal_multiset__a__i) (v0a::'A_literal_multiset_list__a__i) (v2a::'A_literal_multiset_list__a__i) (v3a::'A_multiset_list__a__i)
             (v4a::'A_list__a__i) (v5a::'A_literal_multiset__a__i) v1a::'Nat__a__i.
             v1a \<noteq> (size__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v0a \<or>
             v1a \<noteq> size__a__ia v2a \<or>
             v1a \<noteq> (size__a__i::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v3a \<or>
             v1a \<noteq> (size__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i) v4a \<or>
             (zero__a__ib::'Nat__a__i) = v1a \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> (less__a__i::'Nat__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> bool) v6 v1a \<or>
                    (nth__a__i::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_literal_multiset__a__i) v0a v6 =
                    (plus__a__i::'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (nth__a__i v2a v6)
                     ((image_mset__a__i::'A_a_literal_fun__a__i \<Rightarrow> 'A_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (pos__a__i::'A_a_literal_fun__a__i)
                       ((nth__a__ia::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_multiset__a__i) v3a v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1a \<or> (zero__a__i::'A_multiset__a__i) \<noteq> nth__a__ia v3a v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    \<not> (member__a__i::'A__a__i \<Rightarrow> 'A_set__a__i \<Rightarrow> bool) isabelle_internal_BOUND_VARIABLE_7618
                        ((set_mset__a__i::'A_multiset__a__i \<Rightarrow> 'A_set__a__i) (nth__a__ia v3a v6)) \<or>
                    (nth__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A__a__i) v4a v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> (eligible__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
                 (s__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i) v4a
                 (plus__a__i v5a (image_mset__a__i (neg__a__i::'A_a_literal_fun__a__i) ((mset__a__i::'A_list__a__i \<Rightarrow> 'A_multiset__a__i) v4a))) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or> (strictly_maximal_wrt__a__i::'A__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool) (nth__a__ib v4a v6) (nth__a__i v2a v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    (zero__a__ia::'A_literal_multiset__a__i) =
                    (fun_app__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) s__a__i
                     (nth__a__i v0a v6)) \<or>
             (ord_resolve__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i
                            \<Rightarrow> 'A_literal_multiset_list__a__i
                               \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_multiset_list__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
              s__a__i v0a (plus__a__i v5a (image_mset__a__i neg__a__i (mset__a__i v4a))) v3a v4a
              (plus__a__i
                ((sum_mset__a__i::'A_literal_multiset_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i)
                  ((mset__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'A_literal_multiset_multiset__a__i) v2a))
                v5a)) =
         (\<forall>(v0::'A_literal_multiset_list__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             (v5::'A_literal_multiset__a__i) v1::'Nat__a__i.
             v1 \<noteq> size__a__ia v0 \<or>
             v1 \<noteq> size__a__ia v2 \<or>
             v1 \<noteq> size__a__i v3 \<or>
             v1 \<noteq> size__a__ib v4 \<or>
             zero__a__ib = v1 \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> nth__a__i v0 v6 = plus__a__i (nth__a__i v2 v6) (image_mset__a__i pos__a__i (nth__a__ia v3 v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__i \<noteq> nth__a__ia v3 v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1 \<or>
                    \<not> member__a__i isabelle_internal_BOUND_VARIABLE_7618 (set_mset__a__i (nth__a__ia v3 v6)) \<or>
                    nth__a__ib v4 v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> eligible__a__i s__a__i v4 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> strictly_maximal_wrt__a__i (nth__a__ib v4 v6) (nth__a__i v2 v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__ia = fun_app__a__i s__a__i (nth__a__i v0 v6)) \<or>
             ord_resolve__a__i s__a__i v0 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) v3 v4 (plus__a__i (sum_mset__a__i (mset__a__ia v2)) v5)) \<close>
  by (ctxt_tactic "qnt_rm_unused")
  
lemma \<open> (\<forall>(v0::'A_literal_multiset_list__a__i) (v1::'Nat__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             (v5::'A_literal_multiset__a__i) (v0a::'A_literal_multiset_list__a__i) (v2a::'A_literal_multiset_list__a__i) (v3a::'A_multiset_list__a__i)
             (v4a::'A_list__a__i) (v5a::'A_literal_multiset__a__i) v1a::'Nat__a__i.
             v1a \<noteq> (size__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v0a \<or>
             v1a \<noteq> size__a__ia v2a \<or>
             v1a \<noteq> (size__a__i::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v3a \<or>
             v1a \<noteq> (size__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i) v4a \<or>
             (zero__a__ib::'Nat__a__i) = v1a \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> (less__a__i::'Nat__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> bool) v6 v1a \<or>
                    (nth__a__i::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_literal_multiset__a__i) v0a v6 =
                    (plus__a__i::'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (nth__a__i v2a v6)
                     ((image_mset__a__i::'A_a_literal_fun__a__i \<Rightarrow> 'A_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (pos__a__i::'A_a_literal_fun__a__i)
                       ((nth__a__ia::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_multiset__a__i) v3a v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1a \<or> (zero__a__i::'A_multiset__a__i) \<noteq> nth__a__ia v3a v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    \<not> (member__a__i::'A__a__i \<Rightarrow> 'A_set__a__i \<Rightarrow> bool) isabelle_internal_BOUND_VARIABLE_7618
                        ((set_mset__a__i::'A_multiset__a__i \<Rightarrow> 'A_set__a__i) (nth__a__ia v3a v6)) \<or>
                    (nth__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A__a__i) v4a v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> (eligible__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
                 (s__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i) v4a
                 (plus__a__i v5a (image_mset__a__i (neg__a__i::'A_a_literal_fun__a__i) ((mset__a__i::'A_list__a__i \<Rightarrow> 'A_multiset__a__i) v4a))) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or> (strictly_maximal_wrt__a__i::'A__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool) (nth__a__ib v4a v6) (nth__a__i v2a v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    (zero__a__ia::'A_literal_multiset__a__i) =
                    (fun_app__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) s__a__i
                     (nth__a__i v0a v6)) \<or>
             (ord_resolve__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i
                            \<Rightarrow> 'A_literal_multiset_list__a__i
                               \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_multiset_list__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
              s__a__i v0a (plus__a__i v5a (image_mset__a__i neg__a__i (mset__a__i v4a))) v3a v4a
              (plus__a__i
                ((sum_mset__a__i::'A_literal_multiset_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i)
                  ((mset__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'A_literal_multiset_multiset__a__i) v2a))
                v5a)) =
         (\<forall>(v0::'A_literal_multiset_list__a__i) (v1::'Nat__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             v5::'A_literal_multiset__a__i.
             v1 \<noteq> size__a__ia v0 \<or>
             v1 \<noteq> size__a__ia v2 \<or>
             v1 \<noteq> size__a__i v3 \<or>
             v1 \<noteq> size__a__ib v4 \<or>
             zero__a__ib = v1 \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> nth__a__i v0 v6 = plus__a__i (nth__a__i v2 v6) (image_mset__a__i pos__a__i (nth__a__ia v3 v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__i \<noteq> nth__a__ia v3 v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1 \<or>
                    \<not> member__a__i isabelle_internal_BOUND_VARIABLE_7618 (set_mset__a__i (nth__a__ia v3 v6)) \<or>
                    nth__a__ib v4 v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> eligible__a__i s__a__i v4 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> strictly_maximal_wrt__a__i (nth__a__ib v4 v6) (nth__a__i v2 v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__ia = fun_app__a__i s__a__i (nth__a__i v0 v6)) \<or>
             ord_resolve__a__i s__a__i v0 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) v3 v4 (plus__a__i (sum_mset__a__i (mset__a__ia v2)) v5)) \<close>
  by (ctxt_tactic "qnt_rm_unused")

lemma \<open>(\<forall>(v0::'A_literal_multiset_list__a__i) (v1::'Nat__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             (v5::'A_literal_multiset__a__i) (v0a::'A_literal_multiset_list__a__i) (v2a::'A_literal_multiset_list__a__i) (v3a::'A_multiset_list__a__i)
             (v4a::'A_list__a__i) (v5a::'A_literal_multiset__a__i) v1a::'Nat__a__i.
             v1a \<noteq> (size__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v0a \<or>
             v1a \<noteq> size__a__ia v2a \<or>
             v1a \<noteq> (size__a__i::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v3a \<or>
             v1a \<noteq> (size__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i) v4a \<or>
             (zero__a__ib::'Nat__a__i) = v1a \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> (less__a__i::'Nat__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> bool) v6 v1a \<or>
                    (nth__a__i::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_literal_multiset__a__i) v0a v6 =
                    (plus__a__i::'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (nth__a__i v2a v6)
                     ((image_mset__a__i::'A_a_literal_fun__a__i \<Rightarrow> 'A_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (pos__a__i::'A_a_literal_fun__a__i)
                       ((nth__a__ia::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_multiset__a__i) v3a v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1a \<or> (zero__a__i::'A_multiset__a__i) \<noteq> nth__a__ia v3a v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    \<not> (member__a__i::'A__a__i \<Rightarrow> 'A_set__a__i \<Rightarrow> bool) isabelle_internal_BOUND_VARIABLE_7618
                        ((set_mset__a__i::'A_multiset__a__i \<Rightarrow> 'A_set__a__i) (nth__a__ia v3a v6)) \<or>
                    (nth__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A__a__i) v4a v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> (eligible__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
                 (s__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i) v4a
                 (plus__a__i v5a (image_mset__a__i (neg__a__i::'A_a_literal_fun__a__i) ((mset__a__i::'A_list__a__i \<Rightarrow> 'A_multiset__a__i) v4a))) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or> (strictly_maximal_wrt__a__i::'A__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool) (nth__a__ib v4a v6) (nth__a__i v2a v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    (zero__a__ia::'A_literal_multiset__a__i) =
                    (fun_app__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) s__a__i
                     (nth__a__i v0a v6)) \<or>
             (ord_resolve__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i
                            \<Rightarrow> 'A_literal_multiset_list__a__i
                               \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_multiset_list__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
              s__a__i v0a (plus__a__i v5a (image_mset__a__i neg__a__i (mset__a__i v4a))) v3a v4a
              (plus__a__i
                ((sum_mset__a__i::'A_literal_multiset_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i)
                  ((mset__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'A_literal_multiset_multiset__a__i) v2a))
                v5a)) =
         (\<forall>(v0::'A_literal_multiset_list__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             (v5::'A_literal_multiset__a__i) v1::'Nat__a__i.
             v1 \<noteq> size__a__ia v0 \<or>
             v1 \<noteq> size__a__ia v2 \<or>
             v1 \<noteq> size__a__i v3 \<or>
             v1 \<noteq> size__a__ib v4 \<or>
             zero__a__ib = v1 \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> nth__a__i v0 v6 = plus__a__i (nth__a__i v2 v6) (image_mset__a__i pos__a__i (nth__a__ia v3 v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__i \<noteq> nth__a__ia v3 v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1 \<or>
                    \<not> member__a__i isabelle_internal_BOUND_VARIABLE_7618 (set_mset__a__i (nth__a__ia v3 v6)) \<or>
                    nth__a__ib v4 v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> eligible__a__i s__a__i v4 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> strictly_maximal_wrt__a__i (nth__a__ib v4 v6) (nth__a__i v2 v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__ia = fun_app__a__i s__a__i (nth__a__i v0 v6)) \<or>
             ord_resolve__a__i s__a__i v0 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) v3 v4 (plus__a__i (sum_mset__a__i (mset__a__ia v2)) v5)) \<close>
  by (ctxt_tactic "qnt_rm_unused")
lemma \<open>(\<forall>(v0::'A_literal_multiset_list__a__i) (v1::'Nat__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             (v5::'A_literal_multiset__a__i) (v0a::'A_literal_multiset_list__a__i) (v2a::'A_literal_multiset_list__a__i) (v3a::'A_multiset_list__a__i)
             (v4a::'A_list__a__i) (v5a::'A_literal_multiset__a__i) v1a::'Nat__a__i.
             v1a \<noteq> (size__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v0a \<or>
             v1a \<noteq> size__a__ia v2a \<or>
             v1a \<noteq> (size__a__i::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i) v3a \<or>
             v1a \<noteq> (size__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i) v4a \<or>
             (zero__a__ib::'Nat__a__i) = v1a \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> (less__a__i::'Nat__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> bool) v6 v1a \<or>
                    (nth__a__i::'A_literal_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_literal_multiset__a__i) v0a v6 =
                    (plus__a__i::'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (nth__a__i v2a v6)
                     ((image_mset__a__i::'A_a_literal_fun__a__i \<Rightarrow> 'A_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) (pos__a__i::'A_a_literal_fun__a__i)
                       ((nth__a__ia::'A_multiset_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A_multiset__a__i) v3a v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1a \<or> (zero__a__i::'A_multiset__a__i) \<noteq> nth__a__ia v3a v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    \<not> (member__a__i::'A__a__i \<Rightarrow> 'A_set__a__i \<Rightarrow> bool) isabelle_internal_BOUND_VARIABLE_7618
                        ((set_mset__a__i::'A_multiset__a__i \<Rightarrow> 'A_set__a__i) (nth__a__ia v3a v6)) \<or>
                    (nth__a__ib::'A_list__a__i \<Rightarrow> 'Nat__a__i \<Rightarrow> 'A__a__i) v4a v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> (eligible__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
                 (s__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i) v4a
                 (plus__a__i v5a (image_mset__a__i (neg__a__i::'A_a_literal_fun__a__i) ((mset__a__i::'A_list__a__i \<Rightarrow> 'A_multiset__a__i) v4a))) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or> (strictly_maximal_wrt__a__i::'A__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool) (nth__a__ib v4a v6) (nth__a__i v2a v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i.
                    \<not> less__a__i v6 v1a \<or>
                    (zero__a__ia::'A_literal_multiset__a__i) =
                    (fun_app__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i) s__a__i
                     (nth__a__i v0a v6)) \<or>
             (ord_resolve__a__i::'A_literal_multiset_a_literal_multiset_fun__a__i
                            \<Rightarrow> 'A_literal_multiset_list__a__i
                               \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> 'A_multiset_list__a__i \<Rightarrow> 'A_list__a__i \<Rightarrow> 'A_literal_multiset__a__i \<Rightarrow> bool)
              s__a__i v0a (plus__a__i v5a (image_mset__a__i neg__a__i (mset__a__i v4a))) v3a v4a
              (plus__a__i
                ((sum_mset__a__i::'A_literal_multiset_multiset__a__i \<Rightarrow> 'A_literal_multiset__a__i)
                  ((mset__a__ia::'A_literal_multiset_list__a__i \<Rightarrow> 'A_literal_multiset_multiset__a__i) v2a))
                v5a)) =
         (\<forall>(v0::'A_literal_multiset_list__a__i) (v1::'Nat__a__i) (v2::'A_literal_multiset_list__a__i) (v3::'A_multiset_list__a__i) (v4::'A_list__a__i)
             v5::'A_literal_multiset__a__i.
             v1 \<noteq> size__a__ia v0 \<or>
             v1 \<noteq> size__a__ia v2 \<or>
             v1 \<noteq> size__a__i v3 \<or>
             v1 \<noteq> size__a__ib v4 \<or>
             zero__a__ib = v1 \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> nth__a__i v0 v6 = plus__a__i (nth__a__i v2 v6) (image_mset__a__i pos__a__i (nth__a__ia v3 v6))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__i \<noteq> nth__a__ia v3 v6) \<or>
             \<not> (\<forall>(v6::'Nat__a__i) isabelle_internal_BOUND_VARIABLE_7618::'A__a__i.
                    \<not> less__a__i v6 v1 \<or>
                    \<not> member__a__i isabelle_internal_BOUND_VARIABLE_7618 (set_mset__a__i (nth__a__ia v3 v6)) \<or>
                    nth__a__ib v4 v6 = isabelle_internal_BOUND_VARIABLE_7618) \<or>
             \<not> eligible__a__i s__a__i v4 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> strictly_maximal_wrt__a__i (nth__a__ib v4 v6) (nth__a__i v2 v6)) \<or>
             \<not> (\<forall>v6::'Nat__a__i. \<not> less__a__i v6 v1 \<or> zero__a__ia = fun_app__a__i s__a__i (nth__a__i v0 v6)) \<or>
             ord_resolve__a__i s__a__i v0 (plus__a__i v5 (image_mset__a__i neg__a__i (mset__a__i v4))) v3 v4 (plus__a__i (sum_mset__a__i (mset__a__ia v2)) v5)) \<close>
  supply [[show_types=false]]
  by (ctxt_tactic "qnt_rm_unused")

(* Rule 83: eq_simplify *)

lemma eq_simplify_1:
  shows "(a = a) = True"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_2:
  shows "((3::int) = 3) = True"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_3:
  shows "((3::int) = 4) = False"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_4:
  shows "\<not>((3::int) = 3) = False"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_5:
  shows "((0:: int) = -1) = False"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_6:
  shows "(-1 = (0:: int)) = False"
  by (ctxt_tactic "eq_simplify")

(* Rule 85: div_simplify *)

lemma div_simplify_1:
  shows "((3::int) = 3) = True"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_2:
  shows "((3::int) = 4) = False"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_2b:
  shows "((-3::int) = 4) = False"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_3:
  shows "((3::int) div 3) = 1"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_3b:
  shows "((-3::int) div 3) = -1"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_3c:
  shows "((-3::int) div -3) = 1"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_4a:
  shows "((-20::int) div -3) = 6"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_4b:
  shows "((-21::int) div -3) = 7"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_4c:
  shows "(((178::int) div -3) = 7) = False"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_4d:
  shows "(((179::int) div -3) = 7000) = False"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_4e:
  shows "(((82388::int) div -3) = 7000) = False"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_4f:
  shows "(((82388::int) div -30000) = 7000) = False"
  by (ctxt_tactic "div_simplify")

(* Rule 86: prod_simplify *)

lemma prod_simplify_1:
  shows "(3 * 4 * 5) = (60::int)"
  by (ctxt_tactic "prod_simplify")

lemma prod_simplify_2:
  shows "(3 * 4 * 0 * x) = (0::int)"
  by (ctxt_tactic "prod_simplify")

lemma prod_simplify_3:
  shows "(3 * y * 4 * 2 * x * 5) = (120::int) * y * x"
  by (ctxt_tactic "prod_simplify")

lemma prod_simplify_4:
  shows "(1 * y * 1 * x) = (y::int) * x"
  by (ctxt_tactic "prod_simplify")

lemma prod_simplify_5:
  shows "(13 + (1 * y * 0 * x)) = (13::int) + 0"
  by (ctxt_tactic "prod_simplify")

lemma prod_simplify_6:
  shows "(2 * (2 * y * 3 * x) * 1) = (12::int) * y * x"
  by (ctxt_tactic "prod_simplify")

(* Rule 87: unary_minus_simplify *)

lemma unary_minus_simplify_1:
  shows "- (-(3 * 4 * 5)) = ((3::int) * 4 * 5)"
  by (ctxt_tactic "unary_minus_simplify")

lemma unary_minus_simplify_2:
  shows "- (-3) = (3::int)"
  by (ctxt_tactic "unary_minus_simplify")

lemma unary_minus_simplify_3:
  shows "- (- (-3)) = -(3::int)"
  by (ctxt_tactic "unary_minus_simplify")

(* Rule 88: minus_simplify *)

lemma minus_simplify_1:
  shows "x - x = (0::int)"
  by (ctxt_tactic "minus_simplify")

lemma minus_simplify_2:
  shows "x - 0 = (x::int)"
  by (ctxt_tactic "minus_simplify")

lemma minus_simplify_3:
  shows "x - 0 - x = (0::int)"
  by (ctxt_tactic "minus_simplify")

lemma minus_simplify_4:
  shows "0 - x - 0 - (-2 - 3) = -(x::int) - -5"
  by (ctxt_tactic "minus_simplify")

(* Rule 89: sum_simplify *)

lemma sum_simplify_1:
  shows "1 + 3 + 22 = (26::int)"
  by (ctxt_tactic "sum_simplify")

lemma sum_simplify_2:
  shows "1 + 3 + -4 = (0::int)"
  by (ctxt_tactic "sum_simplify")

lemma sum_simplify_3:
  shows "1 + 3 + x + -4 + (y + 0) = (0::int) + x + y"
  by (ctxt_tactic "sum_simplify")

(* Rule 90: comp_simplify *)

lemma comp_simplify_1:
  shows "(2 < (3::int)) = True"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_2:
  shows "(2 < (1::int)) = False"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_3:
  shows "(2 \<le> (3::int)) = True"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_4:
  shows "(2 \<le> (1::int)) = False"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_5:
  shows "(2 < (2::int)) = False"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_6:
  shows "(2 \<le> (2::int)) = True"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_7:
  shows "(5 \<ge> (2::int)) = ((2::int) \<le> 5)"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_8:
  shows "(3 < (12::int)) = (\<not>((12::int) \<le> 3))"
  by (ctxt_tactic "comp_simplify")

lemma comp_simplify_9:
  shows "(55 > (7::int)) = (\<not>((55::int) \<le> 7))"
  by (ctxt_tactic "comp_simplify")

(* Rule 93: distinct_elim *)

lemma distinct_elim_1: "(x \<noteq> y) = (x \<noteq> y)"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_2: "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((y::bool) \<noteq> z)) = False"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_3: "(((x::int) \<noteq> y) \<and> ((x::int) \<noteq> z) \<and> ((y::int) \<noteq> z)) = (((x::int) \<noteq> y) \<and> ((x::int) \<noteq> z) \<and> ((y::int) \<noteq> z))"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_4: "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((x::bool) \<noteq> a) \<and> ((y::bool) \<noteq> z) \<and> ((y::bool) \<noteq> a) \<and> ((z::bool) \<noteq> a)) = False"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_5:
  "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((x::bool) \<noteq> a) \<and> ((x::bool) \<noteq> b)
 \<and> ((y::bool) \<noteq> z) \<and> ((y::bool) \<noteq> a) \<and> ((y::bool) \<noteq> b)
 \<and> ((z::bool) \<noteq> a) \<and> ((z::bool) \<noteq> b)
 \<and> ((a::bool) \<noteq> b)
 ) = False"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_6:
  "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((x::bool) \<noteq> a) \<and> ((x::bool) \<noteq> b) \<and> ((x::bool) \<noteq> c)
 \<and> ((y::bool) \<noteq> z) \<and> ((y::bool) \<noteq> a) \<and> ((y::bool) \<noteq> b) \<and> ((y::bool) \<noteq> c)
 \<and> ((z::bool) \<noteq> a) \<and> ((z::bool) \<noteq> b) \<and> ((z::bool) \<noteq> c)
 \<and> ((a::bool) \<noteq> b) \<and> ((a::bool) \<noteq> c)
 \<and> ((b::bool) \<noteq> c)
 ) = False"
  by (ctxt_tactic "distinct_elim")

(* Rule 94: la_rw_eq1 *)

lemma la_rw_eq1_1:
  "(t = (u::int)) = (t \<le> u \<and> u \<le> t)"
  by (ctxt_tactic "la_rw_eq1")

lemma la_rw_eq1_2:
  "(5 = (5::int)) = (5 \<le> (5::int) \<and> 5 \<le> (5::int))"
  by (ctxt_tactic "la_rw_eq1")

lemma la_rw_eq1_3:
  "((7-2) = (5::int)) = ((7-2) \<le> (5::int) \<and> (5::int) \<le> (7-2))"
  by (ctxt_tactic "la_rw_eq1")

(* Rule 95: nary_elim *)

(* Parsing already binarizes and breaks up chains so these are basically equalities  *)

(* left-assoc *)


(* chainable operators are already transformed during parsing *)

lemma nary_elim_1:
  "(t1 = t2 \<and> t2 = t3 \<and> t3 = t4) = (t1 = t2 \<and> t2 = t3 \<and> t3 = t4)"
  by (ctxt_tactic "nary_elim")

lemma nary_elim_2:
  "(t1 = t2) = (t1 = t2)"
  by (ctxt_tactic "nary_elim")

(* Rule 96: bfun_elim *)
(*TODO Pascal: Try and improve tactic to solve these *)
(* Note: This rule is veriT only *)
lemma bfun_elim_1:
  assumes   "\<forall>v0 v1 v2.
            fun_app_b (fun_app_c (fun_app_d (follow delta) v0) v1) v2 =
            (\<exists>v3 v4 v5 v6 v7 v8 v9 v10 v11.
                v0 = fun_app_bg (sCons_j v8) v11 \<and>
                v1 = fun_app_bi (sCons_k v7) v4 \<and>
                v2 = sCons_d (fun_app_ag (fun_app_t pair_d v9) v10) v6 \<and>
                v3 = shd_c v4 \<and>
                v5 = fun_app_m fst_a (shd_a v6) \<and>
                member (fun_app_w (fun_app_p pair_b v7) (fun_app_ad (fun_app_r pair_c v8) v3)) (fun_app_dy (fun_app_dz (fun_app_ea delta v9) v10) v5) \<and>
                fun_app_b (fun_app_c (fun_app_d (follow delta) v11) v4) v6)"
  shows "\<forall>v0 v1 v2.
            fun_app_b (fun_app_c (fun_app_d (follow delta) v0) v1) v2 =
            (\<exists>v3 v4 v5 v6 v7 v9 v10 v11.
                v0 = fun_app_bg (sCons_j False) v11 \<and>
                v1 = fun_app_bi (sCons_k v7) v4 \<and>
                v2 = sCons_d (fun_app_ag (fun_app_t pair_d v9) v10) v6 \<and>
                v3 = shd_c v4 \<and>
                v5 = fun_app_m fst_a (shd_a v6) \<and>
                member (fun_app_w (fun_app_p pair_b v7) (fun_app_ad (fun_app_r pair_c False) v3)) (fun_app_dy (fun_app_dz (fun_app_ea delta v9) v10) v5) \<and>
                fun_app_b (fun_app_c (fun_app_d (follow delta) v11) v4) v6 \<or>
                v0 = fun_app_bg (sCons_j True) v11 \<and>
                v1 = fun_app_bi (sCons_k v7) v4 \<and>
                v2 = sCons_d (fun_app_ag (fun_app_t pair_d v9) v10) v6 \<and>
                v3 = shd_c v4 \<and>
                v5 = fun_app_m fst_a (shd_a v6) \<and>
                member (fun_app_w (fun_app_p pair_b v7) (fun_app_ad (fun_app_r pair_c True) v3)) (fun_app_dy (fun_app_dz (fun_app_ea delta v9) v10) v5) \<and>
                fun_app_b (fun_app_c (fun_app_d (follow delta) v11) v4) v6)"
  using assms by (ctxt_tactic "bfun_elim")

(* Rule 97: ite_intro *)
(* Note: This rule is veriT only *)
lemma ite_intro_1: "(If p a b) = ((If p a b) \<and> (If p (a = (If p a b)) (b = (If p a b))))"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_2: "(\<not>(If p a b)) = ((\<not>(If p a b)) \<and> (If p (a = (If p a b)) (b = (If p a b))))"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_3: "((If p a b) \<or> (If q c d)) = ( ((If p a b) \<or> (If q c d)) 
                                                 \<and> (If p (a = (If p a b)) (b = (If p a b))) 
                                                 \<and> (If q (c = (If q c d)) (d = (If q c d))) )"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_4: "((If p a b) \<or> ((If q c d) \<and> (If (\<not>p) b (\<not>d)))) 
                          = ( ((If p a b) \<or> ((If q c d) \<and> (If (\<not>p) b (\<not>d))))
                             \<and> (If p (a = (If p a b)) (b = (If p a b)))
                             \<and> (If q (c = (If q c d)) (d = (If q c d)))
                             \<and> (If (\<not>p) (b = (If (\<not>p) b (\<not>d))) ((\<not>d) = (If (\<not>p) b (\<not>d)))) )"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_5: "(a \<or> b) = (a \<or> b)"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_6: "(If p a b) = (If p a b)"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_7: "((If p a b) \<and> ((If q c d) \<or> (If (\<not>p) b (~d)))) 
                    = ((If p a b) \<and> ((If q c d) \<or> (If (\<not>p) b (~d))))"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_8: "((If p a b) \<or> (If q c d) \<or> (If q d a)) 
                          = ( (((If p a b) \<or> (If q c d) \<or> (If q d a)))
                              \<and> (If p (a = (If p a b)) (b = (If p a b)))
                              \<and> (If q (d = (If q d a)) (a = (If q d a))) )"
  by (ctxt_tactic "ite_intro")

lemma ite_intro_9:
  fixes dec_10 :: \<open>int \<Rightarrow> int\<close>
  shows
  \<open> (dec_10 (4 * dec_10 4) = (if 4 * dec_10 4 < 10 then 4 * dec_10 4 else dec_10 (4 * dec_10 4 - 10))) =
         (dec_10 (4 * dec_10 4) = (if 4 * dec_10 4 < 10 then 4 * dec_10 4 else dec_10 (4 * dec_10 4 - 10)) \<and>
          (if 4 * dec_10 4 < 10 then 4 * dec_10 4 = (if 4 * dec_10 4 < 10 then 4 * dec_10 4 else dec_10 (4 * dec_10 4 - 10))
           else dec_10 (4 * dec_10 4 - 10) = (if 4 * dec_10 4 < 10 then 4 * dec_10 4 else dec_10 (4 * dec_10 4 - 10)))) \<close>
  by (ctxt_tactic "ite_intro")

lemma ite_intro_10:
  shows \<open>((if t < 0 then - t else t) = cmod (complex_of_real t)) =
         (cmod (complex_of_real t) = (if t < 0 then - t else t) \<and> 
     (if t < 0 then - t = (if t < 0 then - t else t) else t = (if t < 0 then - t else t)))\<close>
  by (ctxt_tactic "ite_intro")

(* Rule 104: miniscope_distribute *)
(*Note: there isn't a solver that produces the exists case currently*)

lemma miniscope_distribute_all1:
  "(\<forall>x1::'a. a) = (\<forall>x1::'a. a)"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_all2:
  "(\<forall>x1::'a. (a \<and> b)) = ((\<forall>x1::'a. a) \<and> (\<forall>x1::'a. b))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_all3:
  "(\<forall>x1::'a. (a \<and> (b \<and> c))) = ((\<forall>x1::'a. a) \<and> (\<forall>x1::'a. b) \<and> (\<forall>x1::'a. c))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_all4:
  "(\<forall>x1 ::'a. \<forall> x2 ::'a. (a \<and> b)) = ((\<forall>x1::'a. \<forall>x2::'a. a) \<and> (\<forall>x1::'a. \<forall>x2::'a. b))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_all5:
  "(\<forall>x1::'a. ((x1 = a) \<and> b)) = ((\<forall>x1::'a. x1 = a) \<and> (\<forall>x1::'a. b))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_ex1:
  "(\<exists>x1::'a. a) = (\<exists>x1::'a. a)"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_ex2:
  "(\<exists>x1::'a. (a \<or> b)) = ((\<exists>x1::'a. a) \<or> (\<exists>x1::'a. b))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_ex3:
  "(\<exists>x1::'a. (a \<or> (b \<or> c))) = ((\<exists>x1::'a. a) \<or> (\<exists>x1::'a. b) \<or> (\<exists>x1::'a. c))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_ex4:
  "(\<exists>x1::'a. \<exists>x2 ::'a. (a \<or> b)) = ((\<exists>x1::'a. \<exists>x2::'a. a) \<or> (\<exists>x1::'a. \<exists>x2::'a. b))"
  by (ctxt_tactic "miniscope_distribute")

lemma miniscope_distribute_ex5:
  "(\<exists>x1::'a. ((x1 = a) \<or> b)) = ((\<exists>x1::'a. x1 = a) \<or> (\<exists>x1::'a. b))"
  by (ctxt_tactic "miniscope_distribute")

(* Rule 105: miniscope_split *)
(*Note: there isn't a solver that produces the exists case currently*)

lemma miniscope_split_all1:
  "(\<forall>x1::'a. a) = (\<forall>x1::'a. a)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_all2:
  "(\<forall>x1::'a. (a \<or> b)) = ((\<forall>x1::'a. a) \<or> b)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_all3:
  "(\<forall>x1::'a. \<forall>x2::'a. (a \<or> (b \<or> c))) = ((\<forall>x1::'a. a) \<or> b \<or> (\<forall>x2::'a. c))"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_all4:
  "(\<forall>x1::'a. \<forall>x2::'a. (a \<or> b)) = ((\<forall>x1::'a. \<forall>x2::'a. a) \<or> b)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_all5:
  "(\<forall>x1::'a. \<forall>x2::'a. (a \<or> b)) = (a \<or> (\<forall>x1::'a. \<forall>x2::'a. b))"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_all6:
  "(\<forall>x1::'a. ((x1 = a) \<or> b)) = ((\<forall>x1::'a. x1 = a) \<or> b)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_all7:
  "(\<forall>x1 ::'a. \<forall>x2 ::'a. (a \<or> b)) = ((\<forall>x2::'a. a) \<or> (\<forall>x1::'a. b))"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex1:
  "(\<exists>x1::'a. a) = (\<exists>x1::'a. a)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex2:
  "(\<exists>x1::'a. (a \<and> b)) = ((\<exists>x1::'a. a) \<and> b)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex3:
  "(\<exists>x1 x2::'a. (a \<and> (b \<and> c))) = ((\<exists>x1::'a. a) \<and> b \<and> (\<exists>x2::'a. c))"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex4:
  "(\<exists>x1 ::'a. \<exists>x2 ::'a. (a \<and> b)) = ((\<exists>x1::'a. \<exists>x2::'a. a) \<and> b)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex5:
  "(\<exists>x1 ::'a. \<exists>x2 ::'a. (a \<and> b)) = (a \<and> (\<exists>x1::'a. \<exists>x2::'a. b))"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex6:
  "(\<exists>x1::'a. ((x1 = a) \<and> b)) = ((\<exists>x1::'a. x1 = a) \<and> b)"
  by (ctxt_tactic "miniscope_split")

lemma miniscope_split_ex7:
  "(\<exists>x1 ::'a. \<exists>x2 ::'a. (a \<and> b)) = ((\<exists>x2::'a. a) \<and> (\<exists>x1::'a. b))"
  by (ctxt_tactic "miniscope_split")

(* Rule 106: miniscope_ite *)

lemma miniscope_split_ite1:
  "(\<forall>x1 ::'a. \<forall>x2 ::'a. (If a b c)) = (If a (\<forall>x1 ::'a. \<forall>x2 ::'a. b) (\<forall>x1 ::'a. \<forall>x2 ::'a. c))"
  by (ctxt_tactic "miniscope_ite")

lemma miniscope_split_ite2:
  "(\<forall>x1 ::'a. \<forall>x2 ::'a. (If a (P1 x1) (P2 x2))) = (If a (\<forall>x1 ::'a. \<forall>x2 ::'a. P1 x1) (\<forall>x1 ::'a. \<forall>x2 ::'a. P2 x2))"
  by (ctxt_tactic "miniscope_ite")

(* Rule 106: miniscope_or *)

lemma miniscope_or1:
"(\<forall>y. (n \<noteq> r m n \<or> a \<or>\<not> f m n y y \<or> n = y)) = ((n \<noteq> r m n) \<or> a \<or>(\<forall>y. (\<not> f m n y y \<or> n = y)))"
  by (ctxt_tactic "miniscope_or")

(*Rule : poly_simp_rel*)

lemma poly_simp_rel1:
  assumes "- 1  *  ((arg2::int) + (2::int) * (x::int) + - 1 * (mul2_sum::int) - 1) =
         - 1  * ( (arg2 + (2::int) * x + - 1 * mul2_sum) -  1)"
  shows "((arg2::int) + (2::int) * (x::int) + - 1 * (mul2_sum::int) < 1) =
         ( (arg2 + (2::int) * x + - 1 * mul2_sum) <  1)"
  using assms
  by (ctxt_tactic "poly_simp_rel")

lemma poly_simp_rel2:
  assumes "-88  *  ((arg2::int) + (2::int) * (x::int) + - 1 * (mul2_sum::int) - 1) =
        - 15  * ( (arg2 + (2::int) * x + - 1 * mul2_sum) -  1)"
  shows "((arg2::int) + (2::int) * (x::int) + - 1 * (mul2_sum::int) < 1) =
         ( (arg2 + (2::int) * x + - 1 * mul2_sum) <  1)"
  using assms
  by (ctxt_tactic "poly_simp_rel")


lemma \<open>(lift_x::int) + (3::int) = (3::int) + lift_x\<close>
  by (ctxt_tactic "poly_simp")

(*onepoint**)
experiment
begin

context
  fixes v0 :: \<open>'a :: {one}\<close>
  assumes H: \<open>v0 = 1\<close>
begin

lemma H: \<open>(v0 \<noteq> 1 \<or> v0 \<noteq> 1) = (1 \<noteq> 1)\<close>
  using H by blast

end

ML \<open>
Alethe_Replay_Methods.onepoint @{context} @{thms H[where 'a=nat]}
  @{term \<open>Trueprop ((\<forall>v0::nat. (v0 \<noteq> 1 \<or> v0 \<noteq> 1)) = ((1::nat) \<noteq> 1))\<close>}
|> Thm.prop_of
|> curry (op =) @{term \<open>Trueprop ((\<forall>v0::nat. (v0 \<noteq> 1 \<or> v0 \<noteq> 1)) = ((1::nat) \<noteq> 1))\<close>}
|> (fn x => if not x then error "failed" else ())\<close>
end


context
  fixes
LIM :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
    (\<open>(\<open>notation=\<open>infix LIM\<close>\<close>(_)/ \<midarrow>(_)/\<rightarrow> (_))\<close> [60, 0, 60] 60)
begin


context
  fixes v0 v1 :: \<open>'a\<close> and v4 v5 :: 'b
  assumes H: \<open>v0 = v1\<close> \<open>v4 = v5\<close>
begin
lemma H:
 \<open>(v0 = v1 \<and> (\<forall>v6. v1 \<noteq> v6 \<longrightarrow> v2 v6 = v3 v6) \<and> v4 = v5 \<longrightarrow> v2 \<midarrow>v0\<rightarrow> v4 = v3 \<midarrow>v1\<rightarrow> v5) =
         (v0 = v0 \<and> (\<forall>v6. v0 \<noteq> v6 \<longrightarrow> v2 v6 = v3 v6) \<and> v4 = v4 \<longrightarrow> v2 \<midarrow>v0\<rightarrow> v4 = v3 \<midarrow>v0\<rightarrow> v4)\<close>
  using H by auto
end

ML \<open>
Alethe_Replay_Methods.onepoint @{context} @{thms H}
  @{term \<open>Trueprop ((\<forall>v0 v1 v2 v3 v4 v5. v0 = v1 \<and> (\<forall>v6. v1 \<noteq> v6 \<longrightarrow> v2 v6 = v3 v6) \<and> v4 = v5 \<longrightarrow> v2 \<midarrow>v0\<rightarrow> v4 = v3 \<midarrow>v1\<rightarrow> v5) =
         (\<forall>v0 v2 v3 v4. v0 = v0 \<and> (\<forall>v6. v0 \<noteq> v6 \<longrightarrow> v2 v6 = v3 v6) \<and> v4 = v4 \<longrightarrow> v2 \<midarrow>v0\<rightarrow> v4 = v3 \<midarrow>v0\<rightarrow> v4))\<close>}
|> @{print}
|> Thm.prop_of
|> curry (op =) @{term \<open>Trueprop ((\<forall>(v0::'a) (v1::'a) (v2::'a \<Rightarrow> 'b) (v3::'a \<Rightarrow> 'b) (v4::'b) v5::'b. v0 = v1 \<and> (\<forall>v6::'a. v1 \<noteq> v6 \<longrightarrow> v2 v6 = v3 v6) \<and> v4 = v5 \<longrightarrow> v2 \<midarrow>v0\<rightarrow> v4 = v3 \<midarrow>v1\<rightarrow> v5) =
 (\<forall>(v0::'a) (v2::'a \<Rightarrow> 'b) (v3::'a \<Rightarrow> 'b) v4::'b. v0 = v0 \<and> (\<forall>v6::'a. v0 \<noteq> v6 \<longrightarrow> v2 v6 = v3 v6) \<and> v4 = v4 \<longrightarrow> v2 \<midarrow>v0\<rightarrow> v4 = v3 \<midarrow>v0\<rightarrow> v4))\<close>}
|> (fn x => if not x then error "failed" else ())\<close>

end


experiment
begin

context
  fixes v1 :: nat
begin

context
  fixes v0 :: \<open>nat\<close>
begin

lemma H: \<open>(v0 \<noteq> 0 \<or> v0 \<noteq> 0 \<or> v1 \<noteq> 1 \<or> v0 \<noteq> v1) = (0 \<noteq> 0 \<or> v1 \<noteq> 1 \<or> 0 \<noteq> v1)\<close>
  by auto

end

ML \<open>
Alethe_Replay_Methods.onepoint @{context} @{thms H}
  @{term \<open>Trueprop ((\<forall>v0. v0 \<noteq> 0 \<or> v0 \<noteq> 0 \<or> v1 \<noteq> 1 \<or> v0 \<noteq> v1) = (0 \<noteq> (0::nat) \<or> v1 \<noteq> 1 \<or> 0 \<noteq> v1))\<close>}
|> @{print}
|> Thm.prop_of
|> curry (op =) @{term \<open>Trueprop ((\<forall>v0::nat. v0 \<noteq> 0 \<or> v0 \<noteq> 0 \<or> v1 \<noteq> 1 \<or> v0 \<noteq> v1) = (0 \<noteq> (0::nat) \<or> v1 \<noteq> 1 \<or> 0 \<noteq> v1))\<close>}
|> (fn x => if not x then error "failed" else ())\<close>

end

end

experiment
begin

context
    fixes A:: "('a \<Rightarrow> 'a) set" and result_lub :: "'a set \<Rightarrow> 'a"
begin

context
  fixes v0 v1 :: 'a
  assumes H: \<open>v1 = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0}\<close>
begin

lemma H: \<open>(v1 = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<longrightarrow> v1 = NT \<or> v1 \<in> {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0}) =
         (result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<longrightarrow>
          NT = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<or> result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<in> {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0})\<close>
  using H by auto

end

ML \<open>
let
  val goal = @{term \<open>Trueprop ((\<forall>v0 v1. v1 = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<longrightarrow> v1 = NT \<or> v1 \<in> {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0}) =
         (\<forall>v0. result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<longrightarrow>
               NT = result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<or> result_lub {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0} \<in> {uua. \<exists>xa. xa \<in> A \<and> uua = xa v0}) )\<close>}
in
Alethe_Replay_Methods.onepoint @{context} @{thms H} goal
|> @{print}
|> Thm.prop_of
|> curry (op =) goal
|> (fn x => if not x then error "failed" else ())
end\<close>

end
end

(* Bind *)
experiment
begin

context
  fixes eq :: "'qt1 \<Rightarrow> 'qt1 \<Rightarrow> bool" (infix "#=" 50) and
        card_of :: "'var set \<Rightarrow> 'var rel" (\<open>(\<open>open_block notation=\<open>mixfix card_of\<close>\<close>|_|)\<close>) and
        ordLess2 :: "'var rel \<Rightarrow> 'var rel \<Rightarrow> bool" (infix \<open><o\<close> 50) and
        qGood :: "'qt1 \<Rightarrow> bool" and
        asTerm :: "'qt1 \<Rightarrow> 'qt1 set" and
     qrho qrho' :: \<open>'qt1 \<Rightarrow> 'qt1 \<Rightarrow> 'qt1 option\<close> and
     veriT_vr45 veriT_vr50 :: 'qt1
  assumes overall_assms:
    "veriT_vr45 = veriT_vr50"
begin
context
  fixes veriT_vr48' veriT_vr48 veriT_vr47 veriT_vr46 veriT_vr52 
    veriT_vr53 :: 'qt1
  assumes H:
         "veriT_vr46 = veriT_vr52"
         "veriT_vr47 = veriT_vr48'"
         "veriT_vr48 = veriT_vr53"
begin

lemma H: \<open>(qrho veriT_vr45 veriT_vr46 = Some veriT_vr47 \<and> qrho' veriT_vr45 veriT_vr46 = Some veriT_vr48 \<longrightarrow> veriT_vr47 #= veriT_vr48) =
         (Some veriT_vr48' = qrho veriT_vr50 veriT_vr52 \<and> qrho' veriT_vr50 veriT_vr52 = Some veriT_vr53 \<longrightarrow> veriT_vr48' #= veriT_vr53)\<close>
  unfolding H overall_assms by auto

end


lemma \<open>(P = Q) \<Longrightarrow> P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> Q = Q'\<close>
  by auto

ML \<open>Alethe_Replay_Methods.bind\<close>
ML \<open>
let
  val goal = @{term \<open>Trueprop ((\<forall>veriT_vr46 veriT_vr47 veriT_vr48. qrho veriT_vr45 veriT_vr46 = Some veriT_vr47 \<and> qrho' veriT_vr45 veriT_vr46 = Some veriT_vr48 \<longrightarrow> veriT_vr47 #= veriT_vr48) =
         (\<forall>veriT_vr52 veriT_vr48 veriT_vr53. Some veriT_vr48 = qrho veriT_vr50 veriT_vr52 \<and> qrho' veriT_vr50 veriT_vr52 = Some veriT_vr53 \<longrightarrow> veriT_vr48 #= veriT_vr53)  )\<close>}
in
Alethe_Replay_Methods.bind @{context} @{thms H} [
@{term \<open>Trueprop (veriT_vr52 = veriT_vr48)\<close>},
@{term \<open>Trueprop (veriT_vr48')\<close>},
@{term \<open>Trueprop (veriT_vr53)\<close>},
@{term \<open>Trueprop (veriT_vr46 = veriT_vr52)\<close>},
@{term \<open>Trueprop (veriT_vr47 = veriT_vr48)\<close>},
@{term \<open>Trueprop (veriT_vr48' = veriT_vr53)\<close>}]

 goal
|> Thm.prop_of
|> curry (op =) goal
|> (fn x => if not x then error "failed" else ())
end\<close>

end
end

(*

Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
1         assume          8         8
2         hole            0         0
3         true            1         1
4         false           1         1
5         not_not         3         3
6,7       resolution      3         3
8         tautology       1         1
9         contraction     8         8
10        subproof        0         0
--------------------------------------------
                          25        25


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
11        la_generic      2         2
12        lia_generic     1         1
13        la_disequality  4         4
14        la_totality     2         2
15        la_tautology    9         9
16        la_mult_pos     3         3
17        la_mult_neg     0         0
18        bind            0         0
19        sko_ex          0         0
20        sko_forall      0         0
--------------------------------------------
                          21        21


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
21        forall_inst     0         0
22        refl            0         0
23        trans           5         5
24        cong            3         3
25        eq_reflexive    3         3
26        eq_transitive   4         4
27        eq_congruent    3         3
28        eq_congruent_pred 2       2
29        qnt_cnf         5         4
30        and             4         4
--------------------------------------------
                          29        28


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
31        not_or          6         6
32        or              3         3
33        weakening       5         5
34        reordering      4         4
35        shuffle         15        15
36        not_and         5         5
37        xor1            4         4
38        xor2            4         4
39        not_xor         4         4
40        not_xor2        4         4
--------------------------------------------
                          54        54


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
41        implies         5         5
42        not_implies1    5         5
43        not_implies2    5         5
44        equiv1          5         5
45        equiv2          5         5
46        not_equiv1      5         5
47        not_equiv2      5         5
48        and_pos         9         9
49        and_neg         9         9
50        or_pos          7         7
--------------------------------------------
                          60        60


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
51        or_neg          12        12
52        xor_pos1        7         7
53        xor_pos2        7         7
54        xor_neg1        5         5
55        xor_neg2        5         5
56        implies_pos     6         6
57        implies_neg1    6         6
58        implies_neg2    5         5
59        equiv_pos1      5         5
60        equiv_pos2      5         5
--------------------------------------------
                          63        63


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
61        equiv_neg1      5         5
62        equiv_neg2      5         5
63        ite1            3         3
64        ite2            3         3
65        ite_pos1        6         6
66        ite_pos2        6         6
67        ite_neg1        5         5
68        ite_neg2        5         5
69        not_ite1        3         3
70        not_ite2        3         3
--------------------------------------------
                          44        44


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
71        connective_def  10        10
72        and_simplify    4         4
73        or_simplify     4         4
74        not_simplify    6         6
75        implies_simplify 9        9
76        equiv_simplify  8         8
77        bool_simplify   7         7
78        ac_simp         4         4
79        ite_simplify    12        12
80        qnt_simplify    4         4
--------------------------------------------
                          68        68


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
81        onepoint        0         0
82        qnt_join        8         8
83        qnt_rm_ununsed  6         6
84        eq_simplify     4         4
85        div_simplify    9         9
86        prod_simplify   6         6
87        unary_minus_simplify  3   3
88        minus_simplify  4         4
89        sum_simplify    3         3
90        comp_simplify   9         9
--------------------------------------------
                          52        52


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
91        let             0         0
92        bind_let        0         0
93        distinct_elim   6         6
94        la_rw_eq1       3         3
95        nary_elim       2         2
96        bfun_elim       0         0
97        ite_intro       9         9
98        bitblast_extract 0        0
99        bitblast_ult    0         0
100       bitblast_add    0         0
--------------------------------------------
                          20        20


Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
101       sym             0         0
102       not_symm        0         0
103       eq_symmetric    0         0
104       miniscope_distribute  10  10
105       miniscope_split 14        14
106       miniscope_ite   2         2
107       aci_simp        0         0
--------------------------------------------
                          26        26




Rule Nr   Name            Nr Tests  Nr Success
--------------------------------------------
Total                     462       461

*)

end