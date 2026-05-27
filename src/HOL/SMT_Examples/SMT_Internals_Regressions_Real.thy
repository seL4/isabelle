theory SMT_Internals_Regressions_Real
  imports Complex_Main
begin
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
  val rule = CVC5_Replay_Methods.cvc5_rule_of n |> @{print}
  val rule_name = rule |> Alethe_Replay_Methods.string_of_alethe_rule
  val _ = @{print}("Found tactic", rule_name)
  val _ = @{print}("args", args  )

  (*FIXME: For some reason this function gets called twice... This definitely should not be necessary*)
  val dummys = Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ (Const ("Pure.term", @{typ "prop \<Rightarrow> prop"}) $ Const ("Pure.dummy_pattern", @{typ "prop"}))

  val prems=prems
  val step_args=[]
  val context_args=[]
  val args= (if rule_name = "and_pos" andalso Option.isSome args
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


lemma arith_poly_norm1:
  shows "real_of_int (- 3 * (- 2 - (- (v0 + v1) + 1))) = 9 / 1 + - 3 / 1 * real_of_int v0 + - 3 / 1 * real_of_int v1"
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm2:
  shows "real_of_int (- 2 * (v0 - (2 + - 1 * v1))) = 4 / 1 + - 2 / 1 * real_of_int v0 + - 2 / 1 * real_of_int v1"
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm3:
  shows "real_of_int (- 1 * (- 0 - (- v0 + 1))) = 1 / 1 + - 1 / 1 * real_of_int v0 "
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm4:
  shows "- 1 / 2 * (y + (if 0 \<le> y then y else - y)) = - 1 / 2 * (y::real) + - 1 / 2 * (if 0 \<le> y then y else - y)"
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm5:
  shows "real_of_int (- 4) = - 4"
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm6:
  shows "3 / 2 * real_of_int (3 - 2 * x) = 9 / 2 + - 3 / 1 * real_of_int x"
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm7:
  shows "3 / 1 * (real_of_int (- 1 * x) - - 3 / 2) = 9 / 2 + - 3 / 1 * real_of_int x "
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm8:
  shows "- ((2 * real_of_int (int x) - 1) / 2) = 1 / 2 - real_of_int (int x) "
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm9:
  shows "d / 2 + 0 + 0 - (d::real) / 2 = 0"
  by (ctxt_tactic "poly_simp")

lemma arith_poly_norm10:
  shows "1 / 1 * (2 / 1 * (1 / 1 / (2 / 1)) * (t1 / (1 / 1 / (2 / 1))) - 2 / 1 * (1 / 1 / (2 / 1) * ((t1::real) / (1 / 1 / (2 / 1))))) =
    2 / 1 * (1 / 1 / (2 / 1)) * (t1 / (1 / 1 / (2 / 1))) + - 2 / 1 * (1 / 1 / (2 / 1) * (t1 / (1 / 1 / (2 / 1))))"
  by (ctxt_tactic "poly_simp")

context
begin
lemma arith_poly_norm11:
  shows "(2::real) / 1 *
         (2 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1))) +
          2 / 1 * (- 1 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1)))) -
          0 / 1) =
         4 / 1 * (- 1 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1)))) +
         2 / 1 * (2 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1))))"
  by (ctxt_tactic "arith_poly_norm")
end

lemma arith_poly_norm12:
  shows "- v1 = - (Numeral1 * (v1::real) / Numeral1)"
  by (ctxt_tactic "arith_poly_norm")

lemma arith_poly_norm13:
  shows "1 / 1 * (t1 - - 1 / 1 * t2) = t1 + (t2::real)"
  by (ctxt_tactic "arith_poly_norm")


lemma arith_poly_norm14:
  shows "1 / 1 * ((t1::real) - 1 / 1 / t2) = t1 + - 1 / 1 * (1 / 1 / t2)"
  by (ctxt_tactic "arith_poly_norm")


lemma miniscope_distribute1:
"(\<forall>y3. (x1 = 31 / 70 + - 48 / 35 * y3 + - 11 / 14 * y2a \<or> \<not> 31 / 6 \<le> y3 + - 29 / 3 * y2a \<or> 67 / 97 \<le> x1 + - 26 / 97 * y3) \<and>
               x1 = - 21 / 40 + 27 / 20 * y3 + - 4 / 5 * y2a \<and>
               - 23 / 56 \<le> - 1 / 1 * x1 + 11 / 14 * y3 + 33 / 28 * y2a \<and> x1 = - 81 / 76 + 63 / 76 * y3 \<and> 0 / 1 \<le> x1 + - 5 / 7 * y3 + 1 / 14 * y2a) =
         ((\<forall>y3. x1 = 31 / 70 + - 48 / 35 * y3 + - 11 / 14 * y2a \<or> \<not> 31 / 6 \<le> y3 + - 29 / 3 * y2a \<or> 67 / 97 \<le> x1 + - 26 / 97 * y3) \<and>
          (\<forall>y3. x1 = - 21 / 40 + 27 / 20 * y3 + - 4 / 5 * y2a) \<and>
          (\<forall>y3. - 23 / 56 \<le> - 1 / 1 * x1 + 11 / 14 * y3 + 33 / 28 * y2a) \<and>
          (\<forall>y3. x1 = - 81 / 76 + 63 / 76 * y3) \<and> (\<forall>y3. 0 / 1 \<le> x1 + - 5 / 7 * y3 + 1 / 14 * y2a)) "
  by (ctxt_tactic "miniscope_distribute")

lemma la_generic_4:
  shows \<open>\<not> (114976::real) powr ((2::real) / (3::real)) < (117649::real) powr ((2::real) / (3::real)) \<or>
         (10000::real) + (4::real) * (114976::real) powr ((2::real) / (3::real)) \<le> (10000::real) + (4::real) * (117649::real) powr ((2::real) / (3::real)) \<close>
  by (ctxt_tactic "la_generic" "[(1,1),(1,4)]")

(*Rule : poly_simp_rel*)

lemma poly_simp_rel:
  assumes " - 31 / 70 * (- 70 / 1 * (x1::real) + - 96 / 1 * y3a + - 55 / 1 * y2a - - 31 / 1) =
         31 / 1 * (x1 - (31 / 70 + - 48 / 35 * y3a + - 11 / 14 * y2a))"
  shows "(- 70 / 1 * x1 + - 96 / 1 * y3a + - 55 / 1 * y2a = - 31 / 1) =
    (x1 = 31 / 70 + - 48 / 35 * y3a + - 11 / 14 * y2a)"
  using assms
  by (ctxt_tactic "poly_simp_rel")

lemma poly_simp_rel3:
  assumes "15 / 8 *
         (- 8 / 3 * (q19::real) + - 13 / 3 * q20 +
          - 11 / 3 * q18 -
          - 5 / 1) =
         5 / 1 *
         (- 1 / 1 * q19 + - 13 / 8 * q20 +
          - 11 / 8 * q18 -
          - 15 / 8)"
  shows "(- 5 / 1
          \<le> - 8 / 3 * q19 + - 13 / 3 * q20 +
             - 11 / 3 * q18) =
         (- 15 / 8
          \<le> - 1 / 1 * q19 + - 13 / 8 * q20 +
             - 11 / 8 * q18)"
  using assms
  by (ctxt_tactic "poly_simp_rel")



lemma poly_simp_rel4:
  assumes " 1 / 2 * real_of_int (1 + 2 * v0 - 2 * v1) = 1 / 1 * (real_of_int (v0 + - 1 * v1) - - 1 / 2)"
  shows "(2 * v1 \<le> 1 + 2 * v0) = (- 1 / 2 \<le> real_of_int (v0 + - 1 * v1))"
  using assms
  by (ctxt_tactic "poly_simp_rel")


lemma poly_simp_rel5:
  assumes " - 1 / 1 * real_of_int (2 * lift_x - 1) = - 1 / 1 * (real_of_int (2 * lift_x) - real_of_int 1)"
  shows "(2 * lift_x = 1) = (real_of_int (2 * lift_x) = real_of_int 1)"
  using assms
  by (ctxt_tactic "poly_simp_rel")

(* Rule 85: div_simplify *)

lemma div_simplify_1:
  shows "((-3::real) / 3) = -1"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_2:
  shows "((-3::real) / -3) = 1"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_3:
  shows "((-180::real) / -6) \<noteq> 31"
  by (ctxt_tactic "div_simplify")

end