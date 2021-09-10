(*  Title:      HOL/Library/cconv.ML
    Author:     Christoph Traut, Lars Noschinski, TU Muenchen

FIXME!?
*)

infix 1 then_cconv
infix 0 else_cconv

type cconv = conv

signature BASIC_CCONV =
sig
  val then_cconv: cconv * cconv -> cconv
  val else_cconv: cconv * cconv -> cconv
  val CCONVERSION: cconv -> int -> tactic
end

signature CCONV =
sig
  include BASIC_CCONV
  val no_cconv: cconv
  val all_cconv: cconv
  val first_cconv: cconv list -> cconv
  val abs_cconv: (cterm * Proof.context -> cconv) -> Proof.context -> cconv
  val combination_cconv: cconv -> cconv -> cconv
  val comb_cconv: cconv -> cconv
  val arg_cconv: cconv -> cconv
  val fun_cconv: cconv -> cconv
  val arg1_cconv: cconv -> cconv
  val fun2_cconv: cconv -> cconv
  val rewr_cconv: thm -> cconv
  val rewrs_cconv: thm list -> cconv
  val params_cconv: int -> (Proof.context -> cconv) -> Proof.context -> cconv
  val prems_cconv: int -> cconv -> cconv
  val with_prems_cconv: int -> cconv -> cconv
  val concl_cconv: int -> cconv -> cconv
  val fconv_rule: cconv -> thm -> thm
  val gconv_rule: cconv -> int -> thm -> thm
end

structure CConv : CCONV =
struct

val concl_lhs_of = Thm.cprop_of #> Drule.strip_imp_concl #> Thm.dest_equals_lhs
val concl_rhs_of = Thm.cprop_of #> Drule.strip_imp_concl #> Thm.dest_equals_rhs

fun transitive th1 th2 = Drule.transitive_thm OF [th1, th2]

val combination_thm =
  let
    val fg = \<^cprop>\<open>f :: 'a :: {} \<Rightarrow> 'b :: {} \<equiv> g\<close>
    val st = \<^cprop>\<open>s :: 'a :: {} \<equiv> t\<close>
    val thm = Thm.combination (Thm.assume fg) (Thm.assume st)
      |> Thm.implies_intr st
      |> Thm.implies_intr fg
  in Drule.export_without_context thm end

fun abstract_rule_thm n =
  let
    val eq = \<^cprop>\<open>\<And>x :: 'a :: {}. (s :: 'a \<Rightarrow> 'b :: {}) x \<equiv> t x\<close>
    val x = \<^cterm>\<open>x :: 'a :: {}\<close>
    val thm = eq
      |> Thm.assume
      |> Thm.forall_elim x
      |> Thm.abstract_rule n x
      |> Thm.implies_intr eq
  in Drule.export_without_context thm end

val no_cconv = Conv.no_conv
val all_cconv = Conv.all_conv

fun (cv1 else_cconv cv2) ct =
  (cv1 ct
    handle THM _ => cv2 ct
      | CTERM _ => cv2 ct
      | TERM _ => cv2 ct
      | TYPE _ => cv2 ct)

fun (cv1 then_cconv cv2) ct =
  let
    val eq1 = cv1 ct
    val eq2 = cv2 (concl_rhs_of eq1)
  in
    if Thm.is_reflexive eq1 then eq2
    else if Thm.is_reflexive eq2 then eq1
    else transitive eq1 eq2
  end

fun first_cconv cvs = fold_rev (curry op else_cconv) cvs no_cconv

fun rewr_cconv rule ct =
  let
    val rule1 = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule
    val lhs = concl_lhs_of rule1
    val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1
    val rule3 = Thm.instantiate (Thm.match (lhs, ct)) rule2
                handle Pattern.MATCH => raise CTERM ("rewr_cconv", [lhs, ct])
    val concl = rule3 |> Thm.cprop_of |> Drule.strip_imp_concl
    val rule4 =
      if Thm.dest_equals_lhs concl aconvc ct then rule3
      else let val ceq = Thm.dest_fun2 concl
           in rule3 RS Thm.trivial (Thm.mk_binop ceq ct (Thm.dest_equals_rhs concl)) end
  in
    transitive rule4 (Thm.beta_conversion true (concl_rhs_of rule4))
  end

fun rewrs_cconv rules = first_cconv (map rewr_cconv rules)

fun combination_cconv cv1 cv2 cterm =
  let val (l, r) = Thm.dest_comb cterm
  in combination_thm OF [cv1 l, cv2 r] end

fun comb_cconv cv = combination_cconv cv cv

fun fun_cconv conversion =
  combination_cconv conversion all_cconv

fun arg_cconv conversion =
  combination_cconv all_cconv conversion

fun abs_cconv cv ctxt ct =
  (case Thm.term_of ct of
     Abs (x, _, _) =>
       let
         (* Instantiate the rule properly and apply it to the eq theorem. *)
         fun abstract_rule u v eq =
           let
             (* Take a variable v and an equality theorem of form:
                  P1 \<Longrightarrow> ... \<Longrightarrow> Pn \<Longrightarrow> L v \<equiv> R v
                And build a term of form:
                  \<And>v. (\<lambda>x. L x) v \<equiv> (\<lambda>x. R x) v *)
             fun mk_concl var eq =
               let
                 val certify = Thm.cterm_of ctxt
                 fun abs term = (Term.lambda var term) $ var
                 fun equals_cong f t =
                   Logic.dest_equals t
                   |> (fn (a, b) => (f a, f b))
                   |> Logic.mk_equals
               in
                 Thm.concl_of eq
                 |> equals_cong abs
                 |> Logic.all var |> certify
               end
             val rule = abstract_rule_thm x
             val inst = Thm.match (Drule.cprems_of rule |> hd, mk_concl (Thm.term_of v) eq)
           in
             (Drule.instantiate_normalize inst rule OF
               [Drule.generalize (Names.empty, Names.make_set [u]) eq])
             |> Drule.zero_var_indexes
           end

         (* Destruct the abstraction and apply the conversion. *)
         val (u, ctxt') = yield_singleton Variable.variant_fixes Name.uu ctxt
         val (v, ct') = Thm.dest_abs (SOME u) ct
         val eq = cv (v, ctxt') ct'
       in
         if Thm.is_reflexive eq
         then all_cconv ct
         else abstract_rule u v eq
       end
   | _ => raise CTERM ("abs_cconv", [ct]))

val arg1_cconv = fun_cconv o arg_cconv
val fun2_cconv = fun_cconv o fun_cconv

(* conversions on HHF rules *)

(*rewrite B in \<And>x1 ... xn. B*)
fun params_cconv n cv ctxt ct =
  if n <> 0 andalso Logic.is_all (Thm.term_of ct)
  then arg_cconv (abs_cconv (params_cconv (n - 1) cv o #2) ctxt) ct
  else cv ctxt ct

(* TODO: This code behaves not exactly like Conv.prems_cconv does.
         Fix this! *)
(*rewrite the A's in A1 \<Longrightarrow> ... \<Longrightarrow> An \<Longrightarrow> B*)
fun prems_cconv 0 cv ct = cv ct
  | prems_cconv n cv ct =
      (case ct |> Thm.term_of of
        (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _) $ _ =>
          ((if n = 1 then fun_cconv else I) o arg_cconv) (prems_cconv (n-1) cv) ct
      | _ =>  cv ct)

fun inst_imp_cong ct =
  Thm.instantiate (TVars.empty, Vars.make [((("A", 0), propT), ct)]) Drule.imp_cong

(*rewrite B in A1 \<Longrightarrow> ... \<Longrightarrow> An \<Longrightarrow> B*)
fun concl_cconv 0 cv ct = cv ct
  | concl_cconv n cv ct =
      (case try Thm.dest_implies ct of
        NONE => cv ct
      | SOME (A,B) => (concl_cconv (n-1) cv B) RS inst_imp_cong A)

(* Rewrites A in A \<Longrightarrow> A1 \<Longrightarrow> An \<Longrightarrow> B.
   The premises of the resulting theorem assume A1, ..., An
   *)
fun with_prems_cconv n cv ct =
  let
    fun strip_prems 0 As B = (As, B)
      | strip_prems i As B =
          case try Thm.dest_implies B of
            NONE => (As, B)
          | SOME (A,B) => strip_prems (i - 1) (A::As) B
    val (prem, (prems, concl)) = ct |> Thm.dest_implies ||> strip_prems n [] 
    val rewr_imp_concl =
      Thm.instantiate (TVars.empty, Vars.make [((("C", 0), propT), concl)]) @{thm rewr_imp}
    val th1 = cv prem RS rewr_imp_concl
    val nprems = Thm.nprems_of th1
    fun inst_cut_rl ct =
      Thm.instantiate (TVars.empty, Vars.make [((("psi", 0), propT), ct)]) cut_rl
    fun f p th = (th RS inst_cut_rl p)
      |> Conv.fconv_rule (Conv.concl_conv nprems (Conv.rewr_conv @{thm imp_cong_eq}))
  in fold f prems th1 end

(*forward conversion, cf. FCONV_RULE in LCF*)
fun fconv_rule cv th =
  let
    val eq = cv (Thm.cprop_of th)
  in
    if Thm.is_reflexive eq then th
    else th COMP (Thm.permute_prems 0 (Thm.nprems_of eq) (eq RS Drule.equal_elim_rule1))
  end

(*goal conversion*)
fun gconv_rule cv i th =
  (case try (Thm.cprem_of th) i of
    SOME ct =>
      let
        val eq = cv ct

        (* Drule.with_subgoal assumes that there are no new premises generated
           and thus rotates the premises wrongly. *)
        fun with_subgoal i f thm =
          let
            val num_prems = Thm.nprems_of thm
            val rotate_to_front = rotate_prems (i - 1)
            fun rotate_back thm = rotate_prems (1 - i + num_prems - Thm.nprems_of thm) thm
          in
            thm |> rotate_to_front |> f |> rotate_back
          end
      in
        if Thm.is_reflexive eq then th
        else with_subgoal i (fconv_rule (arg1_cconv (K eq))) th
      end
  | NONE => raise THM ("gconv_rule", i, [th]))

(* Conditional conversions as tactics. *)
fun CCONVERSION cv i st = Seq.single (gconv_rule cv i st)
  handle THM _ => Seq.empty
       | CTERM _ => Seq.empty
       | TERM _ => Seq.empty
       | TYPE _ => Seq.empty

end

structure Basic_CConv: BASIC_CCONV = CConv
open Basic_CConv
