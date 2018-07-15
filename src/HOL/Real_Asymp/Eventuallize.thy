section \<open>Lifting theorems onto filters\<close>
theory Eventuallize
  imports Complex_Main
begin

text \<open>
  The following attribute and ML function lift a given theorem of the form
    @{prop "\<forall>x. A x \<longrightarrow> B x \<longrightarrow> C x"}
  to
    @{prop "eventually A F \<Longrightarrow> eventually B F \<Longrightarrow> eventually C F"} .
\<close>

ML \<open>
signature EVENTUALLIZE =
sig
val eventuallize : Proof.context -> thm -> int option -> thm
end

structure Eventuallize : EVENTUALLIZE =
struct

fun dest_All (Const (@{const_name "HOL.All"}, _) $ Abs (x, T, t)) = (x, T, t)
  | dest_All (Const (@{const_name "HOL.All"}, T) $ f) =
      ("x", T |> dest_funT |> fst |> dest_funT |> fst, f $ Bound 0)
  | dest_All t = raise TERM ("dest_All", [t])

fun strip_imp (@{term "(\<longrightarrow>)"} $ a $ b) = apfst (cons a) (strip_imp b)
  | strip_imp t = ([], t)

fun eventuallize ctxt thm n =
  let
    fun err n = raise THM ("Invalid index in eventuallize: " ^ Int.toString n, 0, [thm])
    val n_max =
      thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_All |> #3 |> strip_imp |> fst |> length
    val _ = case n of NONE => () | SOME n =>
      if n >= 0 andalso n <= n_max then () else err n
    val n = case n of SOME n => n | NONE => n_max
    fun conv n =
      if n < 2 then Conv.all_conv else Conv.arg_conv (conv (n - 1)) then_conv
        Conv.rewr_conv @{thm eq_reflection[OF imp_conjL [symmetric]]}
    val conv = Conv.arg_conv (Conv.binder_conv (K (conv n)) ctxt)
    val thm' = Conv.fconv_rule conv thm
    fun go n = if n < 2 then @{thm _} else @{thm eventually_conj} OF [@{thm _}, go (n - 1)]
  in
    @{thm eventually_rev_mp[OF _ always_eventually]} OF [go n, thm']
  end

end
\<close>

attribute_setup eventuallized = \<open>
  Scan.lift (Scan.option Parse.nat) >>
    (fn n => fn (ctxt, thm) =>
      (NONE, SOME (Eventuallize.eventuallize (Context.proof_of ctxt) thm n)))
\<close>

end