signature REAL_ASYMP_DIAG = sig

val pretty_limit : Proof.context -> term -> Pretty.T

val limit_cmd :
  Proof.context -> (Facts.ref * Token.src list) list list -> string -> string option -> unit
val limit : Proof.context -> thm list -> term -> term -> Multiseries_Expansion.limit_result

val expansion_cmd :
   Proof.context -> (Facts.ref * Token.src list) list list -> bool * int ->
     string -> string option -> unit
val expansion :
  Proof.context -> thm list -> bool * int -> term -> term -> term * Asymptotic_Basis.basis

end

structure Real_Asymp_Diag : REAL_ASYMP_DIAG = struct

open Lazy_Eval
open Multiseries_Expansion

fun pretty_limit _ (Const (@{const_name "at_top"}, _)) = Pretty.str "\<infinity>"
  | pretty_limit _ (Const (@{const_name "at_bot"}, _)) = Pretty.str "-\<infinity>"
  | pretty_limit _ (Const (@{const_name "at_infinity"}, _)) = Pretty.str "\<plusminus>\<infinity>"
  | pretty_limit ctxt (Const (@{const_name "at_within"}, _) $ c $ 
        (Const (@{const_name "greaterThan"}, _) $ _)) = 
      Pretty.block [Syntax.pretty_term ctxt c, Pretty.str "\<^sup>+"]
  | pretty_limit ctxt (Const (@{const_name "at_within"}, _) $ c $ 
        (Const (@{const_name "lessThan"}, _) $ _)) = 
      Pretty.block [Syntax.pretty_term ctxt c, Pretty.str "\<^sup>-"]
  | pretty_limit ctxt (Const (@{const_name "at_within"}, _) $ c $ Const ("UNIV", _)) = 
      Syntax.pretty_term ctxt c
  | pretty_limit ctxt (Const (@{const_name "nhds"}, _) $ c) =
      Syntax.pretty_term ctxt c
  | pretty_limit _ t = raise TERM ("pretty_limit", [t])

fun reduce_to_at_top flt t = Envir.beta_eta_contract (
    case flt of
      @{term "at_top :: real filter"} => t
    | @{term "at_bot :: real filter"} =>
        Term.betapply (@{term "%(f::real\<Rightarrow>real) x. f (-x)"}, t)
    | @{term "at_left 0 :: real filter"} =>
        Term.betapply (@{term "%(f::real\<Rightarrow>real) x. f (-inverse x)"}, t)
    | @{term "at_right 0 :: real filter"} =>
        Term.betapply (@{term "%(f::real\<Rightarrow>real) x. f (inverse x)"}, t)
    | @{term "at_within :: real => _"} $ c $ (@{term "greaterThan :: real \<Rightarrow> _"} $ c') =>
        if c aconv c' then
          Term.betapply (Term.betapply (@{term "%(f::real\<Rightarrow>real) c x. f (c + inverse x)"}, t), c)
        else
          raise TERM ("Unsupported filter for real_limit", [flt])
    | @{term "at_within :: real => _"} $ c $ (@{term "lessThan :: real \<Rightarrow> _"} $ c') =>
        if c aconv c' then
          Term.betapply (Term.betapply (@{term "%(f::real\<Rightarrow>real) c x. f (c - inverse x)"}, t), c)
        else
          raise TERM ("Unsupported filter for real_limit", [flt])
    | _ =>
        raise TERM ("Unsupported filter for real_limit", [flt]))

fun mk_uminus (@{term "uminus :: real => real"} $ c) = c
  | mk_uminus c = Term.betapply (@{term "uminus :: real => real"}, c)

fun transfer_expansion_from_at_top' flt t = Envir.beta_eta_contract (
    case flt of
      @{term "at_top :: real filter"} => t
    | @{term "at_bot :: real filter"} =>
        Term.betapply (@{term "%(f::real\<Rightarrow>real) x. f (-x)"}, t)
    | @{term "at_left 0 :: real filter"} =>
        Term.betapply (@{term "%(f::real\<Rightarrow>real) x. f (-inverse x)"}, t)
    | @{term "at_right 0 :: real filter"} =>
        Term.betapply (@{term "%(f::real\<Rightarrow>real) x. f (inverse x)"}, t)
    | @{term "at_within :: real => _"} $ c $ (@{term "greaterThan :: real \<Rightarrow> _"} $ c') =>
        if c aconv c' then
          Term.betapply (Term.betapply (@{term "%(f::real\<Rightarrow>real) c x. f (inverse (x - c))"}, t), c)
        else
          raise TERM ("Unsupported filter for real_limit", [flt])
    | @{term "at_within :: real => _"} $ c $ (@{term "lessThan :: real \<Rightarrow> _"} $ c') =>
        if c aconv c' then
          Term.betapply (Term.betapply (@{term "%(f::real\<Rightarrow>real) c x. f (inverse (c - x))"}, t), c)
        else
          raise TERM ("Unsupported filter for real_limit", [flt])
    | _ =>
        raise TERM ("Unsupported filter for real_limit", [flt]))


fun transfer_expansion_from_at_top flt =
  let
    fun go idx (t as (@{term "(powr) :: real => _"} $ 
                 (@{term "inverse :: real \<Rightarrow> _"} $ Bound n) $ e)) =
          if n = idx then
            Envir.beta_eta_contract (@{term "(powr) :: real => _"} $ Bound n $ mk_uminus e)
          else
            t
      | go idx (t as (@{term "(powr) :: real => _"} $ (@{term "uminus :: real \<Rightarrow> real"} $
              (@{term "inverse :: real \<Rightarrow> _"} $ Bound n)) $ e)) =
          if n = idx then
            Envir.beta_eta_contract (@{term "(powr) :: real => _"} $
              (mk_uminus (Bound n)) $ mk_uminus e)
          else
            t
      | go idx (t as (@{term "(powr) :: real => _"} $ (@{term "inverse :: real \<Rightarrow> _"} $ 
              (@{term "(-) :: real \<Rightarrow> _"} $ Bound n $ c)) $ e)) =
          if n = idx then
            Envir.beta_eta_contract (@{term "(powr) :: real => _"} $
              (@{term "(-) :: real => _"} $ Bound n $ c) $ mk_uminus e)
          else
            t
      | go idx (t as (@{term "(powr) :: real => _"} $ (@{term "inverse :: real \<Rightarrow> _"} $ 
              (@{term "(-) :: real \<Rightarrow> _"} $ c $ Bound n)) $ e)) =
          if n = idx then
            Envir.beta_eta_contract (@{term "(powr) :: real => _"} $
              (@{term "(-) :: real => _"} $ c $ Bound n) $ mk_uminus e)
          else
            t
      | go idx (s $ t) = go idx s $ go idx t
      | go idx (Abs (x, T, t)) = Abs (x, T, go (idx + 1) t)
      | go _ t = t
  in
    transfer_expansion_from_at_top' flt #> go (~1)
  end

fun gen_limit prep_term prep_flt prep_facts res ctxt facts t flt =
  let
    val t = prep_term ctxt t
    val flt = prep_flt ctxt flt
    val ctxt = Variable.auto_fixes t ctxt
    val t = reduce_to_at_top flt t
    val facts = prep_facts ctxt facts
    val ectxt = mk_eval_ctxt ctxt |> add_facts facts |> set_verbose true
    val (bnds, basis) = expand_term_bounds ectxt t Asymptotic_Basis.default_basis
  in
    res ctxt (limit_of_expansion_bounds ectxt (bnds, basis))
  end

fun pretty_limit_result ctxt (Exact_Limit lim) = pretty_limit ctxt lim
  | pretty_limit_result ctxt (Limit_Bounds (l, u)) =
      let
        fun pretty s (SOME l) = [Pretty.block [Pretty.str s, pretty_limit ctxt l]]
          | pretty _ NONE = []
        val ps = pretty "Lower bound: " l @ pretty "Upper bound: " u
      in
        if null ps then Pretty.str "No bounds found." else Pretty.chunks ps
      end

val limit_cmd =
  gen_limit 
    (fn ctxt => 
      Syntax.parse_term ctxt 
      #> Type.constraint @{typ "real => real"} 
      #> Syntax.check_term ctxt)
    (fn ctxt => fn flt =>
        case flt of
          NONE => @{term "at_top :: real filter"}
        | SOME flt =>
            flt
            |> Syntax.parse_term ctxt
            |> Type.constraint @{typ "real filter"}
            |> Syntax.check_term ctxt)
    (fn ctxt => flat o flat o map (map (Proof_Context.get_fact ctxt o fst)))
    (fn ctxt => pretty_limit_result ctxt #> Pretty.writeln)

val limit = gen_limit Syntax.check_term Syntax.check_term (K I) (K I)


fun gen_expansion prep_term prep_flt prep_facts res ctxt facts (n, strict) t flt =
  let
    val t = prep_term ctxt t
    val flt = prep_flt ctxt flt
    val ctxt = Variable.auto_fixes t ctxt
    val t = reduce_to_at_top flt t
    val facts = prep_facts ctxt facts
    val ectxt = mk_eval_ctxt ctxt |> add_facts facts |> set_verbose true
    val basis = Asymptotic_Basis.default_basis
    val (thm, basis) = expand_term ectxt t basis
    val (exp, error) = extract_terms (strict, n) ectxt basis (get_expansion thm)
    val exp = transfer_expansion_from_at_top flt exp
    val error =
      case error of
        SOME (L $ flt' $ f) => SOME (L $ flt' $ transfer_expansion_from_at_top flt f)
      | _ => error
    val t =
      case error of
        NONE => exp
      | SOME err =>
          Term.betapply (Term.betapply (@{term "expansion_with_remainder_term"}, exp), err)
  in
    res ctxt (t, basis)
  end

fun print_basis_elem ctxt t =
  Syntax.pretty_term (Config.put Syntax_Trans.eta_contract_raw (Config.Bool false) ctxt)
    (Envir.eta_long [] t)

val expansion_cmd =
  gen_expansion
    (fn ctxt => 
      Syntax.parse_term ctxt 
      #> Type.constraint @{typ "real => real"} 
      #> Syntax.check_term ctxt)
    (fn ctxt => fn flt =>
        case flt of
          NONE => @{term "at_top :: real filter"}
        | SOME flt =>
            flt
            |> Syntax.parse_term ctxt
            |> Type.constraint @{typ "real filter"}
            |> Syntax.check_term ctxt)
    (fn ctxt => flat o flat o map (map (Proof_Context.get_fact ctxt o fst)))
    (fn ctxt => fn (exp, basis) =>
       Pretty.writeln (Pretty.chunks (
         [Pretty.str "Expansion:",
          Pretty.indent 2 (Syntax.pretty_term ctxt exp),
          Pretty.str "Basis:"] @
            map (Pretty.indent 2 o print_basis_elem ctxt) (Asymptotic_Basis.get_basis_list basis))))

val expansion = gen_expansion Syntax.check_term (K I) (K I) (K I)

end

local 

fun parse_opts opts dflt =
  let
    val p = map (fn (s, p) => Args.$$$ s |-- Args.colon |-- p) opts
  in
    Scan.repeat (Scan.first p) >> (fn xs => fold I xs dflt)
  end

val limit_opts =
  [("limit", Parse.term >> (fn t => fn {facts, ...} => {limit = SOME t, facts = facts})),
   ("facts", Parse.and_list1 Parse.thms1 >>
     (fn thms => fn {limit, facts} => {limit = limit, facts = facts @ thms}))]

val dflt_limit_opts = {limit = NONE, facts = []}

val expansion_opts =
  [("limit", Parse.term >> (fn t => fn {terms, facts, ...} =>
     {limit = SOME t, terms = terms, facts = facts})),
   ("facts", Parse.and_list1 Parse.thms1 >>
     (fn thms => fn {limit, terms, facts} =>
       {limit = limit, terms = terms, facts = facts @ thms})),
   ("terms", Parse.nat -- Scan.optional (Args.parens (Args.$$$ "strict") >> K true) false >>
     (fn trms => fn {limit, facts, ...} => {limit = limit, terms = trms, facts = facts}))]

val dflt_expansion_opts = {limit = NONE, facts = [], terms = (3, false)}

in

val _ =
  Outer_Syntax.command @{command_keyword real_limit}
    "semi-automatically compute limits of real functions"
    ((Parse.term -- parse_opts limit_opts dflt_limit_opts) >>
    (fn (t, {limit = flt, facts = thms}) => 
      (Toplevel.keep (fn state => 
        Real_Asymp_Diag.limit_cmd (Toplevel.context_of state) thms t flt))))

val _ =
  Outer_Syntax.command @{command_keyword real_expansion}
    "semi-automatically compute expansions of real functions"
    (Parse.term -- parse_opts expansion_opts dflt_expansion_opts >> 
    (fn (t, {limit = flt, terms = n_strict, facts = thms}) => 
      (Toplevel.keep (fn state => 
        Real_Asymp_Diag.expansion_cmd (Toplevel.context_of state) thms (swap n_strict) t flt))))

end