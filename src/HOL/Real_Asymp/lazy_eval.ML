signature LAZY_EVAL = sig

datatype pat = AnyPat of indexname | ConsPat of (string * pat list)

type constructor = string * int

type equation = {
    function : term, 
    thm : thm, 
    rhs : term, 
    pats : pat list
  }

type eval_ctxt' = {
    equations : equation list, 
    constructors : constructor list,
    pctxt : Proof.context, 
    facts : thm Net.net,
    verbose : bool
  }

type eval_hook = eval_ctxt' -> term -> (term * conv) option

type eval_ctxt = {
    ctxt : eval_ctxt', 
    hooks : eval_hook list
  }

val is_constructor_name : constructor list -> string -> bool
val constructor_arity : constructor list -> string -> int option

val mk_eval_ctxt : Proof.context -> constructor list -> thm list -> eval_ctxt
val add_facts : thm list -> eval_ctxt -> eval_ctxt
val get_facts : eval_ctxt -> thm list
val get_ctxt : eval_ctxt -> Proof.context
val add_hook : eval_hook -> eval_ctxt -> eval_ctxt
val get_verbose : eval_ctxt -> bool
val set_verbose : bool -> eval_ctxt -> eval_ctxt
val get_constructors : eval_ctxt -> constructor list
val set_constructors : constructor list -> eval_ctxt -> eval_ctxt

val whnf : eval_ctxt -> term -> term * conv
val match : eval_ctxt -> pat -> term -> 
  (indexname * term) list option -> (indexname * term) list option * term * conv
val match_all : eval_ctxt -> pat list -> term list -> 
  (indexname * term) list option -> (indexname * term) list option * term list * conv

end

structure Lazy_Eval : LAZY_EVAL = struct

datatype pat = AnyPat of indexname | ConsPat of (string * pat list)

type constructor = string * int

type equation = {
    function : term, 
    thm : thm, 
    rhs : term, 
    pats : pat list
  }

type eval_ctxt' = {
    equations : equation list, 
    constructors : constructor list,
    pctxt : Proof.context, 
    facts : thm Net.net,
    verbose : bool
  }

type eval_hook = eval_ctxt' -> term -> (term * conv) option

type eval_ctxt = {
    ctxt : eval_ctxt', 
    hooks : eval_hook list
  }

fun add_hook h ({hooks, ctxt} : eval_ctxt) = 
  {hooks = h :: hooks, ctxt = ctxt} : eval_ctxt

fun get_verbose {ctxt = {verbose, ...}, ...} = verbose

fun set_verbose b ({ctxt = {equations, pctxt, facts, constructors, ...}, hooks} : eval_ctxt) =
  {ctxt = {equations = equations, pctxt = pctxt, facts = facts, 
   constructors = constructors, verbose = b}, hooks = hooks}

fun get_constructors ({ctxt = {constructors, ...}, ...} : eval_ctxt) = constructors

fun set_constructors cs ({ctxt = {equations, pctxt, facts, verbose, ...}, hooks} : eval_ctxt) =
  {ctxt = {equations = equations, pctxt = pctxt, facts = facts, 
   verbose = verbose, constructors = cs}, hooks = hooks}

type constructor = string * int

val is_constructor_name = member (op = o apsnd fst)

val constructor_arity = AList.lookup op =

fun stream_pat_of_term _ (Var v) = AnyPat (fst v)
  | stream_pat_of_term constructors t =
      case strip_comb t of
        (Const (c, _), args) =>
          (case constructor_arity constructors c of
             NONE => raise TERM ("Not a valid pattern.", [t])
           | SOME n => 
               if length args = n then
                 ConsPat (c, map (stream_pat_of_term constructors) args)
               else
                 raise TERM ("Not a valid pattern.", [t]))
      | _ => raise TERM ("Not a valid pattern.", [t])

fun analyze_eq constructors thm = 
  let
    val ((f, pats), rhs) = thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> 
      apfst (strip_comb #> apsnd (map (stream_pat_of_term constructors)))
    handle TERM _ => raise THM ("Not a valid function equation.", 0, [thm])
  in 
    {function = f, thm = thm RS @{thm eq_reflection}, rhs = rhs, pats = pats} : equation
  end

fun mk_eval_ctxt ctxt (constructors : constructor list) thms : eval_ctxt = {
    ctxt = {
        equations = map (analyze_eq constructors) thms, 
        facts = Net.empty, 
        verbose = false,
        pctxt = ctxt,
        constructors = constructors
      }, 
      hooks = []
    }

fun add_facts facts' {ctxt = {equations, pctxt, facts, verbose, constructors}, hooks} =
  let
    val eq = op = o apply2 Thm.prop_of
    val facts' = 
      fold (fn thm => fn net => Net.insert_term eq (Thm.prop_of thm, thm) net
        handle Net.INSERT => net) facts' facts
  in
    {ctxt = {equations = equations, pctxt = pctxt, facts = facts', 
       verbose = verbose, constructors = constructors}, 
     hooks = hooks}
  end

val get_facts = Net.content o #facts o #ctxt

val get_ctxt = (#pctxt o #ctxt : eval_ctxt -> Proof.context)

fun find_eqs (eval_ctxt : eval_ctxt) f = 
  let
    fun eq_const (Const (c, _)) (Const (c', _)) = c = c'
      | eq_const _ _ = false
  in
    map_filter (fn eq => if eq_const f (#function eq) then SOME eq else NONE) 
      (#equations (#ctxt eval_ctxt))
  end

datatype ('a, 'b) either = Inl of 'a | Inr of 'b

fun whnf (ctxt : eval_ctxt) t =
      case whnf_aux1 ctxt (Envir.beta_norm t) of
        (t', conv) => 
          if t aconv t' then 
            (t', conv)
          else
            case whnf ctxt t' of
              (t'', conv') => (t'', conv then_conv conv')
  
and whnf_aux1 (ctxt as {hooks, ctxt = ctxt'}) t =
      case get_first (fn h => h ctxt' t) hooks of
        NONE => whnf_aux2 ctxt t
      | SOME (t', conv) => case whnf ctxt t' of (t'', conv') => 
          (t'', conv then_conv conv')
and whnf_aux2 ctxt t =
  let
    val (f, args) = strip_comb t

    fun instantiate table (Var (x, _)) = the (AList.lookup op = table x)
      | instantiate table (s $ t) = instantiate table s $ instantiate table t
      | instantiate _ t = t
    fun apply_eq {thm, rhs, pats, ...} conv args = 
      let
        val (table, args', conv') = match_all ctxt pats args (SOME [])
      in (
        case table of
          SOME _ => (
            let
              val thy = Proof_Context.theory_of (get_ctxt ctxt)
              val t' = list_comb (f, args')
              val lhs = Thm.term_of (Thm.lhs_of thm)
              val env = Pattern.match thy (lhs, t') (Vartab.empty, Vartab.empty)
              val rhs = Thm.term_of (Thm.rhs_of thm)
              val rhs = Envir.subst_term env rhs |> Envir.beta_norm
            in
              Inr (rhs, conv then_conv conv' then_conv Conv.rewr_conv thm)
            end 
              handle Pattern.MATCH => Inl (args', conv then_conv conv'))
        | NONE => Inl (args', conv then_conv conv'))
       end
    
    fun apply_eqs [] args conv = (list_comb (f, args), conv)
      | apply_eqs (eq :: ctxt) args conv =
          (case apply_eq eq conv args of
             Inr res => res
           | Inl (args', conv) => apply_eqs ctxt args' conv)

  in
    case f of
      Const (f', _) => 
        if is_constructor_name (get_constructors ctxt) f' then
          (t, Conv.all_conv)
        else
          apply_eqs (find_eqs ctxt f) args Conv.all_conv
    | _ => (t, Conv.all_conv)
  end
and match_all ctxt pats args table =
  let
    fun match_all' [] [] acc conv table = (table, rev acc, conv)
      | match_all' (_ :: pats) (arg :: args) acc conv NONE =
        match_all' pats args (arg :: acc) (Conv.fun_conv conv) NONE
      | match_all' (pat :: pats) (arg :: args) acc conv (SOME table) =
          let 
            val (table', arg', conv') = match ctxt pat arg (SOME table)
            val conv = Conv.combination_conv conv conv'
            val acc = arg' :: acc
          in
            match_all' pats args acc conv table'
          end
      | match_all' _ _ _ _ _ = raise Match
  in
    if length pats = length args then
      match_all' pats args [] Conv.all_conv table
    else
      (NONE, args, Conv.all_conv)
  end
and match _ _ t NONE = (NONE, t, Conv.all_conv)
  | match _ (AnyPat v) t (SOME table) = (SOME ((v, t) :: table), t, Conv.all_conv)
  | match ctxt (ConsPat (c, pats)) t (SOME table) =
      let 
        val (t', conv) = whnf ctxt t
        val (f, args) = strip_comb t'
      in
        case f of
          Const (c', _) => 
            if c = c' then
              case match_all ctxt pats args (SOME table) of
                (table, args', conv') => (table, list_comb (f, args'), conv then_conv conv')
            else
              (NONE, t', conv)
          | _ => (NONE, t', conv)
      end

end