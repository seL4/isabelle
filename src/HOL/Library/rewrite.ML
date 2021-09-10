(*  Title:      HOL/Library/rewrite.ML
    Author:     Christoph Traut, Lars Noschinski, TU Muenchen

This is a rewrite method that supports subterm-selection based on patterns.

The patterns accepted by rewrite are of the following form:
  <atom>    ::= <term> | "concl" | "asm" | "for" "(" <names> ")"
  <pattern> ::= (in <atom> | at <atom>) [<pattern>]
  <args>    ::= [<pattern>] ("to" <term>) <thms>

This syntax was clearly inspired by Gonthier's and Tassi's language of
patterns but has diverged significantly during its development.

We also allow introduction of identifiers for bound variables,
which can then be used to match arbitrary subterms inside abstractions.
*)

infix 1 then_pconv;
infix 0 else_pconv;

signature REWRITE =
sig
  type patconv = Proof.context -> Type.tyenv * (string * term) list -> cconv
  val then_pconv: patconv * patconv -> patconv
  val else_pconv: patconv * patconv -> patconv
  val abs_pconv:  patconv -> string option * typ -> patconv (*XXX*)
  val fun_pconv: patconv -> patconv
  val arg_pconv: patconv -> patconv
  val imp_pconv: patconv -> patconv
  val params_pconv: patconv -> patconv
  val forall_pconv: patconv -> string option * typ option -> patconv
  val all_pconv: patconv
  val for_pconv: patconv -> (string option * typ option) list -> patconv
  val concl_pconv: patconv -> patconv
  val asm_pconv: patconv -> patconv
  val asms_pconv: patconv -> patconv
  val judgment_pconv: patconv -> patconv
  val in_pconv: patconv -> patconv
  val match_pconv: patconv -> term * (string option * typ) list -> patconv
  val rewrs_pconv: term option -> thm list -> patconv

  datatype ('a, 'b) pattern = At | In | Term of 'a | Concl | Asm | For of 'b list

  val mk_hole: int -> typ -> term

  val rewrite_conv: Proof.context
    -> (term * (string * typ) list, string * typ option) pattern list * term option
    -> thm list
    -> conv
end

structure Rewrite : REWRITE =
struct

datatype ('a, 'b) pattern = At | In | Term of 'a | Concl | Asm | For of 'b list

exception NO_TO_MATCH

val holeN = Name.internal "_hole"

fun prep_meta_eq ctxt = Simplifier.mksimps ctxt #> map Drule.zero_var_indexes


(* holes *)

fun mk_hole i T = Var ((holeN, i), T)

fun is_hole (Var ((name, _), _)) = (name = holeN)
  | is_hole _ = false

fun is_hole_const (Const (\<^const_name>\<open>rewrite_HOLE\<close>, _)) = true
  | is_hole_const _ = false

val hole_syntax =
  let
    (* Modified variant of Term.replace_hole *)
    fun replace_hole Ts (Const (\<^const_name>\<open>rewrite_HOLE\<close>, T)) i =
          (list_comb (mk_hole i (Ts ---> T), map_range Bound (length Ts)), i + 1)
      | replace_hole Ts (Abs (x, T, t)) i =
          let val (t', i') = replace_hole (T :: Ts) t i
          in (Abs (x, T, t'), i') end
      | replace_hole Ts (t $ u) i =
          let
            val (t', i') = replace_hole Ts t i
            val (u', i'') = replace_hole Ts u i'
          in (t' $ u', i'') end
      | replace_hole _ a i = (a, i)
    fun prep_holes ts = #1 (fold_map (replace_hole []) ts 1)
  in
    Context.proof_map (Syntax_Phases.term_check 101 "hole_expansion" (K prep_holes))
    #> Proof_Context.set_mode Proof_Context.mode_pattern
  end


(* pattern conversions *)

type patconv = Proof.context -> Type.tyenv * (string * term) list -> cterm -> thm

fun (cv1 then_pconv cv2) ctxt tytenv ct = (cv1 ctxt tytenv then_conv cv2 ctxt tytenv) ct

fun (cv1 else_pconv cv2) ctxt tytenv ct = (cv1 ctxt tytenv else_conv cv2 ctxt tytenv) ct

fun raw_abs_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    Abs _ => CConv.abs_cconv (fn (x, ctxt') => cv x ctxt' tytenv) ctxt ct
  | t => raise TERM ("raw_abs_pconv", [t])

fun raw_fun_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    _ $ _ => CConv.fun_cconv (cv ctxt tytenv) ct
  | t => raise TERM ("raw_fun_pconv", [t])

fun raw_arg_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    _ $ _ => CConv.arg_cconv (cv ctxt tytenv) ct
  | t => raise TERM ("raw_arg_pconv", [t])

fun abs_pconv cv (s,T) ctxt (tyenv, ts) ct =
  let val u = Thm.term_of ct
  in
    case try (fastype_of #> dest_funT) u of
      NONE => raise TERM ("abs_pconv: no function type", [u])
    | SOME (U, _) =>
        let
          val tyenv' =
            if T = dummyT then tyenv
            else Sign.typ_match (Proof_Context.theory_of ctxt) (T, U) tyenv
          val eta_expand_cconv =
            case u of
              Abs _=> Thm.reflexive
            | _ => CConv.rewr_cconv @{thm eta_expand}
          fun add_ident NONE _ l = l
            | add_ident (SOME name) ct l = (name, Thm.term_of ct) :: l
          val abs_cv = CConv.abs_cconv (fn (ct, ctxt) => cv ctxt (tyenv', add_ident s ct ts)) ctxt
        in (eta_expand_cconv then_conv abs_cv) ct end
        handle Pattern.MATCH => raise TYPE ("abs_pconv: types don't match", [T,U], [u])
  end

fun fun_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    _ $ _ => CConv.fun_cconv (cv ctxt tytenv) ct
  | Abs (_, T, _ $ Bound 0) => abs_pconv (fun_pconv cv) (NONE, T) ctxt tytenv ct
  | t => raise TERM ("fun_pconv", [t])

local

fun arg_pconv_gen cv0 cv ctxt tytenv ct =
  case Thm.term_of ct of
    _ $ _ => cv0 (cv ctxt tytenv) ct
  | Abs (_, T, _ $ Bound 0) => abs_pconv (arg_pconv_gen cv0 cv) (NONE, T) ctxt tytenv ct
  | t => raise TERM ("arg_pconv_gen", [t])

in

fun arg_pconv ctxt = arg_pconv_gen CConv.arg_cconv ctxt
fun imp_pconv ctxt = arg_pconv_gen (CConv.concl_cconv 1) ctxt

end

(* Move to B in !!x_1 ... x_n. B. Do not eta-expand *)
fun params_pconv cv ctxt tytenv ct =
  let val pconv =
    case Thm.term_of ct of
      Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => (raw_arg_pconv o raw_abs_pconv) (fn _ => params_pconv cv)
    | Const (\<^const_name>\<open>Pure.all\<close>, _) => raw_arg_pconv (params_pconv cv)
    | _ => cv
  in pconv ctxt tytenv ct end

fun forall_pconv cv ident ctxt tytenv ct =
  case Thm.term_of ct of
    Const (\<^const_name>\<open>Pure.all\<close>, T) $ _ =>
      let
        val def_U = T |> dest_funT |> fst |> dest_funT |> fst
        val ident' = apsnd (the_default (def_U)) ident
      in arg_pconv (abs_pconv cv ident') ctxt tytenv ct end
  | t => raise TERM ("forall_pconv", [t])

fun all_pconv _ _ = Thm.reflexive

fun for_pconv cv idents ctxt tytenv ct =
  let
    fun f rev_idents (Const (\<^const_name>\<open>Pure.all\<close>, _) $ t) =
        let val (rev_idents', cv') = f rev_idents (case t of Abs (_,_,u) => u | _ => t)
        in
          case rev_idents' of
            [] => ([], forall_pconv cv' (NONE, NONE))
          | (x :: xs) => (xs, forall_pconv cv' x)
        end
      | f rev_idents _ = (rev_idents, cv)
  in
    case f (rev idents) (Thm.term_of ct) of
      ([], cv') => cv' ctxt tytenv ct
    | _ => raise CTERM ("for_pconv", [ct])
  end

fun concl_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _) $ _ => imp_pconv (concl_pconv cv) ctxt tytenv ct
  | _ => cv ctxt tytenv ct

fun asm_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _) $ _ => CConv.with_prems_cconv ~1 (cv ctxt tytenv) ct
  | t => raise TERM ("asm_pconv", [t])

fun asms_pconv cv ctxt tytenv ct =
  case Thm.term_of ct of
    (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _) $ _ =>
      ((CConv.with_prems_cconv ~1 oo cv) else_pconv imp_pconv (asms_pconv cv)) ctxt tytenv ct
  | t => raise TERM ("asms_pconv", [t])

fun judgment_pconv cv ctxt tytenv ct =
  if Object_Logic.is_judgment ctxt (Thm.term_of ct)
  then arg_pconv cv ctxt tytenv ct
  else cv ctxt tytenv ct

fun in_pconv cv ctxt tytenv ct =
  (cv else_pconv 
   raw_fun_pconv (in_pconv cv) else_pconv
   raw_arg_pconv (in_pconv cv) else_pconv
   raw_abs_pconv (fn _  => in_pconv cv))
  ctxt tytenv ct

fun replace_idents idents t =
  let
    fun subst ((n1, s)::ss) (t as Free (n2, _)) = if n1 = n2 then s else subst ss t
      | subst _ t = t
  in Term.map_aterms (subst idents) t end

fun match_pconv cv (t,fixes) ctxt (tyenv, env_ts) ct =
  let
    val t' = replace_idents env_ts t
    val thy = Proof_Context.theory_of ctxt
    val u = Thm.term_of ct

    fun descend_hole fixes (Abs (_, _, t)) =
        (case descend_hole fixes t of
          NONE => NONE
        | SOME (fix :: fixes', pos) => SOME (fixes', abs_pconv pos fix)
        | SOME ([], _) => raise Match (* less fixes than abstractions on path to hole *))
      | descend_hole fixes (t as l $ r) =
        let val (f, _) = strip_comb t
        in
          if is_hole f
          then SOME (fixes, cv)
          else
            (case descend_hole fixes l of
              SOME (fixes', pos) => SOME (fixes', fun_pconv pos)
            | NONE =>
              (case descend_hole fixes r of
                SOME (fixes', pos) => SOME (fixes', arg_pconv pos)
              | NONE => NONE))
        end
      | descend_hole fixes t =
        if is_hole t then SOME (fixes, cv) else NONE

    val to_hole = descend_hole (rev fixes) #> the_default ([], cv) #> snd
  in
    case try (Pattern.match thy (apply2 Logic.mk_term (t',u))) (tyenv, Vartab.empty) of
      NONE => raise TERM ("match_pconv: Does not match pattern", [t, t',u])
    | SOME (tyenv', _) => to_hole t ctxt (tyenv', env_ts) ct
  end

fun rewrs_pconv to thms ctxt (tyenv, env_ts) =
  let
    fun instantiate_normalize_env ctxt env thm =
      let
        val prop = Thm.prop_of thm
        val norm_type = Envir.norm_type o Envir.type_env
        val insts = Term.add_vars prop []
          |> map (fn x as (s, T) =>
              ((s, norm_type env T), Thm.cterm_of ctxt (Envir.norm_term env (Var x))))
        val tyinsts = Term.add_tvars prop []
          |> map (fn x => (x, Thm.ctyp_of ctxt (norm_type env (TVar x))))
      in Drule.instantiate_normalize (TVars.make tyinsts, Vars.make insts) thm end
    
    fun unify_with_rhs context to env thm =
      let
        val (_, rhs) = thm |> Thm.concl_of |> Logic.dest_equals
        val env' = Pattern.unify context (Logic.mk_term to, Logic.mk_term rhs) env
          handle Pattern.Unif => raise NO_TO_MATCH
      in env' end
    
    fun inst_thm_to _ (NONE, _) thm = thm
      | inst_thm_to (ctxt : Proof.context) (SOME to, env) thm =
          instantiate_normalize_env ctxt (unify_with_rhs (Context.Proof ctxt) to env thm) thm
    
    fun inst_thm ctxt idents (to, tyenv) thm =
      let
        (* Replace any identifiers with their corresponding bound variables. *)
        val maxidx = Term.maxidx_typs (map (snd o snd) (Vartab.dest tyenv)) 0
        val env = Envir.Envir {maxidx = maxidx, tenv = Vartab.empty, tyenv = tyenv}
        val maxidx = Envir.maxidx_of env |> fold Term.maxidx_term (the_list to)
        val thm' = Thm.incr_indexes (maxidx + 1) thm
      in SOME (inst_thm_to ctxt (Option.map (replace_idents idents) to, env) thm') end
      handle NO_TO_MATCH => NONE
    
  in CConv.rewrs_cconv (map_filter (inst_thm ctxt env_ts (to, tyenv)) thms) end

fun rewrite_conv ctxt (pattern, to) thms ct =
  let
    fun apply_pat At = judgment_pconv
      | apply_pat In = in_pconv
      | apply_pat Asm = params_pconv o asms_pconv
      | apply_pat Concl = params_pconv o concl_pconv
      | apply_pat (For idents) = (fn cv => for_pconv cv (map (apfst SOME) idents))
      | apply_pat (Term x) = (fn cv => match_pconv cv (apsnd (map (apfst SOME)) x))

    val cv = fold_rev apply_pat pattern

    fun distinct_prems th =
      case Seq.pull (distinct_subgoals_tac th) of
        NONE => th
      | SOME (th', _) => th'

    val rewrite = rewrs_pconv to (maps (prep_meta_eq ctxt) thms)
  in cv rewrite ctxt (Vartab.empty, []) ct |> distinct_prems end

fun rewrite_export_tac ctxt (pat, pat_ctxt) thms =
  let
    val export = case pat_ctxt of
        NONE => I
      | SOME inner => singleton (Proof_Context.export inner ctxt)
  in CCONVERSION (export o rewrite_conv ctxt pat thms) end

val _ =
  Theory.setup
  let
    fun mk_fix s = (Binding.name s, NONE, NoSyn)

    val raw_pattern : (string, binding * string option * mixfix) pattern list parser =
      let
        val sep = (Args.$$$ "at" >> K At) || (Args.$$$ "in" >> K In)
        val atom =  (Args.$$$ "asm" >> K Asm) ||
          (Args.$$$ "concl" >> K Concl) ||
          (Args.$$$ "for" |-- Args.parens (Scan.optional Parse.vars []) >> For) ||
          (Parse.term >> Term)
        val sep_atom = sep -- atom >> (fn (s,a) => [s,a])

        fun append_default [] = [Concl, In]
          | append_default (ps as Term _ :: _) = Concl :: In :: ps
          | append_default [For x, In] = [For x, Concl, In]
          | append_default (For x :: (ps as In :: Term _:: _)) = For x :: Concl :: ps
          | append_default ps = ps

      in Scan.repeats sep_atom >> (rev #> append_default) end

    fun context_lift (scan : 'a parser) f = fn (context : Context.generic, toks) =>
      let
        val (r, toks') = scan toks
        val (r', context') = Context.map_proof_result (fn ctxt => f ctxt r) context
      in (r', (context', toks' : Token.T list)) end

    fun read_fixes fixes ctxt =
      let fun read_typ (b, rawT, mx) = (b, Option.map (Syntax.read_typ ctxt) rawT, mx)
      in Proof_Context.add_fixes (map read_typ fixes) ctxt end

    fun prep_pats ctxt (ps : (string, binding * string option * mixfix) pattern list) =
      let
        fun add_constrs ctxt n (Abs (x, T, t)) =
            let
              val (x', ctxt') = yield_singleton Proof_Context.add_fixes (mk_fix x) ctxt
            in
              (case add_constrs ctxt' (n+1) t of
                NONE => NONE
              | SOME ((ctxt'', n', xs), t') =>
                  let
                    val U = Type_Infer.mk_param n []
                    val u = Type.constraint (U --> dummyT) (Abs (x, T, t'))
                  in SOME ((ctxt'', n', (x', U) :: xs), u) end)
            end
          | add_constrs ctxt n (l $ r) =
            (case add_constrs ctxt n l of
              SOME (c, l') => SOME (c, l' $ r)
            | NONE =>
              (case add_constrs ctxt n r of
                SOME (c, r') => SOME (c, l $ r')
              | NONE => NONE))
          | add_constrs ctxt n t =
            if is_hole_const t then SOME ((ctxt, n, []), t) else NONE

        fun prep (Term s) (n, ctxt) =
            let
              val t = Syntax.parse_term ctxt s
              val ((ctxt', n', bs), t') =
                the_default ((ctxt, n, []), t) (add_constrs ctxt (n+1) t)
            in (Term (t', bs), (n', ctxt')) end
          | prep (For ss) (n, ctxt) =
            let val (ns, ctxt') = read_fixes ss ctxt
            in (For ns, (n, ctxt')) end
          | prep At (n,ctxt) = (At, (n, ctxt))
          | prep In (n,ctxt) = (In, (n, ctxt))
          | prep Concl (n,ctxt) = (Concl, (n, ctxt))
          | prep Asm (n,ctxt) = (Asm, (n, ctxt))

        val (xs, (_, ctxt')) = fold_map prep ps (0, ctxt)

      in (xs, ctxt') end

    fun prep_args ctxt (((raw_pats, raw_to), raw_ths)) =
      let

        fun check_terms ctxt ps to =
          let
            fun safe_chop (0: int) xs = ([], xs)
              | safe_chop n (x :: xs) = chop (n - 1) xs |>> cons x
              | safe_chop _ _ = raise Match

            fun reinsert_pat _ (Term (_, cs)) (t :: ts) =
                let val (cs', ts') = safe_chop (length cs) ts
                in (Term (t, map dest_Free cs'), ts') end
              | reinsert_pat _ (Term _) [] = raise Match
              | reinsert_pat ctxt (For ss) ts =
                let val fixes = map (fn s => (s, Variable.default_type ctxt s)) ss
                in (For fixes, ts) end
              | reinsert_pat _ At ts = (At, ts)
              | reinsert_pat _ In ts = (In, ts)
              | reinsert_pat _ Concl ts = (Concl, ts)
              | reinsert_pat _ Asm ts = (Asm, ts)

            fun free_constr (s,T) = Type.constraint T (Free (s, dummyT))
            fun mk_free_constrs (Term (t, cs)) = t :: map free_constr cs
              | mk_free_constrs _ = []

            val ts = maps mk_free_constrs ps @ the_list to
              |> Syntax.check_terms (hole_syntax ctxt)
            val ctxt' = fold Variable.declare_term ts ctxt
            val (ps', (to', ts')) = fold_map (reinsert_pat ctxt') ps ts
              ||> (fn xs => case to of NONE => (NONE, xs) | SOME _ => (SOME (hd xs), tl xs))
            val _ = case ts' of (_ :: _) => raise Match | [] => ()
          in ((ps', to'), ctxt') end

        val (pats, ctxt') = prep_pats ctxt raw_pats

        val ths = Attrib.eval_thms ctxt' raw_ths
        val to = Option.map (Syntax.parse_term ctxt') raw_to

        val ((pats', to'), ctxt'') = check_terms ctxt' pats to

      in ((pats', ths, (to', ctxt)), ctxt'') end

    val to_parser = Scan.option ((Args.$$$ "to") |-- Parse.term)

    val subst_parser =
      let val scan = raw_pattern -- to_parser -- Parse.thms1
      in context_lift scan prep_args end
  in
    Method.setup \<^binding>\<open>rewrite\<close> (subst_parser >>
      (fn (pattern, inthms, (to, pat_ctxt)) => fn orig_ctxt =>
        SIMPLE_METHOD' (rewrite_export_tac orig_ctxt ((pattern, to), SOME pat_ctxt) inthms)))
      "single-step rewriting, allowing subterm selection via patterns."
  end
end
