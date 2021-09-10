(*  Title:      Tools/coherent.ML
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Marc Bezem, Institutt for Informatikk, Universitetet i Bergen

Prover for coherent logic, see e.g.

  Marc Bezem and Thierry Coquand, Automating Coherent Logic, LPAR 2005

for a description of the algorithm.
*)

signature COHERENT_DATA =
sig
  val atomize_elimL: thm
  val atomize_exL: thm
  val atomize_conjL: thm
  val atomize_disjL: thm
  val operator_names: string list
end;

signature COHERENT =
sig
  val trace: bool Config.T
  val coherent_tac: Proof.context -> thm list -> int -> tactic
end;

functor Coherent(Data: COHERENT_DATA) : COHERENT =
struct

(** misc tools **)

val (trace, trace_setup) = Attrib.config_bool \<^binding>\<open>coherent_trace\<close> (K false);
fun cond_trace ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ();

datatype cl_prf =
  ClPrf of thm * (Type.tyenv * Envir.tenv) * ((indexname * typ) * term) list *
  int list * (term list * cl_prf) list;

val is_atomic = not o exists_Const (member (op =) Data.operator_names o #1);

fun rulify_elim_conv ctxt ct =
  if is_atomic (Logic.strip_imp_concl (Thm.term_of ct)) then Conv.all_conv ct
  else Conv.concl_conv (length (Logic.strip_imp_prems (Thm.term_of ct)))
    (Conv.rewr_conv (Thm.symmetric Data.atomize_elimL) then_conv
     Raw_Simplifier.rewrite ctxt true (map Thm.symmetric
       [Data.atomize_exL, Data.atomize_conjL, Data.atomize_disjL])) ct

fun rulify_elim ctxt th = Simplifier.norm_hhf ctxt (Conv.fconv_rule (rulify_elim_conv ctxt) th);

(* Decompose elimination rule of the form
   A1 ==> ... ==> Am ==> (!!xs1. Bs1 ==> P) ==> ... ==> (!!xsn. Bsn ==> P) ==> P
*)
fun dest_elim prop =
  let
    val prems = Logic.strip_imp_prems prop;
    val concl = Logic.strip_imp_concl prop;
    val (prems1, prems2) = chop_suffix (fn t => Logic.strip_assums_concl t = concl) prems;
  in
    (prems1,
     if null prems2 then [([], [concl])]
     else map (fn t =>
       (map snd (Logic.strip_params t), Logic.strip_assums_hyp t)) prems2)
  end;

fun mk_rule ctxt th =
  let
    val th' = rulify_elim ctxt th;
    val (prems, cases) = dest_elim (Thm.prop_of th')
  in (th', prems, cases) end;

fun mk_dom ts = fold (fn t =>
  Typtab.map_default (fastype_of t, []) (fn us => us @ [t])) ts Typtab.empty;

val empty_env = (Vartab.empty, Vartab.empty);

(* Find matcher that makes conjunction valid in given state *)
fun valid_conj _ _ env [] = Seq.single (env, [])
  | valid_conj ctxt facts env (t :: ts) =
      Seq.maps (fn (u, x) => Seq.map (apsnd (cons x))
        (valid_conj ctxt facts
           (Pattern.match (Proof_Context.theory_of ctxt) (t, u) env) ts
         handle Pattern.MATCH => Seq.empty))
          (Seq.of_list (sort (int_ord o apply2 snd) (Net.unify_term facts t)));

(* Instantiate variables that only occur free in conlusion *)
fun inst_extra_vars ctxt dom cs =
  let
    val vs = fold Term.add_vars (maps snd cs) [];
    fun insts [] inst = Seq.single inst
      | insts ((ixn, T) :: vs') inst =
          Seq.maps (fn t => insts vs' (((ixn, T), t) :: inst))
            (Seq.of_list
              (case Typtab.lookup dom T of
                NONE =>
                  error ("Unknown domain: " ^
                    Syntax.string_of_typ ctxt T ^ "\nfor term(s) " ^
                    commas (maps (map (Syntax.string_of_term ctxt) o snd) cs))
              | SOME ts => ts))
  in
    Seq.map (fn inst =>
      (inst, map (apsnd (map (subst_Vars (map (apfst fst) inst)))) cs))
        (insts vs [])
  end;

(* Check whether disjunction is valid in given state *)
fun is_valid_disj _ _ [] = false
  | is_valid_disj ctxt facts ((Ts, ts) :: ds) =
      let val vs = map_index (fn (i, T) => Var (("x", i), T)) Ts in
        (case Seq.pull (valid_conj ctxt facts empty_env
            (map (fn t => subst_bounds (rev vs, t)) ts)) of
          SOME _ => true
        | NONE => is_valid_disj ctxt facts ds)
      end;

fun string_of_facts ctxt s facts =
  Pretty.string_of (Pretty.big_list s
    (map (Syntax.pretty_term ctxt) (map fst (sort (int_ord o apply2 snd) (Net.content facts)))));

fun valid ctxt rules goal dom facts nfacts nparams =
  let
    val seq =
      Seq.of_list rules |> Seq.maps (fn (th, ps, cs) =>
        valid_conj ctxt facts empty_env ps |> Seq.maps (fn (env as (tye, _), is) =>
          let val cs' = map (fn (Ts, ts) =>
            (map (Envir.subst_type tye) Ts, map (Envir.subst_term env) ts)) cs
          in
            inst_extra_vars ctxt dom cs' |>
              Seq.map_filter (fn (inst, cs'') =>
                if is_valid_disj ctxt facts cs'' then NONE
                else SOME (th, env, inst, is, cs''))
          end));
  in
    (case Seq.pull seq of
      NONE =>
        (if Context_Position.is_visible ctxt then
          warning (string_of_facts ctxt "Countermodel found:" facts)
         else (); NONE)
    | SOME ((th, env, inst, is, cs), _) =>
        if cs = [([], [goal])] then SOME (ClPrf (th, env, inst, is, []))
        else
          (case valid_cases ctxt rules goal dom facts nfacts nparams cs of
            NONE => NONE
          | SOME prfs => SOME (ClPrf (th, env, inst, is, prfs))))
  end

and valid_cases _ _ _ _ _ _ _ [] = SOME []
  | valid_cases ctxt rules goal dom facts nfacts nparams ((Ts, ts) :: ds) =
      let
        val _ =
          cond_trace ctxt (fn () =>
            Pretty.string_of (Pretty.block
              (Pretty.str "case" :: Pretty.brk 1 ::
                Pretty.commas (map (Syntax.pretty_term ctxt) ts))));

        val ps = map_index (fn (i, T) => ("par" ^ string_of_int (nparams + i), T)) Ts;
        val (params, ctxt') = fold_map Variable.next_bound ps ctxt;
        val ts' = map_index (fn (i, t) => (subst_bounds (rev params, t), nfacts + i)) ts;
        val dom' =
          fold (fn (T, p) => Typtab.map_default (T, []) (fn ps => ps @ [p])) (Ts ~~ params) dom;
        val facts' = fold (fn (t, i) => Net.insert_term op = (t, (t, i))) ts' facts;
      in
        (case valid ctxt' rules goal dom' facts' (nfacts + length ts) (nparams + length Ts) of
          NONE => NONE
        | SOME prf =>
            (case valid_cases ctxt rules goal dom facts nfacts nparams ds of
              NONE => NONE
            | SOME prfs => SOME ((params, prf) :: prfs)))
      end;


(** proof replaying **)

fun thm_of_cl_prf ctxt goal asms (ClPrf (th, (tye, env), insts, is, prfs)) =
  let
    val _ =
      cond_trace ctxt (fn () =>
        Pretty.string_of (Pretty.big_list "asms:" (map (Thm.pretty_thm ctxt) asms)));
    val instT = map (fn (ixn, (S, T)) => ((ixn, S), Thm.ctyp_of ctxt T)) (Vartab.dest tye);
    val inst =
      map (fn (ixn, (T, t)) =>
        ((ixn, Envir.subst_type tye T), Thm.cterm_of ctxt t)) (Vartab.dest env) @
      map (fn (ixnT, t) => (ixnT, Thm.cterm_of ctxt t)) insts;
    val th' =
      Drule.implies_elim_list
        (Thm.instantiate (TVars.make instT, Vars.make inst) th)
        (map (nth asms) is);
    val (_, cases) = dest_elim (Thm.prop_of th');
  in
    (case (cases, prfs) of
      ([([], [_])], []) => th'
    | ([([], [_])], [([], prf)]) => thm_of_cl_prf ctxt goal (asms @ [th']) prf
    | _ =>
        Drule.implies_elim_list
          (Thm.instantiate (Thm.match
             (Drule.strip_imp_concl (Thm.cprop_of th'), goal)) th')
          (map (thm_of_case_prf ctxt goal asms) (prfs ~~ cases)))
  end

and thm_of_case_prf ctxt goal asms ((params, prf), (_, asms')) =
  let
    val cparams = map (Thm.cterm_of ctxt) params;
    val asms'' = map (Thm.cterm_of ctxt o curry subst_bounds (rev params)) asms';
    val (prems'', ctxt') = fold_map Thm.assume_hyps asms'' ctxt;
  in
    Drule.forall_intr_list cparams
      (Drule.implies_intr_list asms'' (thm_of_cl_prf ctxt' goal (asms @ prems'') prf))
  end;


(** external interface **)

fun coherent_tac ctxt rules = SUBPROOF (fn {prems, concl, params, context = ctxt', ...} =>
  resolve_tac ctxt' [rulify_elim_conv ctxt' concl RS Drule.equal_elim_rule2] 1 THEN
  SUBPROOF (fn {prems = prems', concl, context = ctxt'', ...} =>
    let
      val xs =
        map (Thm.term_of o #2) params @
        map (fn (_, s) => Free (s, the (Variable.default_type ctxt'' s)))
          (rev (Variable.dest_fixes ctxt''))  (* FIXME !? *)
    in
      (case
        valid ctxt'' (map (mk_rule ctxt'') (prems' @ prems @ rules)) (Thm.term_of concl)
          (mk_dom xs) Net.empty 0 0 of
        NONE => no_tac
      | SOME prf => resolve_tac ctxt'' [thm_of_cl_prf ctxt'' concl [] prf] 1)
    end) ctxt' 1) ctxt;

val _ = Theory.setup
  (trace_setup #>
   Method.setup \<^binding>\<open>coherent\<close>
    (Attrib.thms >> (fn rules => fn ctxt =>
        METHOD (fn facts => HEADGOAL (coherent_tac ctxt (facts @ rules)))))
      "prove coherent formula");

end;
