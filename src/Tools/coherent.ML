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
  val verbose: bool Unsynchronized.ref
  val show_facts: bool Unsynchronized.ref
  val coherent_tac: Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end;

functor Coherent(Data: COHERENT_DATA) : COHERENT =
struct

(** misc tools **)

val verbose = Unsynchronized.ref false;

fun message f = if !verbose then tracing (f ()) else ();

datatype cl_prf =
  ClPrf of thm * (Type.tyenv * Envir.tenv) * ((indexname * typ) * term) list *
  int list * (term list * cl_prf) list;

val is_atomic = not o exists_Const (member (op =) Data.operator_names o #1);

fun rulify_elim_conv ct =
  if is_atomic (Logic.strip_imp_concl (term_of ct)) then Conv.all_conv ct
  else Conv.concl_conv (length (Logic.strip_imp_prems (term_of ct)))
    (Conv.rewr_conv (Thm.symmetric Data.atomize_elimL) then_conv
     Raw_Simplifier.rewrite true (map Thm.symmetric
       [Data.atomize_exL, Data.atomize_conjL, Data.atomize_disjL])) ct

fun rulify_elim th = Simplifier.norm_hhf (Conv.fconv_rule rulify_elim_conv th);

(* Decompose elimination rule of the form
   A1 ==> ... ==> Am ==> (!!xs1. Bs1 ==> P) ==> ... ==> (!!xsn. Bsn ==> P) ==> P
*)
fun dest_elim prop =
  let
    val prems = Logic.strip_imp_prems prop;
    val concl = Logic.strip_imp_concl prop;
    val (prems1, prems2) =
      take_suffix (fn t => Logic.strip_assums_concl t = concl) prems;
  in
    (prems1,
     if null prems2 then [([], [concl])]
     else map (fn t =>
       (map snd (Logic.strip_params t), Logic.strip_assums_hyp t)) prems2)
  end;

fun mk_rule th =
  let
    val th' = rulify_elim th;
    val (prems, cases) = dest_elim (prop_of th')
  in (th', prems, cases) end;

fun mk_dom ts = fold (fn t =>
  Typtab.map_default (fastype_of t, []) (fn us => us @ [t])) ts Typtab.empty;

val empty_env = (Vartab.empty, Vartab.empty);

(* Find matcher that makes conjunction valid in given state *)
fun valid_conj ctxt facts env [] = Seq.single (env, [])
  | valid_conj ctxt facts env (t :: ts) =
      Seq.maps (fn (u, x) => Seq.map (apsnd (cons x))
        (valid_conj ctxt facts
           (Pattern.match (Proof_Context.theory_of ctxt) (t, u) env) ts
         handle Pattern.MATCH => Seq.empty))
          (Seq.of_list (sort (int_ord o pairself snd) (Net.unify_term facts t)));

(* Instantiate variables that only occur free in conlusion *)
fun inst_extra_vars ctxt dom cs =
  let
    val vs = fold Term.add_vars (maps snd cs) [];
    fun insts [] inst = Seq.single inst
      | insts ((ixn, T) :: vs') inst = Seq.maps
          (fn t => insts vs' (((ixn, T), t) :: inst))
          (Seq.of_list (case Typtab.lookup dom T of
             NONE => error ("Unknown domain: " ^
               Syntax.string_of_typ ctxt T ^ "\nfor term(s) " ^
               commas (maps (map (Syntax.string_of_term ctxt) o snd) cs))
           | SOME ts => ts))
  in Seq.map (fn inst =>
    (inst, map (apsnd (map (subst_Vars (map (apfst fst) inst)))) cs))
      (insts vs [])
  end;

(* Check whether disjunction is valid in given state *)
fun is_valid_disj ctxt facts [] = false
  | is_valid_disj ctxt facts ((Ts, ts) :: ds) =
      let val vs = map_index (fn (i, T) => Var (("x", i), T)) Ts
      in case Seq.pull (valid_conj ctxt facts empty_env
        (map (fn t => subst_bounds (rev vs, t)) ts)) of
          SOME _ => true
        | NONE => is_valid_disj ctxt facts ds
      end;

val show_facts = Unsynchronized.ref false;

fun string_of_facts ctxt s facts = space_implode "\n"
  (s :: map (Syntax.string_of_term ctxt)
     (map fst (sort (int_ord o pairself snd) (Net.content facts)))) ^ "\n\n";

fun print_facts ctxt facts =
  if !show_facts then message (fn () => string_of_facts ctxt "Facts:" facts)
  else ();

fun valid ctxt rules goal dom facts nfacts nparams =
  let val seq = Seq.of_list rules |> Seq.maps (fn (th, ps, cs) =>
    valid_conj ctxt facts empty_env ps |> Seq.maps (fn (env as (tye, _), is) =>
      let val cs' = map (fn (Ts, ts) =>
        (map (Envir.subst_type tye) Ts, map (Envir.subst_term env) ts)) cs
      in
        inst_extra_vars ctxt dom cs' |>
          Seq.map_filter (fn (inst, cs'') =>
            if is_valid_disj ctxt facts cs'' then NONE
            else SOME (th, env, inst, is, cs''))
      end))
  in
    case Seq.pull seq of
      NONE => (tracing (string_of_facts ctxt "Countermodel found:" facts); NONE)
    | SOME ((th, env, inst, is, cs), _) =>
        if cs = [([], [goal])] then SOME (ClPrf (th, env, inst, is, []))
        else
          (case valid_cases ctxt rules goal dom facts nfacts nparams cs of
             NONE => NONE
           | SOME prfs => SOME (ClPrf (th, env, inst, is, prfs)))
  end

and valid_cases ctxt rules goal dom facts nfacts nparams [] = SOME []
  | valid_cases ctxt rules goal dom facts nfacts nparams ((Ts, ts) :: ds) =
      let
        val _ = message (fn () => "case " ^ commas (map (Syntax.string_of_term ctxt) ts));
        val params = map_index (fn (i, T) =>
          Free ("par" ^ string_of_int (nparams + i), T)) Ts;
        val ts' = map_index (fn (i, t) =>
          (subst_bounds (rev params, t), nfacts + i)) ts;
        val dom' = fold (fn (T, p) =>
          Typtab.map_default (T, []) (fn ps => ps @ [p]))
            (Ts ~~ params) dom;
        val facts' = fold (fn (t, i) => Net.insert_term op =
          (t, (t, i))) ts' facts
      in
        case valid ctxt rules goal dom' facts'
          (nfacts + length ts) (nparams + length Ts) of
          NONE => NONE
        | SOME prf => (case valid_cases ctxt rules goal dom facts nfacts nparams ds of
            NONE => NONE
          | SOME prfs => SOME ((params, prf) :: prfs))
      end;


(** proof replaying **)

fun thm_of_cl_prf thy goal asms (ClPrf (th, (tye, env), insts, is, prfs)) =
  let
    val _ = message (fn () => space_implode "\n"
      ("asms:" :: map (Display.string_of_thm_global thy) asms) ^ "\n\n");
    val th' = Drule.implies_elim_list
      (Thm.instantiate
         (map (fn (ixn, (S, T)) =>
            (Thm.ctyp_of thy (TVar ((ixn, S))), Thm.ctyp_of thy T))
               (Vartab.dest tye),
          map (fn (ixn, (T, t)) =>
            (Thm.cterm_of thy (Var (ixn, Envir.subst_type tye T)),
             Thm.cterm_of thy t)) (Vartab.dest env) @
          map (fn (ixnT, t) =>
            (Thm.cterm_of thy (Var ixnT), Thm.cterm_of thy t)) insts) th)
      (map (nth asms) is);
    val (_, cases) = dest_elim (prop_of th')
  in
    case (cases, prfs) of
      ([([], [_])], []) => th'
    | ([([], [_])], [([], prf)]) => thm_of_cl_prf thy goal (asms @ [th']) prf
    | _ => Drule.implies_elim_list
        (Thm.instantiate (Thm.match
           (Drule.strip_imp_concl (cprop_of th'), goal)) th')
        (map (thm_of_case_prf thy goal asms) (prfs ~~ cases))
  end

and thm_of_case_prf thy goal asms ((params, prf), (_, asms')) =
  let
    val cparams = map (cterm_of thy) params;
    val asms'' = map (cterm_of thy o curry subst_bounds (rev params)) asms'
  in
    Drule.forall_intr_list cparams (Drule.implies_intr_list asms''
      (thm_of_cl_prf thy goal (asms @ map Thm.assume asms'') prf))
  end;


(** external interface **)

fun coherent_tac ctxt rules = SUBPROOF (fn {prems, concl, params, context, ...} =>
  rtac (rulify_elim_conv concl RS Drule.equal_elim_rule2) 1 THEN
  SUBPROOF (fn {prems = prems', concl, context, ...} =>
    let val xs = map (term_of o #2) params @
      map (fn (_, s) => Free (s, the (Variable.default_type context s)))
        (rev (Variable.dest_fixes context))  (* FIXME !? *)
    in
      case valid context (map mk_rule (prems' @ prems @ rules)) (term_of concl)
           (mk_dom xs) Net.empty 0 0 of
         NONE => no_tac
       | SOME prf =>
           rtac (thm_of_cl_prf (Proof_Context.theory_of context) concl [] prf) 1
    end) context 1) ctxt;

val setup = Method.setup @{binding coherent}
  (Attrib.thms >> (fn rules => fn ctxt =>
      METHOD (fn facts => HEADGOAL (coherent_tac ctxt (facts @ rules)))))
    "prove coherent formula";

end;
