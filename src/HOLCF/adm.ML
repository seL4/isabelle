(*  Title:      HOLCF/adm.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Admissibility tactic.

Checks whether adm_subst theorem is applicable to the current proof
state:

  [| cont t; adm P |] ==> adm (%x. P (t x))

"t" is instantiated with a term of chain-finite type, so that
adm_chfin can be applied:

  adm (P::'a::{chfin,pcpo} => bool)

*)

signature ADM =
sig
  val adm_tac: (int -> tactic) -> int -> tactic
end;

structure Adm: ADM =
struct


(*** find_subterms t 0 []
     returns lists of terms with the following properties:
       1. all terms in the list are disjoint subterms of t
       2. all terms contain the variable which is bound at level 0
       3. all occurences of the variable which is bound at level 0
          are "covered" by a term in the list
     a list of integers is associated with every term which describes
     the "path" leading to the subterm (required for instantiation of
     the adm_subst theorem (see functions mk_term, inst_adm_subst_thm))
***)

fun find_subterms (Bound i) lev path =
      if i = lev then [[(Bound 0, path)]]
      else []
  | find_subterms (t as (Abs (_, _, t2))) lev path =
      if filter (fn x => x<=lev)
           (add_loose_bnos (t, 0, [])) = [lev] then
        [(incr_bv (~lev, 0, t), path)]::
        (find_subterms t2 (lev+1) (0::path))
      else find_subterms t2 (lev+1) (0::path)
  | find_subterms (t as (t1 $ t2)) lev path =
      let val ts1 = find_subterms t1 lev (0::path);
          val ts2 = find_subterms t2 lev (1::path);
          fun combine [] y = []
            | combine (x::xs) ys =
                (map (fn z => x @ z) ys) @ (combine xs ys)
      in
        (if filter (fn x => x<=lev)
              (add_loose_bnos (t, 0, [])) = [lev] then
           [[(incr_bv (~lev, 0, t), path)]]
         else []) @
        (if ts1 = [] then ts2
         else if ts2 = [] then ts1
         else combine ts1 ts2)
      end
  | find_subterms _ _ _ = [];


(*** make term for instantiation of predicate "P" in adm_subst theorem ***)

fun make_term t path paths lev =
  if path mem paths then Bound lev
  else case t of
      (Abs (s, T, t1)) => Abs (s, T, make_term t1 (0::path) paths (lev+1))
    | (t1 $ t2) => (make_term t1 (0::path) paths lev) $
                   (make_term t2 (1::path) paths lev)
    | t1 => t1;


(*** check whether all terms in list are equal ***)

fun eq_terms [] = true
  | eq_terms (ts as (t, _) :: _) = forall (fn (t2, _) => t2 aconv t) ts;


(*figure out internal names*)
val chfin_pcpoS = Sign.intern_sort (sign_of HOLCF.thy) ["chfin", "pcpo"];
val cont_name = Sign.intern_const (sign_of HOLCF.thy) "cont";
val adm_name = Sign.intern_const (sign_of HOLCF.thy) "adm";


(*** check whether type of terms in list is chain finite ***)

fun is_chfin sign T params ((t, _)::_) =
  let val parTs = map snd (rev params)
  in Sign.of_sort sign (fastype_of1 (T::parTs, t), chfin_pcpoS) end;


(*** try to prove that terms in list are continuous
     if successful, add continuity theorem to list l ***)

fun prove_cont tac sign s T prems params (l, ts as ((t, _)::_)) =
  let val parTs = map snd (rev params);
       val contT = (T --> (fastype_of1 (T::parTs, t))) --> HOLogic.boolT;
       fun mk_all [] t = t
         | mk_all ((a,T)::Ts) t = (all T) $ (Abs (a, T, mk_all Ts t));
       val t = HOLogic.mk_Trueprop((Const (cont_name, contT)) $ (Abs(s, T, t)));
       val t' = mk_all params (Logic.list_implies (prems, t));
       val thm = Tactic.prove sign [] [] t' (K (tac 1));
  in (ts, thm)::l end
  handle ERROR_MESSAGE _ => l;


(*** instantiation of adm_subst theorem (a bit tricky) ***)

fun inst_adm_subst_thm state i params s T subt t paths =
  let val {sign, maxidx, ...} = rep_thm state;
      val j = maxidx+1;
      val tsig = Sign.tsig_of sign;
      val parTs = map snd (rev params);
      val rule = lift_rule (state, i) adm_subst;
      val types = the o (fst (types_sorts rule));
      val tT = types ("t", j);
      val PT = types ("P", j);
      fun mk_abs [] t = t
        | mk_abs ((a,T)::Ts) t = Abs (a, T, mk_abs Ts t);
      val tt = cterm_of sign (mk_abs (params @ [(s, T)]) subt);
      val Pt = cterm_of sign (mk_abs (params @ [(s, fastype_of1 (T::parTs, subt))])
                     (make_term t [] paths 0));
      val tye = Type.typ_match tsig (Vartab.empty, (tT, #T (rep_cterm tt)));
      val tye' = Vartab.dest (Type.typ_match tsig (tye, (PT, #T (rep_cterm Pt))));
      val ctye = map (fn (x, y) => (x, ctyp_of sign y)) tye';
      val tv = cterm_of sign (Var (("t", j), typ_subst_TVars tye' tT));
      val Pv = cterm_of sign (Var (("P", j), typ_subst_TVars tye' PT));
      val rule' = instantiate (ctye, [(tv, tt), (Pv, Pt)]) rule
  in rule' end;


(*** extract subgoal i from proof state ***)

fun nth_subgoal i thm = nth_elem (i-1, prems_of thm);


(*** the admissibility tactic ***)

fun try_dest_adm (Const _ $ (Const (name, _) $ Abs abs)) =
      if name = adm_name then Some abs else None
  | try_dest_adm _ = None;

fun adm_tac tac i state =
  state |>
  let val goali = nth_subgoal i state in
    (case try_dest_adm (Logic.strip_assums_concl goali) of
      None => no_tac
    | Some (s, T, t) =>
        let
          val sign = sign_of_thm state;
          val prems = Logic.strip_assums_hyp goali;
          val params = Logic.strip_params goali;
          val ts = find_subterms t 0 [];
          val ts' = filter eq_terms ts;
          val ts'' = filter (is_chfin sign T params) ts';
          val thms = foldl (prove_cont tac sign s T prems params) ([], ts'');
        in
          (case thms of
            ((ts as ((t', _)::_), cont_thm)::_) =>
              let
                val paths = map snd ts;
                val rule = inst_adm_subst_thm state i params s T t' t paths;
              in
                compose_tac (false, rule, 2) i THEN
                rtac cont_thm i THEN
                REPEAT (assume_tac i) THEN
                rtac adm_chfin i
              end 
          | [] => no_tac)
        end)
    end;


end;


open Adm;
