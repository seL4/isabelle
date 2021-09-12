(*  Title:      FOLP/simpdata.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Simplification data for FOLP.
*)


fun make_iff_T th = th RS @{thm P_Imp_P_iff_T};

val refl_iff_T = make_iff_T @{thm refl};

val norm_thms = [(@{thm norm_eq} RS @{thm sym}, @{thm norm_eq}),
                 (@{thm NORM_iff} RS @{thm iff_sym}, @{thm NORM_iff})];


(* Conversion into rewrite rules *)

fun mk_eq th = case Thm.concl_of th of
      _ $ \<^Const_>\<open>iff for _ _\<close> $ _ => th
    | _ $ \<^Const_>\<open>eq _ for _ _\<close> $ _ => th
    | _ $ \<^Const_>\<open>Not for _\<close> $ _ => th RS @{thm not_P_imp_P_iff_F}
    | _ => make_iff_T th;


val mksimps_pairs =
  [(\<^const_name>\<open>imp\<close>, [@{thm mp}]),
   (\<^const_name>\<open>conj\<close>, [@{thm conjunct1}, @{thm conjunct2}]),
   (\<^const_name>\<open>All\<close>, [@{thm spec}]),
   (\<^const_name>\<open>True\<close>, []),
   (\<^const_name>\<open>False\<close>, [])];

fun mk_atomize pairs =
  let fun atoms th =
        (case Thm.concl_of th of
           Const ("Trueprop", _) $ p =>  (* FIXME formal const name!? *)
             (case head_of p of
                Const(a,_) =>
                  (case AList.lookup (op =) pairs a of
                     SOME(rls) => maps atoms ([th] RL rls)
                   | NONE => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mk_rew_rules th = map mk_eq (mk_atomize mksimps_pairs th);

(*destruct function for analysing equations*)
fun dest_red(_ $ (red $ lhs $ rhs) $ _) = (red,lhs,rhs)
  | dest_red t = raise TERM("dest_red", [t]);

structure FOLP_SimpData : SIMP_DATA =
struct
  val refl_thms         = [@{thm refl}, @{thm iff_refl}]
  val trans_thms        = [@{thm trans}, @{thm iff_trans}]
  val red1              = @{thm iffD1}
  val red2              = @{thm iffD2}
  val mk_rew_rules      = mk_rew_rules
  val case_splits       = []         (*NO IF'S!*)
  val norm_thms         = norm_thms
  val subst_thms        = [@{thm subst}];
  val dest_red          = dest_red
end;

structure FOLP_Simp = SimpFun(FOLP_SimpData);

(*not a component of SIMP_DATA, but an argument of SIMP_TAC *)
val FOLP_congs =
   [@{thm all_cong}, @{thm ex_cong}, @{thm eq_cong},
    @{thm conj_cong}, @{thm disj_cong}, @{thm imp_cong},
    @{thm iff_cong}, @{thm not_cong}] @ @{thms pred_congs};

val IFOLP_rews =
   [refl_iff_T] @ @{thms conj_rews} @ @{thms disj_rews} @ @{thms not_rews} @
    @{thms imp_rews} @ @{thms iff_rews} @ @{thms quant_rews};

open FOLP_Simp;

val auto_ss = empty_ss setauto (fn ctxt => ares_tac ctxt @{thms TrueI});

val IFOLP_ss = auto_ss addcongs FOLP_congs |> fold (addrew \<^context>) IFOLP_rews;


val FOLP_rews = IFOLP_rews @ @{thms cla_rews};

val FOLP_ss = auto_ss addcongs FOLP_congs |> fold (addrew \<^context>) FOLP_rews;
