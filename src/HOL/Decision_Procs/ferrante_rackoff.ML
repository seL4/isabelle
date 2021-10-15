(* Title:      HOL/Decision_Procs/ferrante_rackoff.ML
   Author:     Amine Chaieb, TU Muenchen

Ferrante and Rackoff's algorithm for quantifier elimination in dense
linear orders.  Proof-synthesis and tactic.
*)

signature FERRANTE_RACKOFF =
sig
  val dlo_conv: Proof.context -> conv
  val dlo_tac: Proof.context -> int -> tactic
end;

structure FerranteRackoff: FERRANTE_RACKOFF =
struct

open Ferrante_Rackoff_Data;
open Conv;

type entry = {minf: thm list, pinf: thm list, nmi: thm list, npi: thm list,
   ld: thm list, qe: thm, atoms : cterm list} *
  {isolate_conv: cterm list -> cterm -> thm,
                 whatis : cterm -> cterm -> ord,
                 simpset : simpset};

fun get_p1 th =
  funpow 2 (Thm.dest_arg o snd o Thm.dest_abs_global)
    (funpow 2 Thm.dest_arg (Thm.cprop_of th)) |> Thm.dest_arg

fun ferrack_conv ctxt
   (entr as ({minf = minf, pinf = pinf, nmi = nmi, npi = npi,
              ld = ld, qe = qe, atoms = atoms},
             {isolate_conv = icv, whatis = wi, simpset = simpset}):entry) =
let
 fun uset (vars as (x::vs)) p = case Thm.term_of p of
   \<^Const_>\<open>HOL.conj for _ _\<close> =>
     let
       val ((b,l),r) = Thm.dest_comb p |>> Thm.dest_comb
       val (lS,lth) = uset vars l  val (rS, rth) = uset vars r
     in (lS@rS, Drule.binop_cong_rule b lth rth) end
 | \<^Const_>\<open>HOL.disj for _ _\<close> =>
     let
       val ((b,l),r) = Thm.dest_comb p |>> Thm.dest_comb
       val (lS,lth) = uset vars l  val (rS, rth) = uset vars r
     in (lS@rS, Drule.binop_cong_rule b lth rth) end
 | _ =>
    let
      val th = icv vars p
      val p' = Thm.rhs_of th
      val c = wi x p'
      val S = (if member (op =) [Lt, Le, Eq] c then single o Thm.dest_arg
               else if member (op =) [Gt, Ge] c then single o Thm.dest_arg1
               else if c = NEq then single o Thm.dest_arg o Thm.dest_arg
               else K []) p'
    in (S,th) end

 val ((p1_v,p2_v),(mp1_v,mp2_v)) =
   funpow 2 (Thm.dest_arg o snd o Thm.dest_abs_global)
     (funpow 4 Thm.dest_arg (Thm.cprop_of (hd minf)))
   |> Thm.dest_binop |> apply2 Thm.dest_binop |> apfst (apply2 Thm.dest_fun)
   |> apply2 (apply2 (dest_Var o Thm.term_of))

 fun myfwd (th1, th2, th3, th4, th5) p1 p2
      [(th_1,th_2,th_3,th_4,th_5), (th_1',th_2',th_3',th_4',th_5')] =
  let
   val (mp1, mp2) = (get_p1 th_1, get_p1 th_1')
   val (pp1, pp2) = (get_p1 th_2, get_p1 th_2')
   fun fw mi th th' th'' =
     let
      val th0 = if mi then
           Drule.instantiate_normalize (TVars.empty, Vars.make [(p1_v, p1),(p2_v, p2),(mp1_v, mp1), (mp2_v, mp2)]) th
        else Drule.instantiate_normalize (TVars.empty, Vars.make [(p1_v, p1),(p2_v, p2),(mp1_v, pp1), (mp2_v, pp2)]) th
     in Thm.implies_elim (Thm.implies_elim th0 th') th'' end
  in (fw true th1 th_1 th_1', fw false th2 th_2 th_2',
      fw true th3 th_3 th_3', fw false th4 th_4 th_4', fw true th5 th_5 th_5')
  end
 val U_v = dest_Var (Thm.term_of (Thm.dest_arg (Thm.dest_arg (Thm.dest_arg1 (Thm.cprop_of qe)))))
 fun main vs p =
  let
   val ((xn,ce),(x,fm)) = (case Thm.term_of p of
                   \<^Const_>\<open>Ex _ for \<open>Abs (xn, _, _)\<close>\<close> =>
                        Thm.dest_comb p ||> Thm.dest_abs_global |>> pair xn
                 | _ => raise CTERM ("main QE only treats existential quantifiers!", [p]))
   val cT = Thm.ctyp_of_cterm x
   val (u,nth) = uset (x::vs) fm |>> distinct (op aconvc)
   val nthx = Thm.abstract_rule xn x nth
   val q = Thm.rhs_of nth
   val qx = Thm.rhs_of nthx
   val enth = Drule.arg_cong_rule ce nthx
   val [th0,th1] = map (Thm.instantiate' [SOME cT] []) @{thms "finite.intros"}
   fun ins x th =
      Thm.implies_elim (Thm.instantiate' [] [(SOME o Thm.dest_arg o Thm.dest_arg)
                                       (Thm.cprop_of th), SOME x] th1) th
   val fU = fold ins u th0
   val cU = funpow 2 Thm.dest_arg (Thm.cprop_of fU)
   local
     val insI1 = Thm.instantiate' [SOME cT] [] @{thm "insertI1"}
     val insI2 = Thm.instantiate' [SOME cT] [] @{thm "insertI2"}
   in
    fun provein x S =
     case Thm.term_of S of
        \<^Const_>\<open>Orderings.bot _\<close> => raise CTERM ("provein : not a member!", [S])
      | \<^Const_>\<open>insert _ for y _\<close> =>
         let val (cy,S') = Thm.dest_binop S
         in if Thm.term_of x aconv y then Thm.instantiate' [] [SOME x, SOME S'] insI1
         else Thm.implies_elim (Thm.instantiate' [] [SOME x, SOME S', SOME cy] insI2)
                           (provein x S')
         end
   end
   val tabU = fold (fn t => fn tab => Termtab.update (Thm.term_of t, provein t cU) tab)
                   u Termtab.empty
   val U = the o Termtab.lookup tabU o Thm.term_of
   val [minf_conj, minf_disj, minf_eq, minf_neq, minf_lt,
        minf_le, minf_gt, minf_ge, minf_P] = minf
   val [pinf_conj, pinf_disj, pinf_eq, pinf_neq, pinf_lt,
        pinf_le, pinf_gt, pinf_ge, pinf_P] = pinf
   val [nmi_conj, nmi_disj, nmi_eq, nmi_neq, nmi_lt,
        nmi_le, nmi_gt, nmi_ge, nmi_P] = map (Drule.instantiate_normalize (TVars.empty, Vars.make [(U_v,cU)])) nmi
   val [npi_conj, npi_disj, npi_eq, npi_neq, npi_lt,
        npi_le, npi_gt, npi_ge, npi_P] = map (Drule.instantiate_normalize (TVars.empty, Vars.make [(U_v,cU)])) npi
   val [ld_conj, ld_disj, ld_eq, ld_neq, ld_lt,
        ld_le, ld_gt, ld_ge, ld_P] = map (Drule.instantiate_normalize (TVars.empty, Vars.make [(U_v,cU)])) ld

   fun decomp_mpinf fm =
     case Thm.term_of fm of
       \<^Const_>\<open>HOL.conj for _ _\<close> =>
        let val (p,q) = Thm.dest_binop fm
        in ([p,q], myfwd (minf_conj,pinf_conj, nmi_conj, npi_conj,ld_conj)
                         (Thm.lambda x p) (Thm.lambda x q))
        end
     | \<^Const_>\<open>HOL.disj for _ _\<close> =>
        let val (p,q) = Thm.dest_binop fm
        in ([p,q],myfwd (minf_disj, pinf_disj, nmi_disj, npi_disj,ld_disj)
                         (Thm.lambda x p) (Thm.lambda x q))
        end
     | _ =>
        (let val c = wi x fm
             val t = (if c=Nox then I
                      else if member (op =) [Lt, Le, Eq] c then Thm.dest_arg
                      else if member (op =) [Gt, Ge] c then Thm.dest_arg1
                      else if c = NEq then (Thm.dest_arg o Thm.dest_arg)
                      else raise Fail "decomp_mpinf: Impossible case!!") fm
             val [mi_th, pi_th, nmi_th, npi_th, ld_th] =
               if c = Nox then map (Thm.instantiate' [] [SOME fm])
                                    [minf_P, pinf_P, nmi_P, npi_P, ld_P]
               else
                let val [mi_th,pi_th,nmi_th,npi_th,ld_th] =
                 map (Thm.instantiate' [] [SOME t])
                 (case c of Lt => [minf_lt, pinf_lt, nmi_lt, npi_lt, ld_lt]
                          | Le => [minf_le, pinf_le, nmi_le, npi_le, ld_le]
                          | Gt => [minf_gt, pinf_gt, nmi_gt, npi_gt, ld_gt]
                          | Ge => [minf_ge, pinf_ge, nmi_ge, npi_ge, ld_ge]
                          | Eq => [minf_eq, pinf_eq, nmi_eq, npi_eq, ld_eq]
                          | NEq => [minf_neq, pinf_neq, nmi_neq, npi_neq, ld_neq])
                    val tU = U t
                    fun Ufw th = Thm.implies_elim th tU
                 in [mi_th, pi_th, Ufw nmi_th, Ufw npi_th, Ufw ld_th]
                 end
         in ([], K (mi_th, pi_th, nmi_th, npi_th, ld_th)) end)
   val (minf_th, pinf_th, nmi_th, npi_th, ld_th) = divide_and_conquer decomp_mpinf q
   val qe_th = Drule.implies_elim_list
                  ((fconv_rule (Thm.beta_conversion true))
                   (Thm.instantiate' [] (map SOME [cU, qx, get_p1 minf_th, get_p1 pinf_th])
                        qe))
                  [fU, ld_th, nmi_th, npi_th, minf_th, pinf_th]
    val bex_conv =
      Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps @{thms simp_thms bex_simps(1-5)})
    val result_th = fconv_rule (arg_conv bex_conv) (Thm.transitive enth qe_th)
   in result_th
   end

in main
end;

val grab_atom_bop =
 let
  fun h ctxt tm =
   (case Thm.term_of tm of
     \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for _ _\<close> => find_args ctxt tm
   | \<^Const_>\<open>Not for _\<close> => h ctxt (Thm.dest_arg tm)
   | \<^Const_>\<open>All _ for _\<close> => find_body ctxt (Thm.dest_arg tm)
   | \<^Const_>\<open>Ex _ for _\<close> => find_body ctxt (Thm.dest_arg tm)
   | \<^Const_>\<open>conj for _ _\<close> => find_args ctxt tm
   | \<^Const_>\<open>disj for _ _\<close> => find_args ctxt tm
   | \<^Const_>\<open>implies for _ _\<close> => find_args ctxt tm
   | \<^Const_>\<open>Pure.imp for _ _\<close> => find_args ctxt tm
   | \<^Const_>\<open>Pure.eq _ for _ _\<close> => find_args ctxt tm
   | \<^Const_>\<open>Pure.all _ for _\<close> => find_body ctxt (Thm.dest_arg tm)
   | \<^Const_>\<open>Trueprop for _\<close> => h ctxt (Thm.dest_arg tm)
   | _ => Thm.dest_fun2 tm)
  and find_args ctxt tm =
           (h ctxt (Thm.dest_arg tm) handle CTERM _ => Thm.dest_arg1 tm)
 and find_body ctxt b =
   let val ((_, b'), ctxt') = Variable.dest_abs_cterm b ctxt
   in h ctxt' b' end;
in h end;

fun raw_ferrack_qe_conv ctxt (thy, {isolate_conv, whatis, simpset = ss}) tm =
 let
   val ss' =
     merge_ss (simpset_of
      (put_simpset HOL_basic_ss ctxt addsimps
        @{thms simp_thms ex_simps all_simps not_all all_not_ex ex_disj_distrib}), ss);
   val pcv = Simplifier.rewrite (put_simpset ss' ctxt);
   val postcv = Simplifier.rewrite (put_simpset ss ctxt);
   val nnf = K (nnf_conv ctxt then_conv postcv)
   val env = Cterms.list_set_rev (Cterms.build (Drule.add_frees_cterm tm))
   val qe_conv = Qelim.gen_qelim_conv ctxt pcv postcv pcv cons env
                  (isolate_conv ctxt) nnf
                  (fn vs => ferrack_conv ctxt (thy,{isolate_conv = isolate_conv ctxt,
                                               whatis = whatis, simpset = ss}) vs
                   then_conv postcv)
 in (Simplifier.rewrite (put_simpset ss ctxt) then_conv qe_conv) tm end;

fun dlo_instance ctxt tm =
  Ferrante_Rackoff_Data.match ctxt (grab_atom_bop ctxt tm);

fun dlo_conv ctxt tm =
  (case dlo_instance ctxt tm of
    NONE => raise CTERM ("ferrackqe_conv: no corresponding instance in context!", [tm])
  | SOME instance => raw_ferrack_qe_conv ctxt instance tm);

fun dlo_tac ctxt = CSUBGOAL (fn (p, i) =>
  (case dlo_instance ctxt p of
    NONE => no_tac
  | SOME instance =>
      Object_Logic.full_atomize_tac ctxt i THEN
      simp_tac (put_simpset (#simpset (snd instance)) ctxt) i THEN  (* FIXME already part of raw_ferrack_qe_conv? *)
      CONVERSION (Object_Logic.judgment_conv ctxt (raw_ferrack_qe_conv ctxt instance)) i THEN
      simp_tac ctxt i));  (* FIXME really? *)

end;
