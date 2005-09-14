(*  ID:         $Id$
    Author:     Amine Chaieb

Tactic for solving equalities over commutative rings *)

signature COMM_RING =
sig
  val comm_ring_tac : int -> tactic
  val comm_ring_method: int -> Proof.method
  val setup : (theory -> theory) list
end

structure CommRing: COMM_RING =
struct

(* The Cring exception for erronous uses of cring_tac *)
exception CRing of string;

(* Zero and One of the commutative ring *)
fun cring_zero T = Const("0",T);
fun cring_one T = Const("1",T);

(* reification functions *)
(* add two polynom expressions *)
fun polT t = Type ("Commutative_Ring.pol",[t]);
fun  polexT t = Type("Commutative_Ring.polex",[t]);
val nT = HOLogic.natT;
fun listT T = Type ("List.list",[T]);

(* Reification of the constructors *)
(* Nat*)
val succ = Const("Suc",nT --> nT);
val zero = Const("0",nT);
val one = Const("1",nT);

(* Lists *)
fun reif_list T [] = Const("List.list.Nil",listT T)
  | reif_list T (x::xs) = Const("List.list.Cons",[T,listT T] ---> listT T)
                             $x$(reif_list T xs);

(* pol*)
fun pol_Pc t = Const("Commutative_Ring.pol.Pc",t --> polT t);
fun pol_Pinj t = Const("Commutative_Ring.pol.Pinj",[nT,polT t] ---> polT t);
fun pol_PX t = Const("Commutative_Ring.pol.PX",[polT t, nT, polT t] ---> polT t);

(* polex *)
fun polex_add t = Const("Commutative_Ring.polex.Add",[polexT t,polexT t] ---> polexT t);
fun polex_sub t = Const("Commutative_Ring.polex.Sub",[polexT t,polexT t] ---> polexT t);
fun polex_mul t = Const("Commutative_Ring.polex.Mul",[polexT t,polexT t] ---> polexT t);
fun polex_neg t = Const("Commutative_Ring.polex.Neg",polexT t --> polexT t);
fun polex_pol t = Const("Commutative_Ring.polex.Pol",polT t --> polexT t);
fun polex_pow t = Const("Commutative_Ring.polex.Pow",[polexT t, nT] ---> polexT t);
(* reification of natural numbers *)
fun reif_nat n =
    if n>0 then succ$(reif_nat (n-1))
    else if n=0 then zero
    else raise CRing "ring_tac: reif_nat negative n";

(* reification of polynoms : primitive cring expressions *)
fun reif_pol T vs t =
    case t of
       Free(_,_) =>
        let val i = find_index_eq t vs
        in if i = 0
           then (pol_PX T)$((pol_Pc T)$ (cring_one T))
                          $one$((pol_Pc T)$(cring_zero T))
           else (pol_Pinj T)$(reif_nat i)$
                            ((pol_PX T)$((pol_Pc T)$ (cring_one T))
                                       $one$
                                       ((pol_Pc T)$(cring_zero T)))
        end
      | _ => (pol_Pc T)$ t;


(* reification of polynom expressions *)
fun reif_polex T vs t =
    case t of
        Const("op +",_)$a$b => (polex_add T)
                                   $ (reif_polex T vs a)$(reif_polex T vs b)
      | Const("op -",_)$a$b => (polex_sub T)
                                   $ (reif_polex T vs a)$(reif_polex T vs b)
      | Const("op *",_)$a$b =>  (polex_mul T)
                                    $ (reif_polex T vs a)$ (reif_polex T vs b)
      | Const("uminus",_)$a => (polex_neg T)
                                   $ (reif_polex T vs a)
      | (Const("Nat.power",_)$a$n) => (polex_pow T) $ (reif_polex T vs a) $ n

      | _ => (polex_pol T) $ (reif_pol T vs t);

(* reification of the equation *)
val cr_sort = Sign.read_sort (the_context ()) "{comm_ring,recpower}";
fun reif_eq sg (eq as Const("op =",Type("fun",a::_))$lhs$rhs) =
    if Sign.of_sort (the_context()) (a,cr_sort)
    then
        let val fs = term_frees eq
            val cvs = cterm_of sg (reif_list a fs)
            val clhs = cterm_of sg (reif_polex a fs lhs)
            val crhs = cterm_of sg (reif_polex a fs rhs)
            val ca = ctyp_of sg a
        in (ca,cvs,clhs, crhs)
        end
    else raise CRing "reif_eq: not an equation over comm_ring + recpower"
  | reif_eq sg _ = raise CRing "reif_eq: not an equation";

(*The cring tactic  *)
(* Attention: You have to make sure that no t^0 is in the goal!! *)
(* Use simply rewriting t^0 = 1 *)
val cring_ss = simpset_of (the_context())
                           addsimps
                           (map thm ["mkPX_def", "mkPinj_def","sub_def",
                                     "power_add","even_def","pow_if"])
                           addsimps [sym OF [thm "power_add"]];

val norm_eq = thm "norm_eq"
fun comm_ring_tac i =(fn st =>
    let
        val g = BasisLibrary.List.nth (prems_of st, i - 1)
        val sg = sign_of_thm st
        val (ca,cvs,clhs,crhs) = reif_eq sg (HOLogic.dest_Trueprop g)
        val norm_eq_th = simplify cring_ss
                        (instantiate' [SOME ca] [SOME clhs, SOME crhs, SOME cvs]
                                                norm_eq)
    in ((cut_rules_tac [norm_eq_th] i)
            THEN (simp_tac cring_ss i)
            THEN (simp_tac cring_ss i)) st
    end);

fun comm_ring_method i = Method.METHOD (fn facts =>
  Method.insert_tac facts 1 THEN comm_ring_tac i);

val setup =
  [Method.add_method ("comm_ring",
     Method.no_args (comm_ring_method 1),
     "reflective decision procedure for equalities over commutative rings")];

end;
