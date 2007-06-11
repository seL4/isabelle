(*  Title:      HOL/Tools/Groebner_Basis/groebner.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

signature GROEBNER =
sig
  val ring_and_ideal_conv :
    {idom: thm list, ring: cterm list * thm list, vars: cterm list,
     semiring: Thm.cterm list * thm list} ->
    (Thm.cterm -> Rat.rat) -> (Rat.rat -> Thm.cterm) ->
    Conv.conv ->  Conv.conv ->
    Conv.conv * (cterm list -> cterm -> (cterm * cterm -> order) -> cterm list)
    val ring_conv : Proof.context -> cterm -> thm
end

structure Groebner: GROEBNER =
struct
open Normalizer;
open Misc;

     (* FIXME :: Already present in Tools/Presburger/qelim.ML but is much more general!! *)
fun cterm_frees ct =
 let fun h acc t =
   case (term_of t) of
    _$_ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | Abs(_,_,_) => Thm.dest_abs NONE t ||> h acc |> uncurry (remove (op aconvc))
  | Free _ => insert (op aconvc) t acc
  | _ => acc
 in h [] ct end;

fun assocd x al d = case AList.lookup (op =) al x of SOME y => y | NONE => d;
val rat_0 = Rat.zero;
val rat_1 = Rat.one;
val minus_rat = Rat.neg;
val denominator_rat = Rat.quotient_of_rat #> snd #> Rat.rat_of_int;
fun int_of_rat a =
    case Rat.quotient_of_rat a of (i,1) => i | _ => error "int_of_rat: not an int";
val lcm_rat = fn x => fn y => Rat.rat_of_int (lcm (int_of_rat x, int_of_rat y));

val (eqF_intr, eqF_elim) =
  let val [th1,th2] = thms "PFalse"
  in (fn th => th COMP th2, fn th => th COMP th1) end;

val (PFalse, PFalse') =
 let val PFalse_eq = nth (thms "simp_thms") 13
 in (PFalse_eq RS iffD1, PFalse_eq RS iffD2) end;


(* ------------------------------------------------------------------------- *)
(* Type for recording history, i.e. how a polynomial was obtained.           *)
(* ------------------------------------------------------------------------- *)

datatype history =
   Start of integer
 | Mmul of (Rat.rat * (integer list)) * history
 | Add of history * history;


(* Monomial ordering. *)

fun morder_lt m1 m2=
    let fun lexorder l1 l2 =
            case (l1,l2) of
                ([],[]) => false
              | (x1::o1,x2::o2) => x1 > x2 orelse x1 = x2 andalso lexorder o1 o2
              | _ => error "morder: inconsistent monomial lengths"
        val n1 = fold Integer.add m1 0
        val n2 = fold Integer.add m2 0 in
    n1 < n2 orelse n1 = n2 andalso lexorder m1 m2
    end;

fun morder_le m1 m2 = morder_lt m1 m2 orelse (m1 = m2);

fun morder_gt m1 m2 = morder_lt m2 m1;

(* Arithmetic on canonical polynomials. *)

fun grob_neg l = map (fn (c,m) => (minus_rat c,m)) l;

fun grob_add l1 l2 =
  case (l1,l2) of
    ([],l2) => l2
  | (l1,[]) => l1
  | ((c1,m1)::o1,(c2,m2)::o2) =>
        if m1 = m2 then
          let val c = c1+/c2 val rest = grob_add o1 o2 in
          if c =/ rat_0 then rest else (c,m1)::rest end
        else if morder_lt m2 m1 then (c1,m1)::(grob_add o1 l2)
        else (c2,m2)::(grob_add l1 o2);

fun grob_sub l1 l2 = grob_add l1 (grob_neg l2);

fun grob_mmul (c1,m1) (c2,m2) = (c1*/c2,map2 Integer.add m1 m2);

fun grob_cmul cm pol = map (grob_mmul cm) pol;

fun grob_mul l1 l2 =
  case l1 of
    [] => []
  | (h1::t1) => grob_add (grob_cmul h1 l2) (grob_mul t1 l2);

fun grob_inv l =
  case l of
    [(c,vs)] => if (forall (fn x => x = 0) vs) then
                  if (c =/ rat_0) then error "grob_inv: division by zero"
                  else [(rat_1 // c,vs)]
              else error "grob_inv: non-constant divisor polynomial"
  | _ => error "grob_inv: non-constant divisor polynomial";

fun grob_div l1 l2 =
  case l2 of
    [(c,l)] => if (forall (fn x => x = 0) l) then
                 if c =/ rat_0 then error "grob_div: division by zero"
                 else grob_cmul (rat_1 // c,l) l1
             else error "grob_div: non-constant divisor polynomial"
  | _ => error "grob_div: non-constant divisor polynomial";

fun grob_pow vars l n =
  if n < 0 then error "grob_pow: negative power"
  else if n = 0 then [(rat_1,map (fn v => 0) vars)]
  else grob_mul l (grob_pow vars l (n -% 1));

val max = fn (x: integer) => fn y => if x < y then y else x;

fun degree vn p =
 case p of
  [] => error "Zero polynomial"
| [(c,ns)] => nth ns vn
| (c,ns)::p' => max (nth ns vn) (degree vn p');

fun head_deg vn p = let val d = degree vn p in
 (d,fold (fn (c,r) => fn q => grob_add q [(c, map_index (fn (i,n) => if i = vn then 0 else n) r)]) (filter (fn (c,ns) => c <>/ rat_0 andalso nth ns vn = d) p) []) end;

val is_zerop = forall (fn (c,ns) => c =/ rat_0 andalso forall (curry (op =) (0: integer)) ns);
val grob_pdiv =
 let fun pdiv_aux vn (n,a) p k s =
  if is_zerop s then (k,s) else
  let val (m,b) = head_deg vn s
  in if m < n then (k,s) else
     let val p' = grob_mul p [(rat_1, map_index (fn (i,v) => if i = vn then m -% n else 0)
                                                (snd (hd s)))]
     in if a = b then pdiv_aux vn (n,a) p k (grob_sub s p')
        else pdiv_aux vn (n,a) p (k +% 1) (grob_sub (grob_mul a s) (grob_mul b p'))
     end
  end
 in fn vn => fn s => fn p => pdiv_aux vn (head_deg vn p) p 0 s
 end;

(* Monomial division operation. *)

fun mdiv (c1,m1) (c2,m2) =
  (c1//c2,
   map2 (fn n1 => fn n2 => if n1 < n2 then error "mdiv" else n1 -% n2) m1 m2);

(* Lowest common multiple of two monomials. *)

fun mlcm (c1,m1) (c2,m2) = (rat_1,map2 max m1 m2);

(* Reduce monomial cm by polynomial pol, returning replacement for cm.  *)

fun reduce1 cm (pol,hpol) =
  case pol of
    [] => error "reduce1"
  | cm1::cms => ((let val (c,m) = mdiv cm cm1 in
                    (grob_cmul (minus_rat c,m) cms,
                     Mmul((minus_rat c,m),hpol)) end)
                handle  ERROR _ => error "reduce1");

(* Try this for all polynomials in a basis.  *)
fun tryfind f l =
    case l of
        [] => error "tryfind"
      | (h::t) => ((f h) handle ERROR _ => tryfind f t);

fun reduceb cm basis = tryfind (fn p => reduce1 cm p) basis;

(* Reduction of a polynomial (always picking largest monomial possible).     *)

fun reduce basis (pol,hist) =
  case pol of
    [] => (pol,hist)
  | cm::ptl => ((let val (q,hnew) = reduceb cm basis in
                   reduce basis (grob_add q ptl,Add(hnew,hist)) end)
               handle (ERROR _) =>
                   (let val (q,hist') = reduce basis (ptl,hist) in
                       (cm::q,hist') end));

(* Check for orthogonality w.r.t. LCM.                                       *)

fun orthogonal l p1 p2 =
  snd l = snd(grob_mmul (hd p1) (hd p2));

(* Compute S-polynomial of two polynomials.                                  *)

fun spoly cm ph1 ph2 =
  case (ph1,ph2) of
    (([],h),p) => ([],h)
  | (p,([],h)) => ([],h)
  | ((cm1::ptl1,his1),(cm2::ptl2,his2)) =>
        (grob_sub (grob_cmul (mdiv cm cm1) ptl1)
                  (grob_cmul (mdiv cm cm2) ptl2),
         Add(Mmul(mdiv cm cm1,his1),
             Mmul(mdiv (minus_rat(fst cm),snd cm) cm2,his2)));

(* Make a polynomial monic.                                                  *)

fun monic (pol,hist) =
  if pol = [] then (pol,hist) else
  let val (c',m') = hd pol in
  (map (fn (c,m) => (c//c',m)) pol,
   Mmul((rat_1 // c',map (K 0) m'),hist)) end;

(* The most popular heuristic is to order critical pairs by LCM monomial.    *)

fun forder ((c1,m1),_) ((c2,m2),_) = morder_lt m1 m2;

fun poly_lt  p q =
  case (p,q) of
    (p,[]) => false
  | ([],q) => true
  | ((c1,m1)::o1,(c2,m2)::o2) =>
        c1 </ c2 orelse
        c1 =/ c2 andalso ((morder_lt m1 m2) orelse m1 = m2 andalso poly_lt o1 o2);

fun align  ((p,hp),(q,hq)) =
  if poly_lt p q then ((p,hp),(q,hq)) else ((q,hq),(p,hp));
fun forall2 p l1 l2 =
  case (l1,l2) of
    ([],[]) => true
  | (h1::t1,h2::t2) => p h1 h2 andalso forall2 p t1 t2
  | _ => false;

fun poly_eq p1 p2 =
  forall2 (fn (c1,m1) => fn (c2,m2) => c1 =/ c2 andalso m1 = m2) p1 p2;

fun memx ((p1,h1),(p2,h2)) ppairs =
  not (exists (fn ((q1,_),(q2,_)) => poly_eq p1 q1 andalso poly_eq p2 q2) ppairs);

(* Buchberger's second criterion.                                            *)

fun criterion2 basis (lcm,((p1,h1),(p2,h2))) opairs =
  exists (fn g => not(poly_eq (fst g) p1) andalso not(poly_eq (fst g) p2) andalso
                   can (mdiv lcm) (hd(fst g)) andalso
                   not(memx (align (g,(p1,h1))) (map snd opairs)) andalso
                   not(memx (align (g,(p2,h2))) (map snd opairs))) basis;

(* Test for hitting constant polynomial.                                     *)

fun constant_poly p =
  length p = 1 andalso forall (fn x => x = (0: integer)) (snd(hd p));

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm.                                                  *)
(* ------------------------------------------------------------------------- *)
(* FIXME: try to get rid of mergesort? *)
fun merge ord l1 l2 =
 case l1 of
  [] => l2
 | h1::t1 =>
   case l2 of
    [] => l1
   | h2::t2 => if ord h1 h2 then h1::(merge ord t1 l2)
               else h2::(merge ord l1 t2);
fun mergesort ord l =
 let
 fun mergepairs l1 l2 =
  case (l1,l2) of
   ([s],[]) => s
 | (l,[]) => mergepairs [] l
 | (l,[s1]) => mergepairs (s1::l) []
 | (l,(s1::s2::ss)) => mergepairs ((merge ord s1 s2)::l) ss
 in if l = []  then []  else mergepairs [] (map (fn x => [x]) l)
 end;


fun grobner_basis basis pairs =
  (writeln (Int.toString(length basis)^" basis elements and "^
               Int.toString(length pairs)^" critical pairs");
  case pairs of
    [] => basis
  | (l,(p1,p2))::opairs =>
        let val (sph as (sp,hist)) = monic (reduce basis (spoly l p1 p2))
        in if sp = [] orelse criterion2 basis (l,(p1,p2)) opairs
           then grobner_basis basis opairs
           else if constant_poly sp then grobner_basis (sph::basis) []
           else let val rawcps = map (fn p => (mlcm (hd(fst p)) (hd sp),align(p,sph)))
                                     basis
                    val newcps = filter
                                     (fn (l,(p,q)) => not(orthogonal l (fst p) (fst q)))
                                     rawcps
                in grobner_basis (sph::basis)
                                 (merge forder opairs (mergesort forder newcps))
                end
        end);

(* ------------------------------------------------------------------------- *)
(* Interreduce initial polynomials.                                          *)
(* ------------------------------------------------------------------------- *)

fun grobner_interreduce rpols ipols =
  case ipols of
    [] => map monic (rev rpols)
  | p::ps => let val p' = reduce (rpols @ ps) p in
             if fst p' = [] then grobner_interreduce rpols ps
             else grobner_interreduce (p'::rpols) ps end;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

fun grobner pols =
    let val npols = map2 (fn p => fn n => (p,Start n)) pols
          (map Integer.int (0 upto (length pols - 1)))
        val phists = filter (fn (p,_) => p <> []) npols
        val bas = grobner_interreduce [] (map monic phists)
        val prs0 = product bas bas
        val prs1 = filter (fn ((x,_),(y,_)) => poly_lt x y) prs0
        val prs2 = map (fn (p,q) => (mlcm (hd(fst p)) (hd(fst q)),(p,q))) prs1
        val prs3 =
            filter (fn (l,(p,q)) => not(orthogonal l (fst p) (fst q))) prs2 in
        grobner_basis bas (mergesort forder prs3) end;

(* ------------------------------------------------------------------------- *)
(* Get proof of contradiction from Grobner basis.                            *)
(* ------------------------------------------------------------------------- *)
fun find p l =
  case l of
      [] => error "find"
    | (h::t) => if p(h) then h else find p t;

fun grobner_refute pols =
  let val gb = grobner pols in
  snd(find (fn (p,h) => length p = 1 andalso forall (fn x=> x=0) (snd(hd p))) gb)
  end;

(* ------------------------------------------------------------------------- *)
(* Turn proof into a certificate as sum of multipliers.                      *)
(*                                                                           *)
(* In principle this is very inefficient: in a heavily shared proof it may   *)
(* make the same calculation many times. Could put in a cache or something.  *)
(* ------------------------------------------------------------------------- *)
fun assoc x l = snd(find (fn p => fst p = x) l);

fun resolve_proof vars prf =
  case prf of
    Start(~1) => []
  | Start m => [(m,[(rat_1,map (K 0) vars)])]
  | Mmul(pol,lin) =>
        let val lis = resolve_proof vars lin in
            map (fn (n,p) => (n,grob_cmul pol p)) lis end
  | Add(lin1,lin2) =>
        let val lis1 = resolve_proof vars lin1
            val lis2 = resolve_proof vars lin2
            val dom = distinct (op =) ((map fst lis1) union (map fst lis2))
        in
            map (fn n => let val a = ((assoc n lis1) handle _ => [])  (* FIXME *)
                             val b = ((assoc n lis2) handle _ => []) in  (* FIXME *)
                             (n,grob_add a b) end) dom end;

(* ------------------------------------------------------------------------- *)
(* Run the procedure and produce Weak Nullstellensatz certificate.           *)
(* ------------------------------------------------------------------------- *)
fun grobner_weak vars pols =
    let val cert = resolve_proof vars (grobner_refute pols)
        val l =
            fold_rev (fold_rev (lcm_rat o denominator_rat o fst) o snd) cert (rat_1) in
        (l,map (fn (i,p) => (i,map (fn (d,m) => (l*/d,m)) p)) cert) end;

(* ------------------------------------------------------------------------- *)
(* Prove a polynomial is in ideal generated by others, using Grobner basis.  *)
(* ------------------------------------------------------------------------- *)

fun grobner_ideal vars pols pol =
  let val (pol',h) = reduce (grobner pols) (grob_neg pol,Start(~1)) in
  if pol <> [] then error "grobner_ideal: not in the ideal" else
  resolve_proof vars h end;

(* ------------------------------------------------------------------------- *)
(* Produce Strong Nullstellensatz certificate for a power of pol.            *)
(* ------------------------------------------------------------------------- *)

fun grobner_strong vars pols pol =
    let val vars' = @{cterm "True"}::vars
        val grob_z = [(rat_1,1::(map (fn x => 0) vars))]
        val grob_1 = [(rat_1,(map (fn x => 0) vars'))]
        fun augment p= map (fn (c,m) => (c,0::m)) p
        val pols' = map augment pols
        val pol' = augment pol
        val allpols = (grob_sub (grob_mul grob_z pol') grob_1)::pols'
        val (l,cert) = grobner_weak vars' allpols
        val d = fold_rev (fold_rev (max o hd o snd) o snd) cert 0
        fun transform_monomial (c,m) =
            grob_cmul (c,tl m) (grob_pow vars pol (d - hd m))
        fun transform_polynomial q = fold_rev (grob_add o transform_monomial) q []
        val cert' = map (fn (c,q) => (c-1,transform_polynomial q))
                        (filter (fn (k,_) => k <> 0) cert) in
        (d,l,cert') end;

fun string_of_pol vars pol =
    foldl (fn ((c,m),s) => ((Rat.string_of_rat c)
                            ^ "*(" ^
                            (snd (foldl
                                      (fn (e,(i,s)) =>
                                          (i+ 1,
                                           (nth vars i
                                                     |>cterm_of (the_context())  (* FIXME *)
                                                     |> string_of_cterm)^ "^"
                                           ^ (Int.toString e) ^" * " ^ s)) (0,"0") m))
                            ^ ") + ") ^ s) "" pol;


(* ------------------------------------------------------------------------- *)
(* Overall parametrized universal procedure for (semi)rings.                 *)
(* We return an ideal_conv and the actual ring prover.                       *)
(* ------------------------------------------------------------------------- *)
fun refute_disj rfn tm =
 case term_of tm of
  Const("op |",_)$l$r =>
   Drule.compose_single(refute_disj rfn (Thm.dest_arg tm),2,Drule.compose_single(refute_disj rfn (Thm.dest_arg1 tm),2,disjE))
  | _ => rfn tm ;

val notnotD = @{thm "notnotD"};
fun mk_binop ct x y =
  Thm.capply (Thm.capply ct x) y

val mk_comb = Thm.capply;
fun is_neg t =
    case term_of t of
      (Const("Not",_)$p) => true
    | _  => false;
fun is_eq t =
 case term_of t of
 (Const("op =",_)$_$_) => true
| _  => false;

fun end_itlist f l =
  case l of
        []     => error "end_itlist"
      | [x]    => x
      | (h::t) => f h (end_itlist f t);

val list_mk_binop = fn b => end_itlist (mk_binop b);

val list_dest_binop = fn b =>
 let fun h acc t =
  ((let val (l,r) = dest_binop b t in h (h acc r) l end)
   handle CTERM _ => (t::acc)) (* Why had I handle _ => ? *)
 in h []
 end;

val strip_exists =
 let fun h (acc, t) =
      case (term_of t) of
       Const("Ex",_)$Abs(x,T,p) => h (Thm.dest_abs NONE (Thm.dest_arg t) |>> (fn v => v::acc))
     | _ => (acc,t)
 in fn t => h ([],t)
 end;

fun is_forall t =
 case term_of t of
  (Const("All",_)$Abs(_,_,_)) => true
| _ => false;

val mk_object_eq = fn th => th COMP meta_eq_to_obj_eq;
val bool_simps = @{thms "bool_simps"};
val nnf_simps = @{thms "nnf_simps"};
val nnf_conv = Simplifier.rewrite (HOL_basic_ss addsimps bool_simps addsimps nnf_simps)
val weak_dnf_conv = Simplifier.rewrite (HOL_basic_ss addsimps (@{thms "weak_dnf_simps"}));
val initial_conv =
    Simplifier.rewrite
     (HOL_basic_ss addsimps nnf_simps
     addsimps [not_all, not_ex] addsimps map (fn th => th RS sym) (ex_simps @ all_simps));

val specl = fold_rev (fn x => fn th => instantiate' [] [SOME x] (th RS spec));

val cTrp = @{cterm "Trueprop"};
val cConj = @{cterm "op &"};
val (cNot,false_tm) = (@{cterm "Not"}, @{cterm "False"});
val ASSUME = mk_comb cTrp #> assume;
val list_mk_conj = list_mk_binop cConj;
val conjs = list_dest_binop cConj;
val mk_neg = mk_comb cNot;



(** main **)

fun ring_and_ideal_conv
  {vars, semiring = (sr_ops, sr_rules), ring = (r_ops, r_rules), idom}
  dest_const mk_const ring_eq_conv ring_normalize_conv =
let
  val [add_pat, mul_pat, pow_pat, zero_tm, one_tm] = sr_ops;
  val [ring_add_tm, ring_mul_tm, ring_pow_tm] =
    map (Thm.dest_fun o Thm.dest_fun) [add_pat, mul_pat, pow_pat];

  val (ring_sub_tm, ring_neg_tm) =
    (case r_ops of
      [] => (@{cterm "True"}, @{cterm "True"})
    | [sub_pat, neg_pat] => (Thm.dest_fun (Thm.dest_fun sub_pat), Thm.dest_fun neg_pat));

  val [idom_thm, neq_thm] = idom;

  val ring_dest_neg =
    fn t => let val (l,r) = Thm.dest_comb t in
        if could_unify(term_of l,term_of ring_neg_tm) then r else raise CTERM ("ring_dest_neg", [t])
      end

 val ring_mk_neg = fn tm => mk_comb (ring_neg_tm) (tm);
(*
 fun ring_dest_inv t =
    let val (l,r) = Thm.dest_comb t in
        if could_unify(term_of l, term_of ring_inv_tm) then r else raise CTERM "ring_dest_inv"
    end
*)
 val ring_dest_add = dest_binop ring_add_tm;
 val ring_mk_add = mk_binop ring_add_tm;
 val ring_dest_sub = dest_binop ring_sub_tm;
 val ring_mk_sub = mk_binop ring_sub_tm;
 val ring_dest_mul = dest_binop ring_mul_tm;
 val ring_mk_mul = mk_binop ring_mul_tm;
(* val ring_dest_div = dest_binop ring_div_tm;
 val ring_mk_div = mk_binop ring_div_tm;*)
 val ring_dest_pow = dest_binop ring_pow_tm;
 val ring_mk_pow = mk_binop ring_pow_tm ;
 fun grobvars tm acc =
    if can dest_const tm then acc
    else if can ring_dest_neg tm then grobvars (Thm.dest_arg tm) acc
    else if can ring_dest_pow tm then grobvars (Thm.dest_arg1 tm) acc
    else if can ring_dest_add tm orelse can ring_dest_sub tm
            orelse can ring_dest_mul tm
    then grobvars (Thm.dest_arg1 tm) (grobvars (Thm.dest_arg tm) acc)
(*    else if can ring_dest_inv tm
       then
             let val gvs = grobvars (Thm.dest_arg tm) [] in
             if gvs = [] then acc else tm::acc
             end
    else if can ring_dest_div tm then
              let val lvs = grobvars (Thm.dest_arg1 tm) acc
                val gvs = grobvars (Thm.dest_arg tm) []
              in if gvs = [] then lvs else tm::acc
             end *)
    else tm::acc ;

fun grobify_term vars tm =
((if not (member (op aconvc) vars tm) then raise CTERM ("Not a variable", [tm]) else
     [(rat_1,map (fn i => if i aconvc tm then 1 else 0) vars)])
handle  CTERM _ =>
 ((let val x = dest_const tm
 in if x =/ rat_0 then [] else [(x,map (fn v => 0) vars)]
 end)
 handle ERROR _ =>
  ((grob_neg(grobify_term vars (ring_dest_neg tm)))
  handle CTERM _ =>
   (
(*   (grob_inv(grobify_term vars (ring_dest_inv tm)))
   handle CTERM _ => *)
    ((let val (l,r) = ring_dest_add tm
    in grob_add (grobify_term vars l) (grobify_term vars r)
    end)
    handle CTERM _ =>
     ((let val (l,r) = ring_dest_sub tm
     in grob_sub (grobify_term vars l) (grobify_term vars r)
     end)
     handle  CTERM _ =>
      ((let val (l,r) = ring_dest_mul tm
      in grob_mul (grobify_term vars l) (grobify_term vars r)
      end)
       handle CTERM _ =>
        (
(*  (let val (l,r) = ring_dest_div tm
          in grob_div (grobify_term vars l) (grobify_term vars r)
          end)
         handle CTERM _ => *)
          ((let val (l,r) = ring_dest_pow tm
          in grob_pow vars (grobify_term vars l) ((term_of #> HOLogic.dest_number #> snd) r)
          end)
           handle CTERM _ => error "grobify_term: unknown or invalid term")))))))));
val eq_tm = idom_thm |> concl |> Thm.dest_arg |> Thm.dest_arg |> Thm.dest_fun |> Thm.dest_fun ;
(*ring_integral |> hd |> concl |> Thm.dest_arg
                          |> Thm.dest_abs NONE |> snd |> Thm.dest_fun |> Thm.dest_fun; *)
val dest_eq = dest_binop eq_tm;

fun grobify_equation vars tm =
    let val (l,r) = dest_binop eq_tm tm
    in grob_sub (grobify_term vars l) (grobify_term vars r)
    end;

fun grobify_equations tm =
 let
  val cjs = conjs tm
  val  rawvars = fold_rev (fn eq => fn a =>
                                       grobvars (Thm.dest_arg1 eq) (grobvars (Thm.dest_arg eq) a)) cjs []
  val vars = sort (fn (x, y) => Term.term_ord(term_of x,term_of y))
                  (distinct (op aconvc) rawvars)
 in (vars,map (grobify_equation vars) cjs)
 end;

val holify_polynomial =
 let fun holify_varpow (v,n) =
  if n = 1 then v else ring_mk_pow v (mk_cnumber @{ctyp "nat"} n)  (* FIXME *)
 fun holify_monomial vars (c,m) =
  let val xps = map holify_varpow (filter (fn (_,n) => n <> (0: integer)) (vars ~~ m))
   in end_itlist ring_mk_mul (mk_const c :: xps)
  end
 fun holify_polynomial vars p =
     if p = [] then mk_const (rat_0)
     else end_itlist ring_mk_add (map (holify_monomial vars) p)
 in holify_polynomial
 end ;
val idom_rule = simplify (HOL_basic_ss addsimps [idom_thm]);
fun prove_nz n = eqF_elim
                 (ring_eq_conv(mk_binop eq_tm (mk_const n) (mk_const(rat_0))));
val neq_01 = prove_nz (rat_1);
fun neq_rule n th = [prove_nz n, th] MRS neq_thm;
fun mk_add th1 = combination(Drule.arg_cong_rule ring_add_tm th1);

fun refute tm =
 if tm aconvc false_tm then ASSUME tm else
  let
   val (nths0,eths0) = List.partition (is_neg o concl) (conjuncts(ASSUME tm))
   val  nths = filter (is_eq o Thm.dest_arg o concl) nths0
   val eths = filter (is_eq o concl) eths0
  in
   if null eths then
    let
      val th1 = end_itlist (fn th1 => fn th2 => idom_rule(conji th1 th2)) nths
      val th2 = Conv.fconv_rule
                ((arg_conv #> arg_conv)
                     (binop_conv ring_normalize_conv)) th1
      val conc = th2 |> concl |> Thm.dest_arg
      val (l,r) = conc |> dest_eq
    in implies_intr (mk_comb cTrp tm)
                    (equal_elim (Drule.arg_cong_rule cTrp (eqF_intr th2))
                           (reflexive l |> mk_object_eq))
    end
   else
   let
    val (vars,l,cert,noteqth) =(
     if null nths then
      let val (vars,pols) = grobify_equations(list_mk_conj(map concl eths))
          val (l,cert) = grobner_weak vars pols
      in (vars,l,cert,neq_01)
      end
     else
      let
       val nth = end_itlist (fn th1 => fn th2 => idom_rule(conji th1 th2)) nths
       val (vars,pol::pols) =
          grobify_equations(list_mk_conj(Thm.dest_arg(concl nth)::map concl eths))
       val (deg,l,cert) = grobner_strong vars pols pol
       val th1 = Conv.fconv_rule((arg_conv o arg_conv)(binop_conv ring_normalize_conv)) nth
       val th2 = funpow (Integer.machine_int deg) (idom_rule o conji th1) neq_01
      in (vars,l,cert,th2)
      end)
    val _ = writeln ("Translating certificate to HOL inferences")
    val cert_pos = map (fn (i,p) => (i,filter (fn (c,m) => c >/ rat_0) p)) cert
    val cert_neg = map (fn (i,p) => (i,map (fn (c,m) => (minus_rat c,m))
                                            (filter (fn (c,m) => c </ rat_0) p))) cert
    val  herts_pos = map (fn (i,p) => (i,holify_polynomial vars p)) cert_pos
    val  herts_neg = map (fn (i,p) => (i,holify_polynomial vars p)) cert_neg
    fun thm_fn pols =
        if null pols then reflexive(mk_const rat_0) else
        end_itlist mk_add
            (map (fn (i,p) => Drule.arg_cong_rule (mk_comb ring_mul_tm p)
              (nth eths (Integer.machine_int i) |> mk_meta_eq)) pols)
    val th1 = thm_fn herts_pos
    val th2 = thm_fn herts_neg
    val th3 = conji(mk_add (symmetric th1) th2 |> mk_object_eq) noteqth
    val th4 = Conv.fconv_rule ((arg_conv o arg_conv o binop_conv) ring_normalize_conv)
                               (neq_rule l th3)
    val (l,r) = dest_eq(Thm.dest_arg(concl th4))
   in implies_intr (mk_comb cTrp tm)
                        (equal_elim (Drule.arg_cong_rule cTrp (eqF_intr th4))
                   (reflexive l |> mk_object_eq))
   end
  end

fun ring tm =
 let
  fun mk_forall x p =
      mk_comb (Drule.cterm_rule (instantiate' [SOME (ctyp_of_term x)] []) @{cpat "All:: (?'a => bool) => _"}) (Thm.cabs x p)
  val avs = cterm_frees tm
  val P' = fold mk_forall avs tm
  val th1 = initial_conv(mk_neg P')
  val (evs,bod) = strip_exists(concl th1) in
   if is_forall bod then error "ring: non-universal formula"
   else
   let
    val th1a = weak_dnf_conv bod
    val boda = concl th1a
    val th2a = refute_disj refute boda
    val th2b = [mk_object_eq th1a, (th2a COMP notI) COMP PFalse'] MRS trans
    val th2 = fold (fn v => fn th => (forall_intr v th) COMP allI) evs (th2b RS PFalse)
    val th3 = equal_elim
                (Simplifier.rewrite (HOL_basic_ss addsimps [not_ex RS sym])
                          (th2 |> cprop_of)) th2
    in specl avs
             ([[[mk_object_eq th1, th3 RS PFalse'] MRS trans] MRS PFalse] MRS notnotD)
   end
 end
fun ideal tms tm ord =
 let
  val rawvars = fold_rev grobvars (tm::tms) []
  val vars = sort ord (distinct (fn (x,y) => (term_of x) aconv (term_of y)) rawvars)
  val pols = map (grobify_term vars) tms
  val pol = grobify_term vars tm
  val cert = grobner_ideal vars pols pol
 in map (fn n => let val p = assocd n cert [] in holify_polynomial vars p end)
        (map Integer.int (0 upto (length pols - 1)))
 end
in (ring,ideal)
end;


fun find_term bounds tm =
  (case term_of tm of
    Const ("op =", T) $ _ $ _ =>
      if domain_type T = HOLogic.boolT then find_args bounds tm
      else Thm.dest_arg tm
  | Const ("Not", _) $ _ => find_term bounds (Thm.dest_arg tm)
  | Const ("All", _) $ _ => find_body bounds (Thm.dest_arg tm)
  | Const ("Ex", _) $ _ => find_body bounds (Thm.dest_arg tm)
  | Const ("op &", _) $ _ $ _ => find_args bounds tm
  | Const ("op |", _) $ _ $ _ => find_args bounds tm
  | Const ("op -->", _) $ _ $ _ => find_args bounds tm
  | _ => raise TERM ("find_term", []))
and find_args bounds tm =
  let val (t, u) = Thm.dest_binop tm
  in (find_term bounds t handle TERM _ => find_term bounds u) end
and find_body bounds b =
  let val (_, b') = Thm.dest_abs (SOME (Name.bound bounds)) b
  in find_term (bounds + 1) b' end;

fun ring_conv ctxt form =
  (case try (find_term 0 (* FIXME !? *)) form of
    NONE => reflexive form
  | SOME tm =>
      (case NormalizerData.match ctxt tm of
        NONE => reflexive form
      | SOME (res as (theory, {is_const, dest_const, mk_const, conv = ring_eq_conv})) =>
        fst (ring_and_ideal_conv theory
          dest_const (mk_const (Thm.ctyp_of_term tm)) (ring_eq_conv ctxt)
          (semiring_normalize_wrapper ctxt res)) form));

end;
