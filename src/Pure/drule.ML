(*  Title:      Pure/drule.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Derived rules and other operations on theorems.
*)

infix 0 RS RSN RL RLN MRS MRL COMP;

signature DRULE =
sig
  val dest_implies      : cterm -> cterm * cterm
  val skip_flexpairs	: cterm -> cterm
  val strip_imp_prems	: cterm -> cterm list
  val cprems_of		: thm -> cterm list
  val read_insts	:
          Sign.sg -> (indexname -> typ option) * (indexname -> sort option)
                  -> (indexname -> typ option) * (indexname -> sort option)
                  -> string list -> (string*string)list
                  -> (indexname*ctyp)list * (cterm*cterm)list
  val types_sorts: thm -> (indexname-> typ option) * (indexname-> sort option)
  val forall_intr_list	: cterm list -> thm -> thm
  val forall_intr_frees	: thm -> thm
  val forall_intr_vars	: thm -> thm
  val forall_elim_list	: cterm list -> thm -> thm
  val forall_elim_var	: int -> thm -> thm
  val forall_elim_vars	: int -> thm -> thm
  val freeze_thaw	: thm -> thm * (thm -> thm)
  val implies_elim_list	: thm -> thm list -> thm
  val implies_intr_list	: cterm list -> thm -> thm
  val zero_var_indexes	: thm -> thm
  val standard		: thm -> thm
  val rotate_prems      : int -> thm -> thm
  val assume_ax		: theory -> string -> thm
  val RSN		: thm * (int * thm) -> thm
  val RS		: thm * thm -> thm
  val RLN		: thm list * (int * thm list) -> thm list
  val RL		: thm list * thm list -> thm list
  val MRS		: thm list * thm -> thm
  val MRL		: thm list list * thm list -> thm list
  val compose		: thm * int * thm -> thm list
  val COMP		: thm * thm -> thm
  val read_instantiate_sg: Sign.sg -> (string*string)list -> thm -> thm
  val read_instantiate	: (string*string)list -> thm -> thm
  val cterm_instantiate	: (cterm*cterm)list -> thm -> thm
  val weak_eq_thm	: thm * thm -> bool
  val eq_thm_sg		: thm * thm -> bool
  val size_of_thm	: thm -> int
  val reflexive_thm	: thm
  val symmetric_thm	: thm
  val transitive_thm	: thm
  val refl_implies      : thm
  val rewrite_rule_aux	: (meta_simpset -> thm -> thm option) -> thm list -> thm -> thm
  val rewrite_thm	: bool * bool -> (meta_simpset -> thm -> thm option)
	-> meta_simpset -> thm -> thm
  val rewrite_goals_rule_aux: (meta_simpset -> thm -> thm option) -> thm list -> thm -> thm
  val rewrite_goal_rule	: bool * bool -> (meta_simpset -> thm -> thm option)
        -> meta_simpset -> int -> thm -> thm

  val equal_abs_elim	: cterm  -> thm -> thm
  val equal_abs_elim_list: cterm list -> thm -> thm
  val flexpair_abs_elim_list: cterm list -> thm -> thm
  val asm_rl		: thm
  val cut_rl		: thm
  val revcut_rl		: thm
  val thin_rl		: thm
  val triv_forall_equality: thm
  val swap_prems_rl     : thm
  val equal_intr_rule   : thm
  val instantiate': ctyp option list -> cterm option list -> thm -> thm
end;

structure Drule : DRULE =
struct


(** some cterm->cterm operations: much faster than calling cterm_of! **)

(** SAME NAMES as in structure Logic: use compound identifiers! **)

(*dest_implies for cterms. Note T=prop below*)
fun dest_implies ct =
    case term_of ct of 
	(Const("==>", _) $ _ $ _) => 
	    let val (ct1,ct2) = dest_comb ct
	    in  (#2 (dest_comb ct1), ct2)  end	     
      | _ => raise TERM ("dest_implies", [term_of ct]) ;


(*Discard flexflex pairs; return a cterm*)
fun skip_flexpairs ct =
    case term_of ct of
	(Const("==>", _) $ (Const("=?=",_)$_$_) $ _) =>
	    skip_flexpairs (#2 (dest_implies ct))
      | _ => ct;

(* A1==>...An==>B  goes to  [A1,...,An], where B is not an implication *)
fun strip_imp_prems ct =
    let val (cA,cB) = dest_implies ct
    in  cA :: strip_imp_prems cB  end
    handle TERM _ => [];

(* A1==>...An==>B  goes to B, where B is not an implication *)
fun strip_imp_concl ct =
    case term_of ct of (Const("==>", _) $ _ $ _) => 
	strip_imp_concl (#2 (dest_comb ct))
  | _ => ct;

(*The premises of a theorem, as a cterm list*)
val cprems_of = strip_imp_prems o skip_flexpairs o cprop_of;


(** reading of instantiations **)

fun indexname cs = case Syntax.scan_varname cs of (v,[]) => v
        | _ => error("Lexical error in variable name " ^ quote (implode cs));

fun absent ixn =
  error("No such variable in term: " ^ Syntax.string_of_vname ixn);

fun inst_failure ixn =
  error("Instantiation of " ^ Syntax.string_of_vname ixn ^ " fails");

fun read_insts sign (rtypes,rsorts) (types,sorts) used insts =
let val {tsig,...} = Sign.rep_sg sign
    fun split([],tvs,vs) = (tvs,vs)
      | split((sv,st)::l,tvs,vs) = (case explode sv of
                  "'"::cs => split(l,(indexname cs,st)::tvs,vs)
                | cs => split(l,tvs,(indexname cs,st)::vs));
    val (tvs,vs) = split(insts,[],[]);
    fun readT((a,i),st) =
        let val ixn = ("'" ^ a,i);
            val S = case rsorts ixn of Some S => S | None => absent ixn;
            val T = Sign.read_typ (sign,sorts) st;
        in if Type.typ_instance(tsig,T,TVar(ixn,S)) then (ixn,T)
           else inst_failure ixn
        end
    val tye = map readT tvs;
    fun mkty(ixn,st) = (case rtypes ixn of
                          Some T => (ixn,(st,typ_subst_TVars tye T))
                        | None => absent ixn);
    val ixnsTs = map mkty vs;
    val ixns = map fst ixnsTs
    and sTs  = map snd ixnsTs
    val (cts,tye2) = read_def_cterms(sign,types,sorts) used false sTs;
    fun mkcVar(ixn,T) =
        let val U = typ_subst_TVars tye2 T
        in cterm_of sign (Var(ixn,U)) end
    val ixnTs = ListPair.zip(ixns, map snd sTs)
in (map (fn (ixn,T) => (ixn,ctyp_of sign T)) (tye2 @ tye),
    ListPair.zip(map mkcVar ixnTs,cts))
end;


(*** Find the type (sort) associated with a (T)Var or (T)Free in a term
     Used for establishing default types (of variables) and sorts (of
     type variables) when reading another term.
     Index -1 indicates that a (T)Free rather than a (T)Var is wanted.
***)

fun types_sorts thm =
    let val {prop,hyps,...} = rep_thm thm;
        val big = list_comb(prop,hyps); (* bogus term! *)
        val vars = map dest_Var (term_vars big);
        val frees = map dest_Free (term_frees big);
        val tvars = term_tvars big;
        val tfrees = term_tfrees big;
        fun typ(a,i) = if i<0 then assoc(frees,a) else assoc(vars,(a,i));
        fun sort(a,i) = if i<0 then assoc(tfrees,a) else assoc(tvars,(a,i));
    in (typ,sort) end;

(** Standardization of rules **)

(*Generalization over a list of variables, IGNORING bad ones*)
fun forall_intr_list [] th = th
  | forall_intr_list (y::ys) th =
        let val gth = forall_intr_list ys th
        in  forall_intr y gth   handle THM _ =>  gth  end;

(*Generalization over all suitable Free variables*)
fun forall_intr_frees th =
    let val {prop,sign,...} = rep_thm th
    in  forall_intr_list
         (map (cterm_of sign) (sort (make_ord atless) (term_frees prop)))
         th
    end;

(*Replace outermost quantified variable by Var of given index.
    Could clash with Vars already present.*)
fun forall_elim_var i th =
    let val {prop,sign,...} = rep_thm th
    in case prop of
          Const("all",_) $ Abs(a,T,_) =>
              forall_elim (cterm_of sign (Var((a,i), T)))  th
        | _ => raise THM("forall_elim_var", i, [th])
    end;

(*Repeat forall_elim_var until all outer quantifiers are removed*)
fun forall_elim_vars i th =
    forall_elim_vars i (forall_elim_var i th)
        handle THM _ => th;

(*Specialization over a list of cterms*)
fun forall_elim_list cts th = foldr (uncurry forall_elim) (rev cts, th);

(* maps [A1,...,An], B   to   [| A1;...;An |] ==> B  *)
fun implies_intr_list cAs th = foldr (uncurry implies_intr) (cAs,th);

(* maps [| A1;...;An |] ==> B and [A1,...,An]   to   B *)
fun implies_elim_list impth ths = foldl (uncurry implies_elim) (impth,ths);

(*Reset Var indexes to zero, renaming to preserve distinctness*)
fun zero_var_indexes th =
    let val {prop,sign,...} = rep_thm th;
        val vars = term_vars prop
        val bs = foldl add_new_id ([], map (fn Var((a,_),_)=>a) vars)
        val inrs = add_term_tvars(prop,[]);
        val nms' = rev(foldl add_new_id ([], map (#1 o #1) inrs));
        val tye = ListPair.map (fn ((v,rs),a) => (v, TVar((a,0),rs)))
	             (inrs, nms')
        val ctye = map (fn (v,T) => (v,ctyp_of sign T)) tye;
        fun varpairs([],[]) = []
          | varpairs((var as Var(v,T)) :: vars, b::bs) =
                let val T' = typ_subst_TVars tye T
                in (cterm_of sign (Var(v,T')),
                    cterm_of sign (Var((b,0),T'))) :: varpairs(vars,bs)
                end
          | varpairs _ = raise TERM("varpairs", []);
    in instantiate (ctye, varpairs(vars,rev bs)) th end;


(*Standard form of object-rule: no hypotheses, Frees, or outer quantifiers;
    all generality expressed by Vars having index 0.*)
fun standard th =
  let val {maxidx,...} = rep_thm th
  in
    th |> implies_intr_hyps
       |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
       |> Thm.strip_shyps |> Thm.implies_intr_shyps
       |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;


(*Convert all Vars in a theorem to Frees.  Also return a function for 
  reversing that operation.  DOES NOT WORK FOR TYPE VARIABLES.
  Similar code in type/freeze_thaw*)
fun freeze_thaw th =
  let val fth = freezeT th
      val {prop,sign,...} = rep_thm fth
      val used = add_term_names (prop, [])
      and vars = term_vars prop
      fun newName (Var(ix,_), (pairs,used)) = 
	    let val v = variant used (string_of_indexname ix)
	    in  ((ix,v)::pairs, v::used)  end;
      val (alist, _) = foldr newName (vars, ([], used))
      fun mk_inst (Var(v,T)) = 
	  (cterm_of sign (Var(v,T)),
	   cterm_of sign (Free(the (assoc(alist,v)), T)))
      val insts = map mk_inst vars
      fun thaw th' = 
	  th' |> forall_intr_list (map #2 insts)
	      |> forall_elim_list (map #1 insts)
  in  (instantiate ([],insts) fth, thaw)  end;


(*Rotates a rule's premises to the left by k.  Does nothing if k=0 or
  if k equals the number of premises.  Useful, for instance, with etac.
  Similar to tactic/defer_tac*)
fun rotate_prems k rl = 
    let val (rl',thaw) = freeze_thaw rl
	val hyps = strip_imp_prems (adjust_maxidx (cprop_of rl'))
	val hyps' = List.drop(hyps, k)
    in  implies_elim_list rl' (map assume hyps)
        |> implies_intr_list (hyps' @ List.take(hyps, k))
        |> thaw |> varifyT
    end;


(*Assume a new formula, read following the same conventions as axioms.
  Generalizes over Free variables,
  creates the assumption, and then strips quantifiers.
  Example is [| ALL x:?A. ?P(x) |] ==> [| ?P(?a) |]
             [ !(A,P,a)[| ALL x:A. P(x) |] ==> [| P(a) |] ]    *)
fun assume_ax thy sP =
    let val sign = sign_of thy
        val prop = Logic.close_form (term_of (read_cterm sign (sP, propT)))
    in forall_elim_vars 0 (assume (cterm_of sign prop))  end;

(*Resolution: exactly one resolvent must be produced.*)
fun tha RSN (i,thb) =
  case Seq.chop (2, biresolution false [(false,tha)] i thb) of
      ([th],_) => th
    | ([],_)   => raise THM("RSN: no unifiers", i, [tha,thb])
    |      _   => raise THM("RSN: multiple unifiers", i, [tha,thb]);

(*resolution: P==>Q, Q==>R gives P==>R. *)
fun tha RS thb = tha RSN (1,thb);

(*For joining lists of rules*)
fun thas RLN (i,thbs) =
  let val resolve = biresolution false (map (pair false) thas) i
      fun resb thb = Seq.list_of (resolve thb) handle THM _ => []
  in  List.concat (map resb thbs)  end;

fun thas RL thbs = thas RLN (1,thbs);

(*Resolve a list of rules against bottom_rl from right to left;
  makes proof trees*)
fun rls MRS bottom_rl =
  let fun rs_aux i [] = bottom_rl
        | rs_aux i (rl::rls) = rl RSN (i, rs_aux (i+1) rls)
  in  rs_aux 1 rls  end;

(*As above, but for rule lists*)
fun rlss MRL bottom_rls =
  let fun rs_aux i [] = bottom_rls
        | rs_aux i (rls::rlss) = rls RLN (i, rs_aux (i+1) rlss)
  in  rs_aux 1 rlss  end;

(*compose Q and [...,Qi,Q(i+1),...]==>R to [...,Q(i+1),...]==>R
  with no lifting or renaming!  Q may contain ==> or meta-quants
  ALWAYS deletes premise i *)
fun compose(tha,i,thb) =
    Seq.list_of (bicompose false (false,tha,0) i thb);

(*compose Q and [Q1,Q2,...,Qk]==>R to [Q2,...,Qk]==>R getting unique result*)
fun tha COMP thb =
    case compose(tha,1,thb) of
        [th] => th
      | _ =>   raise THM("COMP", 1, [tha,thb]);

(*Instantiate theorem th, reading instantiations under signature sg*)
fun read_instantiate_sg sg sinsts th =
    let val ts = types_sorts th;
        val used = add_term_tvarnames(#prop(rep_thm th),[]);
    in  instantiate (read_insts sg ts ts used sinsts) th  end;

(*Instantiate theorem th, reading instantiations under theory of th*)
fun read_instantiate sinsts th =
    read_instantiate_sg (#sign (rep_thm th)) sinsts th;


(*Left-to-right replacements: tpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms, inferring type instantiations. *)
local
  fun add_types ((ct,cu), (sign,tye,maxidx)) =
    let val {sign=signt, t=t, T= T, maxidx=maxt,...} = rep_cterm ct
        and {sign=signu, t=u, T= U, maxidx=maxu,...} = rep_cterm cu;
        val maxi = Int.max(maxidx, Int.max(maxt, maxu));
        val sign' = Sign.merge(sign, Sign.merge(signt, signu))
        val (tye',maxi') = Type.unify (#tsig(Sign.rep_sg sign')) maxi tye (T,U)
          handle Type.TUNIFY => raise TYPE("add_types", [T,U], [t,u])
    in  (sign', tye', maxi')  end;
in
fun cterm_instantiate ctpairs0 th =
  let val (sign,tye,_) = foldr add_types (ctpairs0, (#sign(rep_thm th),[],0))
      val tsig = #tsig(Sign.rep_sg sign);
      fun instT(ct,cu) = let val inst = subst_TVars tye
                         in (cterm_fun inst ct, cterm_fun inst cu) end
      fun ctyp2 (ix,T) = (ix, ctyp_of sign T)
  in  instantiate (map ctyp2 tye, map instT ctpairs0) th  end
  handle TERM _ =>
           raise THM("cterm_instantiate: incompatible signatures",0,[th])
       | TYPE (msg, _, _) => raise THM("cterm_instantiate: " ^ msg, 0, [th])
end;


(** theorem equality **)

(*Do the two theorems have the same signature?*)
fun eq_thm_sg (th1,th2) = Sign.eq_sg(#sign(rep_thm th1), #sign(rep_thm th2));

(*Useful "distance" function for BEST_FIRST*)
val size_of_thm = size_of_term o #prop o rep_thm;


(** Mark Staples's weaker version of eq_thm: ignores variable renaming and
    (some) type variable renaming **)

 (* Can't use term_vars, because it sorts the resulting list of variable names.
    We instead need the unique list noramlised by the order of appearance
    in the term. *)
fun term_vars' (t as Var(v,T)) = [t]
  | term_vars' (Abs(_,_,b)) = term_vars' b
  | term_vars' (f$a) = (term_vars' f) @ (term_vars' a)
  | term_vars' _ = [];

fun forall_intr_vars th =
  let val {prop,sign,...} = rep_thm th;
      val vars = distinct (term_vars' prop);
  in forall_intr_list (map (cterm_of sign) vars) th end;

fun weak_eq_thm (tha,thb) =
    eq_thm(forall_intr_vars (freezeT tha), forall_intr_vars (freezeT thb));



(*** Meta-Rewriting Rules ***)

val proto_sign = sign_of ProtoPure.thy;

fun read_prop s = read_cterm proto_sign (s, propT);

fun store_thm name thm = PureThy.smart_store_thm (name, standard thm);

val reflexive_thm =
  let val cx = cterm_of proto_sign (Var(("x",0),TVar(("'a",0),logicS)))
  in store_thm "reflexive" (Thm.reflexive cx) end;

val symmetric_thm =
  let val xy = read_prop "x::'a::logic == y"
  in store_thm "symmetric" 
      (Thm.implies_intr_hyps(Thm.symmetric(Thm.assume xy)))
   end;

val transitive_thm =
  let val xy = read_prop "x::'a::logic == y"
      val yz = read_prop "y::'a::logic == z"
      val xythm = Thm.assume xy and yzthm = Thm.assume yz
  in store_thm "transitive" (Thm.implies_intr yz (Thm.transitive xythm yzthm))
  end;

(** Below, a "conversion" has type cterm -> thm **)

val refl_implies = reflexive (cterm_of proto_sign implies);

(*In [A1,...,An]==>B, rewrite the selected A's only -- for rewrite_goals_tac*)
(*Do not rewrite flex-flex pairs*)
fun goals_conv pred cv =
  let fun gconv i ct =
        let val (A,B) = dest_implies ct
            val (thA,j) = case term_of A of
                  Const("=?=",_)$_$_ => (reflexive A, i)
                | _ => (if pred i then cv A else reflexive A, i+1)
        in  combination (combination refl_implies thA) (gconv j B) end
        handle TERM _ => reflexive ct
  in gconv 1 end;

(*Use a conversion to transform a theorem*)
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;

(*rewriting conversion*)
fun rew_conv mode prover mss = rewrite_cterm mode mss prover;

(*Rewrite a theorem*)
fun rewrite_rule_aux _ []   th = th
  | rewrite_rule_aux prover thms th =
      fconv_rule (rew_conv (true,false) prover (Thm.mss_of thms)) th;

fun rewrite_thm mode prover mss = fconv_rule (rew_conv mode prover mss);

(*Rewrite the subgoals of a proof state (represented by a theorem) *)
fun rewrite_goals_rule_aux _ []   th = th
  | rewrite_goals_rule_aux prover thms th =
      fconv_rule (goals_conv (K true) (rew_conv (true, true) prover
        (Thm.mss_of thms))) th;

(*Rewrite the subgoal of a proof state (represented by a theorem) *)
fun rewrite_goal_rule mode prover mss i thm =
  if 0 < i  andalso  i <= nprems_of thm
  then fconv_rule (goals_conv (fn j => j=i) (rew_conv mode prover mss)) thm
  else raise THM("rewrite_goal_rule",i,[thm]);


(** Derived rules mainly for METAHYPS **)

(*Given the term "a", takes (%x.t)==(%x.u) to t[a/x]==u[a/x]*)
fun equal_abs_elim ca eqth =
  let val {sign=signa, t=a, ...} = rep_cterm ca
      and combth = combination eqth (reflexive ca)
      val {sign,prop,...} = rep_thm eqth
      val (abst,absu) = Logic.dest_equals prop
      val cterm = cterm_of (Sign.merge (sign,signa))
  in  transitive (symmetric (beta_conversion (cterm (abst$a))))
           (transitive combth (beta_conversion (cterm (absu$a))))
  end
  handle THM _ => raise THM("equal_abs_elim", 0, [eqth]);

(*Calling equal_abs_elim with multiple terms*)
fun equal_abs_elim_list cts th = foldr (uncurry equal_abs_elim) (rev cts, th);

local
  val alpha = TVar(("'a",0), [])     (*  type ?'a::{}  *)
  fun err th = raise THM("flexpair_inst: ", 0, [th])
  fun flexpair_inst def th =
    let val {prop = Const _ $ t $ u,  sign,...} = rep_thm th
        val cterm = cterm_of sign
        fun cvar a = cterm(Var((a,0),alpha))
        val def' = cterm_instantiate [(cvar"t", cterm t), (cvar"u", cterm u)]
                   def
    in  equal_elim def' th
    end
    handle THM _ => err th | bind => err th
in
val flexpair_intr = flexpair_inst (symmetric ProtoPure.flexpair_def)
and flexpair_elim = flexpair_inst ProtoPure.flexpair_def
end;

(*Version for flexflex pairs -- this supports lifting.*)
fun flexpair_abs_elim_list cts =
    flexpair_intr o equal_abs_elim_list cts o flexpair_elim;


(*** Some useful meta-theorems ***)

(*The rule V/V, obtains assumption solving for eresolve_tac*)
val asm_rl =
  store_thm "asm_rl" (trivial(read_prop "PROP ?psi"));

(*Meta-level cut rule: [| V==>W; V |] ==> W *)
val cut_rl =
  store_thm "cut_rl"
    (trivial(read_prop "PROP ?psi ==> PROP ?theta"));

(*Generalized elim rule for one conclusion; cut_rl with reversed premises:
     [| PROP V;  PROP V ==> PROP W |] ==> PROP W *)
val revcut_rl =
  let val V = read_prop "PROP V"
      and VW = read_prop "PROP V ==> PROP W";
  in
    store_thm "revcut_rl"
      (implies_intr V (implies_intr VW (implies_elim (assume VW) (assume V))))
  end;

(*for deleting an unwanted assumption*)
val thin_rl =
  let val V = read_prop "PROP V"
      and W = read_prop "PROP W";
  in  store_thm "thin_rl" (implies_intr V (implies_intr W (assume W)))
  end;

(* (!!x. PROP ?V) == PROP ?V       Allows removal of redundant parameters*)
val triv_forall_equality =
  let val V  = read_prop "PROP V"
      and QV = read_prop "!!x::'a. PROP V"
      and x  = read_cterm proto_sign ("x", TFree("'a",logicS));
  in
    store_thm "triv_forall_equality"
      (equal_intr (implies_intr QV (forall_elim x (assume QV)))
        (implies_intr V  (forall_intr x (assume V))))
  end;

(* (PROP ?PhiA ==> PROP ?PhiB ==> PROP ?Psi) ==>
   (PROP ?PhiB ==> PROP ?PhiA ==> PROP ?Psi)
   `thm COMP swap_prems_rl' swaps the first two premises of `thm'
*)
val swap_prems_rl =
  let val cmajor = read_prop "PROP PhiA ==> PROP PhiB ==> PROP Psi";
      val major = assume cmajor;
      val cminor1 = read_prop "PROP PhiA";
      val minor1 = assume cminor1;
      val cminor2 = read_prop "PROP PhiB";
      val minor2 = assume cminor2;
  in store_thm "swap_prems_rl"
       (implies_intr cmajor (implies_intr cminor2 (implies_intr cminor1
         (implies_elim (implies_elim major minor1) minor2))))
  end;

(* [| PROP ?phi ==> PROP ?psi; PROP ?psi ==> PROP ?phi |]
   ==> PROP ?phi == PROP ?psi
   Introduction rule for == as a meta-theorem.  
*)
val equal_intr_rule =
  let val PQ = read_prop "PROP phi ==> PROP psi"
      and QP = read_prop "PROP psi ==> PROP phi"
  in
    store_thm "equal_intr_rule"
      (implies_intr PQ (implies_intr QP (equal_intr (assume PQ) (assume QP))))
  end;



(** instantiate' rule **)

(* collect vars *)

val add_tvarsT = foldl_atyps (fn (vs, TVar v) => v ins vs | (vs, _) => vs);
val add_tvars = foldl_types add_tvarsT;
val add_vars = foldl_aterms (fn (vs, Var v) => v ins vs | (vs, _) => vs);

fun tvars_of thm = rev (add_tvars ([], #prop (Thm.rep_thm thm)));
fun vars_of thm = rev (add_vars ([], #prop (Thm.rep_thm thm)));


(* instantiate by left-to-right occurrence of variables *)

fun instantiate' cTs cts thm =
  let
    fun err msg =
      raise TYPE ("instantiate': " ^ msg,
        mapfilter (apsome Thm.typ_of) cTs,
        mapfilter (apsome Thm.term_of) cts);

    fun inst_of (v, ct) =
      (Thm.cterm_of (#sign (Thm.rep_cterm ct)) (Var v), ct)
        handle TYPE (msg, _, _) => err msg;

    fun zip_vars _ [] = []
      | zip_vars (_ :: vs) (None :: opt_ts) = zip_vars vs opt_ts
      | zip_vars (v :: vs) (Some t :: opt_ts) = (v, t) :: zip_vars vs opt_ts
      | zip_vars [] _ = err "more instantiations than variables in thm";

    (*instantiate types first!*)
    val thm' =
      if forall is_none cTs then thm
      else Thm.instantiate (zip_vars (map fst (tvars_of thm)) cTs, []) thm;
    in
      if forall is_none cts then thm'
      else Thm.instantiate ([], map inst_of (zip_vars (vars_of thm') cts)) thm'
    end;


end;

open Drule;
