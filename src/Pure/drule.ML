(*  Title:      Pure/drule.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Derived rules and other operations on theorems and theories
*)

infix 0 RS RSN RL RLN MRS MRL COMP;

signature DRULE =
  sig
  structure Thm : THM
  local open Thm  in
  val asm_rl: thm
  val assume_ax: theory -> string -> thm
  val COMP: thm * thm -> thm
  val compose: thm * int * thm -> thm list
  val cterm_instantiate: (cterm*cterm)list -> thm -> thm
  val cut_rl: thm
  val equal_abs_elim: cterm  -> thm -> thm
  val equal_abs_elim_list: cterm list -> thm -> thm
  val eq_thm: thm * thm -> bool
  val eq_thm_sg: thm * thm -> bool
  val flexpair_abs_elim_list: cterm list -> thm -> thm
  val forall_intr_list: cterm list -> thm -> thm
  val forall_intr_frees: thm -> thm
  val forall_elim_list: cterm list -> thm -> thm
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val implies_elim_list: thm -> thm list -> thm
  val implies_intr_list: cterm list -> thm -> thm
  val MRL: thm list list * thm list -> thm list
  val MRS: thm list * thm -> thm
  val pprint_cterm: cterm -> pprint_args -> unit
  val pprint_ctyp: ctyp -> pprint_args -> unit
  val pprint_theory: theory -> pprint_args -> unit
  val pprint_thm: thm -> pprint_args -> unit
  val pretty_thm: thm -> Sign.Syntax.Pretty.T
  val print_cterm: cterm -> unit
  val print_ctyp: ctyp -> unit
  val print_goals: int -> thm -> unit
  val print_goals_ref: (int -> thm -> unit) ref
  val print_theory: theory -> unit
  val print_thm: thm -> unit
  val prth: thm -> thm
  val prthq: thm Sequence.seq -> thm Sequence.seq
  val prths: thm list -> thm list
  val read_instantiate: (string*string)list -> thm -> thm
  val read_instantiate_sg: Sign.sg -> (string*string)list -> thm -> thm
  val read_insts:
          Sign.sg -> (indexname -> typ option) * (indexname -> sort option)
                  -> (indexname -> typ option) * (indexname -> sort option)
                  -> (string*string)list
                  -> (indexname*ctyp)list * (cterm*cterm)list
  val reflexive_thm: thm
  val revcut_rl: thm
  val rewrite_goal_rule: bool*bool -> (meta_simpset -> thm -> thm option)
        -> meta_simpset -> int -> thm -> thm
  val rewrite_goals_rule: thm list -> thm -> thm
  val rewrite_rule: thm list -> thm -> thm
  val RS: thm * thm -> thm
  val RSN: thm * (int * thm) -> thm
  val RL: thm list * thm list -> thm list
  val RLN: thm list * (int * thm list) -> thm list
  val show_hyps: bool ref
  val size_of_thm: thm -> int
  val standard: thm -> thm
  val string_of_cterm: cterm -> string
  val string_of_ctyp: ctyp -> string
  val string_of_thm: thm -> string
  val symmetric_thm: thm
  val transitive_thm: thm
  val triv_forall_equality: thm
  val types_sorts: thm -> (indexname-> typ option) * (indexname-> sort option)
  val zero_var_indexes: thm -> thm
  end
  end;

functor DruleFun (structure Logic: LOGIC and Thm: THM): DRULE =
struct
structure Thm = Thm;
structure Sign = Thm.Sign;
structure Type = Sign.Type;
structure Pretty = Sign.Syntax.Pretty
local open Thm
in

(**** More derived rules and operations on theorems ****)

(** reading of instantiations **)

fun indexname cs = case Syntax.scan_varname cs of (v,[]) => v
        | _ => error("Lexical error in variable name " ^ quote (implode cs));

fun absent ixn =
  error("No such variable in term: " ^ Syntax.string_of_vname ixn);

fun inst_failure ixn =
  error("Instantiation of " ^ Syntax.string_of_vname ixn ^ " fails");

fun read_insts sign (rtypes,rsorts) (types,sorts) insts =
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
    fun add_cterm ((cts,tye), (ixn,st)) =
        let val T = case rtypes ixn of
                      Some T => typ_subst_TVars tye T
                    | None => absent ixn;
            val (ct,tye2) = read_def_cterm (sign,types,sorts) (st,T);
            val cv = cterm_of sign (Var(ixn,typ_subst_TVars tye2 T))
        in ((cv,ct)::cts,tye2 @ tye) end
    val (cterms,tye') = foldl add_cterm (([],tye), vs);
in (map (fn (ixn,T) => (ixn,ctyp_of sign T)) tye', cterms) end;



(*** Printing of theories, theorems, etc. ***)

(*If false, hypotheses are printed as dots*)
val show_hyps = ref true;

fun pretty_thm th =
let val {sign, hyps, prop,...} = rep_thm th
    val hsymbs = if null hyps then []
                 else if !show_hyps then
                      [Pretty.brk 2,
                       Pretty.lst("[","]") (map (Sign.pretty_term sign) hyps)]
                 else Pretty.str" [" :: map (fn _ => Pretty.str".") hyps @
                      [Pretty.str"]"];
in Pretty.blk(0, Sign.pretty_term sign prop :: hsymbs) end;

val string_of_thm = Pretty.string_of o pretty_thm;

val pprint_thm = Pretty.pprint o Pretty.quote o pretty_thm;


(** Top-level commands for printing theorems **)
val print_thm = writeln o string_of_thm;

fun prth th = (print_thm th; th);

(*Print and return a sequence of theorems, separated by blank lines. *)
fun prthq thseq =
  (Sequence.prints (fn _ => print_thm) 100000 thseq; thseq);

(*Print and return a list of theorems, separated by blank lines. *)
fun prths ths = (print_list_ln print_thm ths; ths);


(* other printing commands *)

fun pprint_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.pprint_typ sign T end;

fun string_of_ctyp cT =
  let val {sign, T} = rep_ctyp cT in Sign.string_of_typ sign T end;

val print_ctyp = writeln o string_of_ctyp;

fun pprint_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.pprint_term sign t end;

fun string_of_cterm ct =
  let val {sign, t, ...} = rep_cterm ct in Sign.string_of_term sign t end;

val print_cterm = writeln o string_of_cterm;


(* print theory *)

val pprint_theory = Sign.pprint_sg o sign_of;

fun print_theory thy =
  let
    fun prt_thm (name, thm) = Pretty.block
      [Pretty.str (name ^ ":"), Pretty.brk 1, Pretty.quote (pretty_thm thm)];

    val sg = sign_of thy;
    val axioms =        (* FIXME should rather fix axioms_of *)
      sort (fn ((x, _), (y, _)) => x <= y)
        (gen_distinct eq_fst (axioms_of thy));
  in
    Sign.print_sg sg;
    Pretty.writeln (Pretty.big_list "axioms:" (map prt_thm axioms))
  end;



(** Print thm A1,...,An/B in "goal style" -- premises as numbered subgoals **)

fun prettyprints es = writeln(Pretty.string_of(Pretty.blk(0,es)));

fun print_goals maxgoals th : unit =
let val {sign, hyps, prop,...} = rep_thm th;
    fun printgoals (_, []) = ()
      | printgoals (n, A::As) =
        let val prettyn = Pretty.str(" " ^ string_of_int n ^ ". ");
            val prettyA = Sign.pretty_term sign A
        in prettyprints[prettyn,prettyA];
           printgoals (n+1,As)
        end;
    fun prettypair(t,u) =
        Pretty.blk(0, [Sign.pretty_term sign t, Pretty.str" =?=", Pretty.brk 1,
                       Sign.pretty_term sign u]);
    fun printff [] = ()
      | printff tpairs =
         writeln("\nFlex-flex pairs:\n" ^
                 Pretty.string_of(Pretty.lst("","") (map prettypair tpairs)))
    val (tpairs,As,B) = Logic.strip_horn(prop);
    val ngoals = length As
in
   writeln (Sign.string_of_term sign B);
   if ngoals=0 then writeln"No subgoals!"
   else if ngoals>maxgoals
        then (printgoals (1, take(maxgoals,As));
              writeln("A total of " ^ string_of_int ngoals ^ " subgoals..."))
        else printgoals (1, As);
   printff tpairs
end;

(*"hook" for user interfaces: allows print_goals to be replaced*)
val print_goals_ref = ref print_goals;

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
         (map (cterm_of sign) (sort atless (term_frees prop)))
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
        val tye = map (fn ((v,rs),a) => (v, TVar((a,0),rs))) (inrs ~~ nms')
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
    in  varifyT (zero_var_indexes (forall_elim_vars(maxidx+1)
                         (forall_intr_frees(implies_intr_hyps th))))
    end;

(*Assume a new formula, read following the same conventions as axioms.
  Generalizes over Free variables,
  creates the assumption, and then strips quantifiers.
  Example is [| ALL x:?A. ?P(x) |] ==> [| ?P(?a) |]
             [ !(A,P,a)[| ALL x:A. P(x) |] ==> [| P(a) |] ]    *)
fun assume_ax thy sP =
    let val sign = sign_of thy
        val prop = Logic.close_form (term_of (read_cterm sign
                         (sP, propT)))
    in forall_elim_vars 0 (assume (cterm_of sign prop))  end;

(*Resolution: exactly one resolvent must be produced.*)
fun tha RSN (i,thb) =
  case Sequence.chop (2, biresolution false [(false,tha)] i thb) of
      ([th],_) => th
    | ([],_)   => raise THM("RSN: no unifiers", i, [tha,thb])
    |      _   => raise THM("RSN: multiple unifiers", i, [tha,thb]);

(*resolution: P==>Q, Q==>R gives P==>R. *)
fun tha RS thb = tha RSN (1,thb);

(*For joining lists of rules*)
fun thas RLN (i,thbs) =
  let val resolve = biresolution false (map (pair false) thas) i
      fun resb thb = Sequence.list_of_s (resolve thb) handle THM _ => []
  in  flat (map resb thbs)  end;

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
    Sequence.list_of_s (bicompose false (false,tha,0) i thb);

(*compose Q and [Q1,Q2,...,Qk]==>R to [Q2,...,Qk]==>R getting unique result*)
fun tha COMP thb =
    case compose(tha,1,thb) of
        [th] => th
      | _ =>   raise THM("COMP", 1, [tha,thb]);

(*Instantiate theorem th, reading instantiations under signature sg*)
fun read_instantiate_sg sg sinsts th =
    let val ts = types_sorts th;
    in  instantiate (read_insts sg ts ts sinsts) th  end;

(*Instantiate theorem th, reading instantiations under theory of th*)
fun read_instantiate sinsts th =
    read_instantiate_sg (#sign (rep_thm th)) sinsts th;


(*Left-to-right replacements: tpairs = [...,(vi,ti),...].
  Instantiates distinct Vars by terms, inferring type instantiations. *)
local
  fun add_types ((ct,cu), (sign,tye)) =
    let val {sign=signt, t=t, T= T, ...} = rep_cterm ct
        and {sign=signu, t=u, T= U, ...} = rep_cterm cu
        val sign' = Sign.merge(sign, Sign.merge(signt, signu))
        val tye' = Type.unify (#tsig(Sign.rep_sg sign')) ((T,U), tye)
          handle Type.TUNIFY => raise TYPE("add_types", [T,U], [t,u])
    in  (sign', tye')  end;
in
fun cterm_instantiate ctpairs0 th =
  let val (sign,tye) = foldr add_types (ctpairs0, (#sign(rep_thm th),[]))
      val tsig = #tsig(Sign.rep_sg sign);
      fun instT(ct,cu) = let val inst = subst_TVars tye
                         in (cterm_fun inst ct, cterm_fun inst cu) end
      fun ctyp2 (ix,T) = (ix, ctyp_of sign T)
  in  instantiate (map ctyp2 tye, map instT ctpairs0) th  end
  handle TERM _ =>
           raise THM("cterm_instantiate: incompatible signatures",0,[th])
       | TYPE _ => raise THM("cterm_instantiate: types", 0, [th])
end;


(** theorem equality test is exported and used by BEST_FIRST **)

(*equality of theorems uses equality of signatures and
  the a-convertible test for terms*)
fun eq_thm (th1,th2) =
    let val {sign=sg1, hyps=hyps1, prop=prop1, ...} = rep_thm th1
        and {sign=sg2, hyps=hyps2, prop=prop2, ...} = rep_thm th2
    in  Sign.eq_sg (sg1,sg2) andalso
        aconvs(hyps1,hyps2) andalso
        prop1 aconv prop2
    end;

(*Do the two theorems have the same signature?*)
fun eq_thm_sg (th1,th2) = Sign.eq_sg(#sign(rep_thm th1), #sign(rep_thm th2));

(*Useful "distance" function for BEST_FIRST*)
val size_of_thm = size_of_term o #prop o rep_thm;


(*** Meta-Rewriting Rules ***)


val reflexive_thm =
  let val cx = cterm_of Sign.pure (Var(("x",0),TVar(("'a",0),["logic"])))
  in Thm.reflexive cx end;

val symmetric_thm =
  let val xy = read_cterm Sign.pure ("x::'a::logic == y",propT)
  in standard(Thm.implies_intr_hyps(Thm.symmetric(Thm.assume xy))) end;

val transitive_thm =
  let val xy = read_cterm Sign.pure ("x::'a::logic == y",propT)
      val yz = read_cterm Sign.pure ("y::'a::logic == z",propT)
      val xythm = Thm.assume xy and yzthm = Thm.assume yz
  in standard(Thm.implies_intr yz (Thm.transitive xythm yzthm)) end;

(** Below, a "conversion" has type cterm -> thm **)

val refl_cimplies = reflexive (cterm_of Sign.pure implies);

(*In [A1,...,An]==>B, rewrite the selected A's only -- for rewrite_goals_tac*)
(*Do not rewrite flex-flex pairs*)
fun goals_conv pred cv =
  let fun gconv i ct =
        let val (A,B) = Thm.dest_cimplies ct
            val (thA,j) = case term_of A of
                  Const("=?=",_)$_$_ => (reflexive A, i)
                | _ => (if pred i then cv A else reflexive A, i+1)
        in  combination (combination refl_cimplies thA) (gconv j B) end
        handle TERM _ => reflexive ct
  in gconv 1 end;

(*Use a conversion to transform a theorem*)
fun fconv_rule cv th = equal_elim (cv (cprop_of th)) th;

(*rewriting conversion*)
fun rew_conv mode prover mss = rewrite_cterm mode mss prover;

(*Rewrite a theorem*)
fun rewrite_rule thms =
  fconv_rule (rew_conv (true,false) (K(K None)) (Thm.mss_of thms));

(*Rewrite the subgoals of a proof state (represented by a theorem) *)
fun rewrite_goals_rule thms =
  fconv_rule (goals_conv (K true) (rew_conv (true,false) (K(K None))
             (Thm.mss_of thms)));

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
  open Logic
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
val flexpair_intr = flexpair_inst (symmetric flexpair_def)
and flexpair_elim = flexpair_inst flexpair_def
end;

(*Version for flexflex pairs -- this supports lifting.*)
fun flexpair_abs_elim_list cts =
    flexpair_intr o equal_abs_elim_list cts o flexpair_elim;


(*** Some useful meta-theorems ***)

(*The rule V/V, obtains assumption solving for eresolve_tac*)
val asm_rl = trivial(read_cterm Sign.pure ("PROP ?psi",propT));

(*Meta-level cut rule: [| V==>W; V |] ==> W *)
val cut_rl = trivial(read_cterm Sign.pure
        ("PROP ?psi ==> PROP ?theta", propT));

(*Generalized elim rule for one conclusion; cut_rl with reversed premises:
     [| PROP V;  PROP V ==> PROP W |] ==> PROP W *)
val revcut_rl =
  let val V = read_cterm Sign.pure ("PROP V", propT)
      and VW = read_cterm Sign.pure ("PROP V ==> PROP W", propT);
  in  standard (implies_intr V
                (implies_intr VW
                 (implies_elim (assume VW) (assume V))))
  end;

(* (!!x. PROP ?V) == PROP ?V       Allows removal of redundant parameters*)
val triv_forall_equality =
  let val V  = read_cterm Sign.pure ("PROP V", propT)
      and QV = read_cterm Sign.pure ("!!x::'a. PROP V", propT)
      and x  = read_cterm Sign.pure ("x", TFree("'a",["logic"]));
  in  standard (equal_intr (implies_intr QV (forall_elim x (assume QV)))
                           (implies_intr V  (forall_intr x (assume V))))
  end;

end
end;

