(*  Title:      ZF/ind-syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Abstract Syntax functions for Inductive Definitions
*)

(*The structure protects these items from redeclaration (somewhat!).  The 
  datatype definitions in theory files refer to these items by name!
*)
structure Ind_Syntax =
struct

(*Print tracing messages during processing of "inductive" theory sections*)
val trace = ref false;

fun traceIt msg ct = 
    if !trace then (writeln (msg ^ string_of_cterm ct); ct)
    else ct;

(** Abstract syntax definitions for ZF **)

val iT = Type("i",[]);

val mem_const = Const("op :", [iT,iT]--->FOLogic.oT);

(*Creates All(%v.v:A --> P(v)) rather than Ball(A,P) *)
fun mk_all_imp (A,P) = 
    FOLogic.all_const iT $ 
      Abs("v", iT, FOLogic.imp $ (mem_const $ Bound 0 $ A) $ 
	           betapply(P, Bound 0));

val Part_const = Const("Part", [iT,iT-->iT]--->iT);

val apply_const = Const("op `", [iT,iT]--->iT);

val Vrecursor_const = Const("Univ.Vrecursor", [[iT,iT]--->iT, iT]--->iT);

val Collect_const = Const("Collect", [iT, iT-->FOLogic.oT] ---> iT);
fun mk_Collect (a,D,t) = Collect_const $ D $ absfree(a, iT, t);

(*simple error-checking in the premises of an inductive definition*)
fun chk_prem rec_hd (Const("op &",_) $ _ $ _) =
        error"Premises may not be conjuctive"
  | chk_prem rec_hd (Const("op :",_) $ t $ X) = 
        deny (Logic.occs(rec_hd,t)) "Recursion term on left of member symbol"
  | chk_prem rec_hd t = 
        deny (Logic.occs(rec_hd,t)) "Recursion term in side formula";

(*Return the conclusion of a rule, of the form t:X*)
fun rule_concl rl = 
    let val Const("Trueprop",_) $ (Const("op :",_) $ t $ X) = 
                Logic.strip_imp_concl rl
    in  (t,X)  end;

(*As above, but return error message if bad*)
fun rule_concl_msg sign rl = rule_concl rl
    handle Bind => error ("Ill-formed conclusion of introduction rule: " ^ 
                          Sign.string_of_term sign rl);

(*For deriving cases rules.  CollectD2 discards the domain, which is redundant;
  read_instantiate replaces a propositional variable by a formula variable*)
val equals_CollectD = 
    read_instantiate [("W","?Q")]
        (make_elim (equalityD1 RS subsetD RS CollectD2));


(** For datatype definitions **)

(*Constructor name, type, mixfix info;
  internal name from mixfix, datatype sets, full premises*)
type constructor_spec = 
    ((string * typ * mixfix) * string * term list * term list);

fun dest_mem (Const("op :",_) $ x $ A) = (x,A)
  | dest_mem _ = error "Constructor specifications must have the form x:A";

(*read a constructor specification*)
fun read_construct sign (id, sprems, syn) =
    let val prems = map (Sign.simple_read_term sign FOLogic.oT) sprems
        val args = map (#1 o dest_mem) prems
        val T = (map (#2 o dest_Free) args) ---> iT
                handle TERM _ => error 
                    "Bad variable in constructor specification"
        val name = Syntax.const_name id syn  (*handle infix constructors*)
    in ((id,T,syn), name, args, prems) end;

val read_constructs = map o map o read_construct;

(*convert constructor specifications into introduction rules*)
fun mk_intr_tms sg (rec_tm, constructs) =
  let
    fun mk_intr ((id,T,syn), name, args, prems) =
      Logic.list_implies
        (map FOLogic.mk_Trueprop prems,
	 FOLogic.mk_Trueprop
	    (mem_const $ list_comb (Const (Sign.full_name sg name, T), args)
	               $ rec_tm))
  in  map mk_intr constructs  end;

fun mk_all_intr_tms sg arg = List.concat (ListPair.map (mk_intr_tms sg) arg);

fun mk_Un (t1, t2) = Const("op Un", [iT,iT]--->iT) $ t1 $ t2;

val empty       = Const("0", iT)
and univ        = Const("Univ.univ", iT-->iT)
and quniv       = Const("QUniv.quniv", iT-->iT);

(*Make a datatype's domain: form the union of its set parameters*)
fun union_params (rec_tm, cs) =
  let val (_,args) = strip_comb rec_tm
      fun is_ind arg = (type_of arg = iT)
  in  case filter is_ind (args @ cs) of
         []     => empty
       | u_args => fold_bal mk_Un u_args
  end;

(*univ or quniv constitutes the sum domain for mutual recursion;
  it is applied to the datatype parameters and to Consts occurring in the
  definition other than Nat.nat and the datatype sets themselves.
  FIXME: could insert all constant set expressions, e.g. nat->nat.*)
fun data_domain co (rec_tms, con_ty_lists) = 
    let val rec_names = (*nat doesn't have to be added*)
	    "Nat.nat" :: map (#1 o dest_Const o head_of) rec_tms
	val u = if co then quniv else univ
	fun is_OK (Const(a,T)) = not (a mem_string rec_names)
	  | is_OK _            = false
	val add_term_consts_2 =
	    foldl_aterms (fn (cs, Const c) => Const c ins cs | (cs, _) => cs);
	fun fourth (_, name, args, prems) = prems
	fun add_consts_in_cts cts = 
	    foldl (foldl add_term_consts_2) ([], map fourth (flat cts));
	val cs = filter is_OK (add_consts_in_cts con_ty_lists)
    in  u $ union_params (hd rec_tms, cs)  end;


(*Could go to FOL, but it's hardly general*)
val def_swap_iff = prove_goal IFOL.thy "a==b ==> a=c <-> c=b"
 (fn [def] => [(rewtac def), (rtac iffI 1), (REPEAT (etac sym 1))]);

val def_trans = prove_goal IFOL.thy "[| f==g;  g(a)=b |] ==> f(a)=b"
  (fn [rew,prem] => [ rewtac rew, rtac prem 1 ]);

(*Delete needless equality assumptions*)
val refl_thin = prove_goal IFOL.thy "!!P. [| a=a;  P |] ==> P"
     (fn _ => [assume_tac 1]);

(*Includes rules for succ and Pair since they are common constructions*)
val elim_rls = [asm_rl, FalseE, succ_neq_0, sym RS succ_neq_0, 
                Pair_neq_0, sym RS Pair_neq_0, Pair_inject,
                make_elim succ_inject, 
                refl_thin, conjE, exE, disjE];


(*From HOL/ex/meson.ML: raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

fun gen_make_elim elim_rls rl = 
      standard (tryres (rl, elim_rls @ [revcut_rl]));

(*Turns iff rules into safe elimination rules*)
fun mk_free_SEs iffs = map (gen_make_elim [conjE,FalseE]) (iffs RL [iffD1]);


end;


(*For convenient access by the user*)
val trace_induct = Ind_Syntax.trace;
