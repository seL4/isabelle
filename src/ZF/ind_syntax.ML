(*  Title:      ZF/ind_syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Abstract Syntax functions for Inductive Definitions.
*)

structure Ind_Syntax =
struct

(*Print tracing messages during processing of "inductive" theory sections*)
val trace = Unsynchronized.ref false;

fun traceIt msg thy t =
  if !trace then (tracing (msg ^ Syntax.string_of_term_global thy t); t)
  else t;


(** Abstract syntax definitions for ZF **)

val iT = Type("i",[]);

(*Creates All(%v.v:A --> P(v)) rather than Ball(A,P) *)
fun mk_all_imp (A,P) =
    FOLogic.all_const iT $
      Abs("v", iT, FOLogic.imp $ (@{const mem} $ Bound 0 $ A) $
	           Term.betapply(P, Bound 0));

fun mk_Collect (a, D, t) = @{const Collect} $ D $ absfree (a, iT, t);

(*simple error-checking in the premises of an inductive definition*)
fun chk_prem rec_hd (Const (@{const_name "op &"}, _) $ _ $ _) =
        error"Premises may not be conjuctive"
  | chk_prem rec_hd (Const (@{const_name mem}, _) $ t $ X) =
        (Logic.occs(rec_hd,t) andalso error "Recursion term on left of member symbol"; ())
  | chk_prem rec_hd t =
        (Logic.occs(rec_hd,t) andalso error "Recursion term in side formula"; ());

(*Return the conclusion of a rule, of the form t:X*)
fun rule_concl rl =
    let val Const (@{const_name Trueprop}, _) $ (Const (@{const_name mem}, _) $ t $ X) =
                Logic.strip_imp_concl rl
    in  (t,X)  end;

(*As above, but return error message if bad*)
fun rule_concl_msg sign rl = rule_concl rl
    handle Bind => error ("Ill-formed conclusion of introduction rule: " ^
                          Syntax.string_of_term_global sign rl);

(*For deriving cases rules.  CollectD2 discards the domain, which is redundant;
  read_instantiate replaces a propositional variable by a formula variable*)
val equals_CollectD =
    read_instantiate @{context} [(("W", 0), "?Q")]
        (make_elim (@{thm equalityD1} RS @{thm subsetD} RS @{thm CollectD2}));


(** For datatype definitions **)

(*Constructor name, type, mixfix info;
  internal name from mixfix, datatype sets, full premises*)
type constructor_spec =
    (string * typ * mixfix) * string * term list * term list;

fun dest_mem (Const (@{const_name mem}, _) $ x $ A) = (x, A)
  | dest_mem _ = error "Constructor specifications must have the form x:A";

(*read a constructor specification*)
fun read_construct ctxt (id, sprems, syn) =
    let val prems = map (Syntax.parse_term ctxt #> TypeInfer.constrain FOLogic.oT) sprems
          |> Syntax.check_terms ctxt
        val args = map (#1 o dest_mem) prems
        val T = (map (#2 o dest_Free) args) ---> iT
                handle TERM _ => error
                    "Bad variable in constructor specification"
        val name = Syntax.const_name syn id
    in ((id,T,syn), name, args, prems) end;

val read_constructs = map o map o read_construct;

(*convert constructor specifications into introduction rules*)
fun mk_intr_tms sg (rec_tm, constructs) =
  let
    fun mk_intr ((id,T,syn), name, args, prems) =
      Logic.list_implies
        (map FOLogic.mk_Trueprop prems,
	 FOLogic.mk_Trueprop
	    (@{const mem} $ list_comb (Const (Sign.full_bname sg name, T), args)
	               $ rec_tm))
  in  map mk_intr constructs  end;

fun mk_all_intr_tms sg arg = List.concat (ListPair.map (mk_intr_tms sg) arg);

fun mk_Un (t1, t2) = @{const Un} $ t1 $ t2;

(*Make a datatype's domain: form the union of its set parameters*)
fun union_params (rec_tm, cs) =
  let val (_,args) = strip_comb rec_tm
      fun is_ind arg = (type_of arg = iT)
  in  case List.filter is_ind (args @ cs) of
         []     => @{const 0}
       | u_args => BalancedTree.make mk_Un u_args
  end;


(*Includes rules for succ and Pair since they are common constructions*)
val elim_rls =
  [@{thm asm_rl}, @{thm FalseE}, @{thm succ_neq_0}, @{thm sym} RS @{thm succ_neq_0},
   @{thm Pair_neq_0}, @{thm sym} RS @{thm Pair_neq_0}, @{thm Pair_inject},
   make_elim @{thm succ_inject}, @{thm refl_thin}, @{thm conjE}, @{thm exE}, @{thm disjE}];


(*From HOL/ex/meson.ML: raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

fun gen_make_elim elim_rls rl =
      standard (tryres (rl, elim_rls @ [revcut_rl]));

(*Turns iff rules into safe elimination rules*)
fun mk_free_SEs iffs = map (gen_make_elim [@{thm conjE}, @{thm FalseE}]) (iffs RL [@{thm iffD1}]);

end;

