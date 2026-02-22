(*  Title:    HOL/Prolog/prolog.ML
    Author:   David von Oheimb (based on a lecture on Lambda Prolog by Nadathur)
*)

structure Prolog =
struct

exception not_HOHH;

fun isD t = case t of
    Const(\<^const_name>\<open>Trueprop\<close>,_)$t     => isD t
  | Const(\<^const_name>\<open>HOL.conj\<close>  ,_)$l$r     => isD l andalso isD r
  | Const(\<^const_name>\<open>HOL.implies\<close>,_)$l$r     => isG l andalso isD r
  | Const(\<^const_name>\<open>Pure.imp\<close>,_)$l$r     => isG l andalso isD r
  | Const(\<^const_name>\<open>All\<close>,_)$Abs(s,_,t) => isD t
  | Const(\<^const_name>\<open>Pure.all\<close>,_)$Abs(s,_,t) => isD t
  | Const(\<^const_name>\<open>HOL.disj\<close>,_)$_$_       => false
  | Const(\<^const_name>\<open>Ex\<close> ,_)$_          => false
  | Const(\<^const_name>\<open>Not\<close>,_)$_          => false
  | Const(\<^const_name>\<open>True\<close>,_)           => false
  | Const(\<^const_name>\<open>False\<close>,_)          => false
  | l $ r                     => isD l
  | Const _ (* rigid atom *)  => true
  | Bound _ (* rigid atom *)  => true
  | Free  _ (* rigid atom *)  => true
  | _    (* flexible atom,
            anything else *)  => false
and
    isG t = case t of
    Const(\<^const_name>\<open>Trueprop\<close>,_)$t     => isG t
  | Const(\<^const_name>\<open>HOL.conj\<close>  ,_)$l$r     => isG l andalso isG r
  | Const(\<^const_name>\<open>HOL.disj\<close>  ,_)$l$r     => isG l andalso isG r
  | Const(\<^const_name>\<open>HOL.implies\<close>,_)$l$r     => isD l andalso isG r
  | Const(\<^const_name>\<open>Pure.imp\<close>,_)$l$r     => isD l andalso isG r
  | Const(\<^const_name>\<open>All\<close>,_)$Abs(_,_,t) => isG t
  | Const(\<^const_name>\<open>Pure.all\<close>,_)$Abs(_,_,t) => isG t
  | Const(\<^const_name>\<open>Ex\<close> ,_)$Abs(_,_,t) => isG t
  | Const(\<^const_name>\<open>True\<close>,_)           => true
  | Const(\<^const_name>\<open>Not\<close>,_)$_          => false
  | Const(\<^const_name>\<open>False\<close>,_)          => false
  | _ (* atom *)              => true;

val check_HOHH_tac1 = PRIMITIVE (fn thm =>
        if isG (Thm.concl_of thm) then thm else raise not_HOHH);
val check_HOHH_tac2 = PRIMITIVE (fn thm =>
        if forall isG (Thm.prems_of thm) then thm else raise not_HOHH);
fun check_HOHH thm  = (if isD (Thm.concl_of thm) andalso forall isG (Thm.prems_of thm)
                        then thm else raise not_HOHH);

fun atomizeD ctxt thm =
  let
    fun at  thm = case Thm.concl_of thm of
      _$(Const(\<^const_name>\<open>All\<close> ,_)$Abs(s,_,_))=>
        let val s' = if s="P" then "PP" else s in
          at(thm RS (Rule_Insts.read_instantiate ctxt [((("x", 0), Position.none), s')] [s'] spec))
        end
    | _$(Const(\<^const_name>\<open>HOL.conj\<close>,_)$_$_)       => at(thm RS conjunct1)@at(thm RS conjunct2)
    | _$(Const(\<^const_name>\<open>HOL.implies\<close>,_)$_$_)     => at(thm RS mp)
    | _                             => [thm]
  in map zero_var_indexes (at thm) end;

val atomize_ss =
  (Simplifier.empty_simpset \<^context> |> Simplifier.set_mksimps (mksimps mksimps_pairs))
  addsimps [
        @{thm all_conj_distrib}, (* "(! x. P x & Q x) = ((! x. P x) & (! x. Q x))" *)
        @{thm imp_conjL} RS sym, (* "(D :- G1 :- G2) = (D :- G1 & G2)" *)
        @{thm imp_conjR},        (* "(D1 & D2 :- G) = ((D1 :- G) & (D2 :- G))" *)
        @{thm imp_all}]          (* "((!x. D) :- G) = (!x. D :- G)" *)
  |> simpset_of;


(*val hyp_resolve_tac = Subgoal.FOCUS_PREMS (fn {prems, ...} =>
                                  resolve_tac (maps atomizeD prems) 1);
  -- is nice, but cannot instantiate unknowns in the assumptions *)
fun hyp_resolve_tac ctxt = SUBGOAL (fn (subgoal, i) =>
  let
        fun ap (Const(\<^const_name>\<open>All\<close>,_)$Abs(_,_,t))=(case ap t of (k,a,t) => (k+1,a  ,t))
        |   ap (Const(\<^const_name>\<open>HOL.implies\<close>,_)$_$t)    =(case ap t of (k,_,t) => (k,true ,t))
        |   ap t                          =                         (0,false,t);
(*
        fun rep_goal (Const (@{const_name Pure.all},_)$Abs (_,_,t)) = rep_goal t
        |   rep_goal (Const (@{const_name Pure.imp},_)$s$t)         =
                        (case rep_goal t of (l,t) => (s::l,t))
        |   rep_goal t                             = ([]  ,t);
        val (prems, Const(@{const_name Trueprop}, _)$concl) = rep_goal
                                                (#3(dest_state (st,i)));
*)
        val prems = Logic.strip_assums_hyp subgoal;
        val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl subgoal);
        fun drot_tac k i = DETERM (rotate_tac k i);
        fun spec_tac 0 i = all_tac
        |   spec_tac k i = EVERY' [dresolve_tac ctxt [spec], drot_tac ~1, spec_tac (k-1)] i;
        fun dup_spec_tac k i = if k = 0 then all_tac else EVERY'
                      [DETERM o (eresolve_tac ctxt [all_dupE]), drot_tac ~2, spec_tac (k-1)] i;
        fun same_head _ (Const (x,_)) (Const (y,_)) = x = y
        |   same_head k (s$_)         (t$_)         = same_head k s t
        |   same_head k (Bound i)     (Bound j)     = i = j + k
        |   same_head _ _             _             = true;
        fun mapn f n []      = []
        |   mapn f n (x::xs) = f n x::mapn f (n+1) xs;
        fun pres_tac (k,arrow,t) n i = drot_tac n i THEN (
          if same_head k t concl
          then dup_spec_tac k i THEN
               (if arrow then eresolve_tac ctxt [mp] i THEN drot_tac (~n) i else assume_tac ctxt i)
          else no_tac);
        val ptacs = mapn (fn n => fn t =>
                          pres_tac (ap (HOLogic.dest_Trueprop t)) n i) 0 prems;
  in Library.foldl (op APPEND) (no_tac, ptacs) end);

fun ptac ctxt prog = let
  val proga = maps (atomizeD ctxt) prog         (* atomize the prog *)
  in    (REPEAT_DETERM1 o FIRST' [
                resolve_tac ctxt [TrueI],                     (* "True" *)
                resolve_tac ctxt [conjI],                     (* "[| P; Q |] ==> P & Q" *)
                resolve_tac ctxt [allI],                      (* "(!!x. P x) ==> ! x. P x" *)
                resolve_tac ctxt [exI],                       (* "P x ==> ? x. P x" *)
                resolve_tac ctxt [impI] THEN'                 (* "(P ==> Q) ==> P --> Q" *)
                  asm_full_simp_tac (put_simpset atomize_ss ctxt) THEN'    (* atomize the asms *)
                  (REPEAT_DETERM o (eresolve_tac ctxt [conjE]))        (* split the asms *)
                ])
        ORELSE' resolve_tac ctxt [disjI1,disjI2]     (* "P ==> P | Q","Q ==> P | Q"*)
        ORELSE' ((resolve_tac ctxt proga APPEND' hyp_resolve_tac ctxt)
                 THEN' (fn _ => check_HOHH_tac2))
end;

fun prolog_tac ctxt prog =
  check_HOHH_tac1 THEN
  DEPTH_SOLVE (ptac ctxt (map check_HOHH prog) 1);

val prog_HOHH = [];

end;
