(*Attempts to remove occurrences of split, and pair-valued parameters*)
val remove_split = rewrite_rule [split_conv RS eq_reflection] o split_all;

local

(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split (Type ("*", [T1, T2])) T3 u =
      HOLogic.split_const (T1, T2, T3) $
      Abs("v", T1,
          ap_split T2 T3
             ((ap_split T1 (HOLogic.prodT_factors T2 ---> T3) (incr_boundvars 1 u)) $
              Bound 0))
  | ap_split T T3 u = u;

(*Curries any Var of function type in the rule*)
fun split_rule_var' (t as Var (v, Type ("fun", [T1, T2])), rl) =
      let val T' = HOLogic.prodT_factors T1 ---> T2
          val newt = ap_split T1 T2 (Var (v, T'))
          val cterm = Thm.cterm_of (#sign (rep_thm rl))
      in
          instantiate ([], [(cterm t, cterm newt)]) rl
      end
  | split_rule_var' (t, rl) = rl;

(*** Complete splitting of partially splitted rules ***)

fun ap_split' (T::Ts) U u = Abs ("v", T, ap_split' Ts U
      (ap_split T (flat (map HOLogic.prodT_factors Ts) ---> U)
        (incr_boundvars 1 u) $ Bound 0))
  | ap_split' _ _ u = u;

fun complete_split_rule_var ((t as Var (v, T), ts), (rl, vs)) =
      let
        val cterm = Thm.cterm_of (#sign (rep_thm rl))
        val (Us', U') = strip_type T;
        val Us = take (length ts, Us');
        val U = drop (length ts, Us') ---> U';
        val T' = flat (map HOLogic.prodT_factors Us) ---> U;
        fun mk_tuple ((xs, insts), v as Var ((a, _), T)) =
              let
                val Ts = HOLogic.prodT_factors T;
                val ys = variantlist (replicate (length Ts) a, xs);
              in (xs @ ys, (cterm v, cterm (HOLogic.mk_tuple T
                (map (Var o apfst (rpair 0)) (ys ~~ Ts))))::insts)
              end
          | mk_tuple (x, _) = x;
        val newt = ap_split' Us U (Var (v, T'));
        val cterm = Thm.cterm_of (#sign (rep_thm rl));
        val (vs', insts) = foldl mk_tuple ((vs, []), ts);
      in
        (instantiate ([], [(cterm t, cterm newt)] @ insts) rl, vs')
      end
  | complete_split_rule_var (_, x) = x;

fun collect_vars (vs, Abs (_, _, t)) = collect_vars (vs, t)
  | collect_vars (vs, t) = (case strip_comb t of
        (v as Var _, ts) => (v, ts)::vs
      | (t, ts) => foldl collect_vars (vs, ts));

in

val split_rule_var = standard o remove_split o split_rule_var';

(*Curries ALL function variables occurring in a rule's conclusion*)
fun split_rule rl = standard (remove_split (foldr split_rule_var' (term_vars (concl_of rl), rl)));

fun complete_split_rule rl =
  standard (remove_split (fst (foldr complete_split_rule_var
    (collect_vars ([], concl_of rl),
     (rl, map (fst o fst o dest_Var) (term_vars (#prop (rep_thm rl))))))))
	|> RuleCases.save rl;

end;
fun complete_split x = 
	Attrib.no_args (Drule.rule_attribute (K complete_split_rule)) x;

fun split_rule_goal xss rl = let 
	val ss = HOL_basic_ss addsimps [split_conv, fst_conv, snd_conv]; 
	fun one_split i (th,s) = rule_by_tactic (pair_tac s i) th;
	fun one_goal (xs,i) th = foldl (one_split i) (th,xs);
        in standard (Simplifier.full_simplify ss (foldln one_goal xss rl))
	   |> RuleCases.save rl
        end;
fun split_format x = 
	Attrib.syntax (Args.and_list1 (Scan.lift (Scan.repeat Args.name)) 
	>> (fn xss => Drule.rule_attribute (K (split_rule_goal xss)))) x;

val split_attributes = [Attrib.add_attributes 
	[("complete_split", (complete_split, complete_split), 
          "recursively split all pair-typed function arguments"),
	 ("split_format", (split_format, split_format), 
          "split given pair-typed subterms in premises")]];

