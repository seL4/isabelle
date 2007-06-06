structure LinZTac =
struct

val trace = ref false;
fun trace_msg s = if !trace then tracing s else ();

val cooper_ss = @{simpset};

val nT = HOLogic.natT;
val binarith = map thm
  ["Pls_0_eq", "Min_1_eq"];
 val intarithrel = 
     (map thm ["int_eq_number_of_eq","int_neg_number_of_BIT", 
		"int_le_number_of_eq","int_iszero_number_of_0",
		"int_less_number_of_eq_neg"]) @
     (map (fn s => thm s RS thm "lift_bool") 
	  ["int_iszero_number_of_Pls","int_iszero_number_of_1",
	   "int_neg_number_of_Min"])@
     (map (fn s => thm s RS thm "nlift_bool") 
	  ["int_nonzero_number_of_Min","int_not_neg_number_of_Pls"]);
     
val intarith = map thm ["int_number_of_add_sym", "int_number_of_minus_sym",
			"int_number_of_diff_sym", "int_number_of_mult_sym"];
val natarith = map thm ["add_nat_number_of", "diff_nat_number_of",
			"mult_nat_number_of", "eq_nat_number_of",
			"less_nat_number_of"]
val powerarith = 
    (map thm ["nat_number_of", "zpower_number_of_even", 
	      "zpower_Pls", "zpower_Min"]) @ 
    [simplify (HOL_basic_ss addsimps [thm "zero_eq_Numeral0_nring", 
			   thm "one_eq_Numeral1_nring"])
  (thm "zpower_number_of_odd")]

val comp_arith = binarith @ intarith @ intarithrel @ natarith 
	    @ powerarith @[thm"not_false_eq_true", thm "not_true_eq_false"];


val zdvd_int = thm "zdvd_int";
val zdiff_int_split = thm "zdiff_int_split";
val all_nat = thm "all_nat";
val ex_nat = thm "ex_nat";
val number_of1 = thm "number_of1";
val number_of2 = thm "number_of2";
val split_zdiv = thm "split_zdiv";
val split_zmod = thm "split_zmod";
val mod_div_equality' = thm "mod_div_equality'";
val split_div' = thm "split_div'";
val Suc_plus1 = thm "Suc_plus1";
val imp_le_cong = thm "imp_le_cong";
val conj_le_cong = thm "conj_le_cong";
val nat_mod_add_eq = mod_add1_eq RS sym;
val nat_mod_add_left_eq = mod_add_left_eq RS sym;
val nat_mod_add_right_eq = mod_add_right_eq RS sym;
val int_mod_add_eq = @{thm "zmod_zadd1_eq"} RS sym;
val int_mod_add_left_eq = @{thm "zmod_zadd_left_eq"} RS sym;
val int_mod_add_right_eq = @{thm "zmod_zadd_right_eq"} RS sym;
val nat_div_add_eq = @{thm "div_add1_eq"} RS sym;
val int_div_add_eq = @{thm "zdiv_zadd1_eq"} RS sym;
val ZDIVISION_BY_ZERO_MOD = @{thm "DIVISION_BY_ZERO"} RS conjunct2;
val ZDIVISION_BY_ZERO_DIV = @{thm "DIVISION_BY_ZERO"} RS conjunct1;

(*
val fn_rews = List.concat (map thms ["allpairs.simps","iupt.simps","decr.simps", "decrnum.simps","disjuncts.simps","simpnum.simps", "simpfm.simps","numadd.simps","nummul.simps","numneg_def","numsub","simp_num_pair_def","not.simps","prep.simps","qelim.simps","minusinf.simps","plusinf.simps","rsplit0.simps","rlfm.simps","\\<Upsilon>.simps","\\<upsilon>.simps","linrqe_def", "ferrack_def", "Let_def", "numsub_def", "numneg_def","DJ_def", "imp_def", "evaldjf_def", "djf_def", "split_def", "eq_def", "disj_def", "simp_num_pair_def", "conj_def", "lt_def", "neq_def","gt_def"]);
*)
fun prepare_for_linz q fm = 
  let
    val ps = Logic.strip_params fm
    val hs = map HOLogic.dest_Trueprop (Logic.strip_assums_hyp fm)
    val c = HOLogic.dest_Trueprop (Logic.strip_assums_concl fm)
    fun mk_all ((s, T), (P,n)) =
      if 0 mem loose_bnos P then
        (HOLogic.all_const T $ Abs (s, T, P), n)
      else (incr_boundvars ~1 P, n-1)
    fun mk_all2 (v, t) = HOLogic.all_const (fastype_of v) $ lambda v t;
      val rhs = hs
(*    val (rhs,irhs) = List.partition (relevant (rev ps)) hs *)
    val np = length ps
    val (fm',np) =  foldr (fn ((x, T), (fm,n)) => mk_all ((x, T), (fm,n)))
      (foldr HOLogic.mk_imp c rhs, np) ps
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = nT)
      (term_frees fm' @ term_vars fm');
    val fm2 = foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun linz_tac ctxt q i = ObjectLogic.atomize_tac i THEN (fn st =>
  let
    val g = List.nth (prems_of st, i - 1)
    val thy = ProofContext.theory_of ctxt
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linz q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset = HOL_basic_ss 
			addsimps [refl,nat_mod_add_eq, nat_mod_add_left_eq, 
				  nat_mod_add_right_eq, int_mod_add_eq, 
				  int_mod_add_right_eq, int_mod_add_left_eq,
				  nat_div_add_eq, int_div_add_eq,
				  mod_self, @{thm "zmod_self"},
				  DIVISION_BY_ZERO_MOD,DIVISION_BY_ZERO_DIV,
				  ZDIVISION_BY_ZERO_MOD,ZDIVISION_BY_ZERO_DIV,
				  @{thm "zdiv_zero"}, @{thm "zmod_zero"}, @{thm "div_0"}, @{thm "mod_0"},
				  @{thm "zdiv_1"}, @{thm "zmod_1"}, @{thm "div_1"}, @{thm "mod_1"},
				  Suc_plus1]
			addsimps add_ac
			addsimprocs [cancel_div_mod_proc]
    val simpset0 = HOL_basic_ss
      addsimps [mod_div_equality', Suc_plus1]
      addsimps comp_arith
      addsplits [split_zdiv, split_zmod, split_div', @{thm "split_min"}, @{thm "split_max"}]
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 = HOL_basic_ss
      addsimps [nat_number_of_def, zdvd_int] @ map (fn r => r RS sym)
        [int_int_eq, zle_int, zless_int, zadd_int, zmult_int]
      addsplits [zdiff_int_split]
    (*simp rules for elimination of int n*)

    val simpset2 = HOL_basic_ss
      addsimps [nat_0_le, all_nat, ex_nat, number_of1, number_of2, int_0, int_1]
      addcongs [conj_le_cong, imp_le_cong]
    (* simp rules for elimination of abs *)
    val simpset3 = HOL_basic_ss addsplits [abs_split]
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1),
       TRY (simp_tac simpset3 1), TRY (simp_tac cooper_ss 1)]
      (trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const ("Trueprop", _) $ t1) $ _ =>
    let val pth = linzqe_oracle thy (Pattern.eta_long [] t1)
    in 
          ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i))
    end
      | _ => (pre_thm, assm_tac i)
  in (rtac (((mp_step nh) o (spec_step np)) th) i 
      THEN tac) st
  end handle Subscript => no_tac st);

fun linz_args meth =
 let val parse_flag = 
         Args.$$$ "no_quantify" >> (K (K false));
 in
   Method.simple_args 
  (Scan.optional (Args.$$$ "(" |-- Scan.repeat1 parse_flag --| Args.$$$ ")") [] >>
    curry (Library.foldl op |>) true)
    (fn q => fn ctxt => meth ctxt q 1)
  end;

fun linz_method ctxt q i = Method.METHOD (fn facts =>
  Method.insert_tac facts 1 THEN linz_tac ctxt q i);

val setup =
  Method.add_method ("cooper",
     linz_args linz_method,
     "decision procedure for linear integer arithmetic");

end