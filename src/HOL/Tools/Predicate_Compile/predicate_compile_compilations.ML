(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_compilations.ML
    Author:     Lukas Bulwahn, TU Muenchen

Structures for different compilations of the predicate compiler.
*)

structure Predicate_Comp_Funs =  (* FIXME proper signature *)
struct

fun mk_monadT T = Type (\<^type_name>\<open>Predicate.pred\<close>, [T])

fun dest_monadT (Type (\<^type_name>\<open>Predicate.pred\<close>, [T])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Orderings.bot\<close>, mk_monadT T)

fun mk_single t =
  let val T = fastype_of t
  in Const(\<^const_name>\<open>Predicate.single\<close>, T --> mk_monadT T) $ t end

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Predicate.bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>sup\<close>

fun mk_if cond = Const (\<^const_name>\<open>Predicate.if_pred\<close>,
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (\<^const_name>\<open>Predicate.iterate_upto\<close>,
      [\<^typ>\<open>natural\<close> --> T, \<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>] ---> mk_monadT T),
    [f, from, to])

fun mk_not t =
  let
    val T = mk_monadT HOLogic.unitT
  in Const (\<^const_name>\<open>Predicate.not_pred\<close>, T --> T) $ t end

fun mk_Enum f =
  let val T as Type ("fun", [T', _]) = fastype_of f
  in
    Const (\<^const_name>\<open>Predicate.Pred\<close>, T --> mk_monadT T') $ f    
  end;

fun mk_Eval (f, x) =
  let
    val T = dest_monadT (fastype_of f)
  in
    Const (\<^const_name>\<open>Predicate.eval\<close>, mk_monadT T --> T --> HOLogic.boolT) $ f $ x
  end

fun dest_Eval (Const (\<^const_name>\<open>Predicate.eval\<close>, _) $ f $ x) = (f, x)

fun mk_map T1 T2 tf tp = Const (\<^const_name>\<open>Predicate.map\<close>,
  (T1 --> T2) --> mk_monadT T1 --> mk_monadT T2) $ tf $ tp

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end


structure CPS_Comp_Funs =  (* FIXME proper signature *)
struct

fun mk_monadT T =
  (T --> \<^typ>\<open>Code_Evaluation.term list option\<close>) --> \<^typ>\<open>Code_Evaluation.term list option\<close>

fun dest_monadT
      (Type ("fun", [Type ("fun", [T, \<^typ>\<open>term list option\<close>]), \<^typ>\<open>term list option\<close>])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], []);

fun mk_empty T = Const (\<^const_name>\<open>Quickcheck_Exhaustive.cps_empty\<close>, mk_monadT T)

fun mk_single t =
  let val T = fastype_of t
  in Const(\<^const_name>\<open>Quickcheck_Exhaustive.cps_single\<close>, T --> mk_monadT T) $ t end

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Quickcheck_Exhaustive.cps_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Quickcheck_Exhaustive.cps_plus\<close>

fun mk_if cond = Const (\<^const_name>\<open>Quickcheck_Exhaustive.cps_if\<close>,
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond

fun mk_iterate_upto _ _ = error "not implemented yet"

fun mk_not t =
  let
    val T = mk_monadT HOLogic.unitT
  in Const (\<^const_name>\<open>Quickcheck_Exhaustive.cps_not\<close>, T --> T) $ t end

fun mk_Enum _ = error "not implemented"

fun mk_Eval _ = error "not implemented"

fun dest_Eval _ = error "not implemented"

fun mk_map _ _ _ _ = error "not implemented"

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end


structure Pos_Bounded_CPS_Comp_Funs =  (* FIXME proper signature *)
struct

val resultT = \<^typ>\<open>(bool * Code_Evaluation.term list) option\<close>
fun mk_monadT T = (T --> resultT) --> \<^typ>\<open>natural\<close> --> resultT

fun dest_monadT (Type ("fun", [Type ("fun", [T, \<^typ>\<open>(bool * term list) option\<close>]),
  \<^typ>\<open>natural => (bool * term list) option\<close>])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Quickcheck_Exhaustive.pos_bound_cps_empty\<close>, mk_monadT T)

fun mk_single t =
  let val T = fastype_of t
  in Const(\<^const_name>\<open>Quickcheck_Exhaustive.pos_bound_cps_single\<close>, T --> mk_monadT T) $ t end

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Quickcheck_Exhaustive.pos_bound_cps_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Quickcheck_Exhaustive.pos_bound_cps_plus\<close>

fun mk_if cond =
  Const (\<^const_name>\<open>Quickcheck_Exhaustive.pos_bound_cps_if\<close>,
    HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond

fun mk_iterate_upto _ _ = error "not implemented yet"

fun mk_not t =
  let
    val nT = \<^typ>\<open>(unit Quickcheck_Exhaustive.unknown =>
      Code_Evaluation.term list Quickcheck_Exhaustive.three_valued) => natural =>
      Code_Evaluation.term list Quickcheck_Exhaustive.three_valued\<close>
    val T = mk_monadT HOLogic.unitT
  in Const (\<^const_name>\<open>Quickcheck_Exhaustive.pos_bound_cps_not\<close>, nT --> T) $ t end

fun mk_Enum _ = error "not implemented"

fun mk_Eval _ = error "not implemented"

fun dest_Eval _ = error "not implemented"

fun mk_map _ _ _ _ = error "not implemented"

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end


structure Neg_Bounded_CPS_Comp_Funs =  (* FIXME proper signature *)
struct

fun mk_monadT T =
  (Type (\<^type_name>\<open>Quickcheck_Exhaustive.unknown\<close>, [T])
    --> \<^typ>\<open>Code_Evaluation.term list Quickcheck_Exhaustive.three_valued\<close>)
    --> \<^typ>\<open>natural => Code_Evaluation.term list Quickcheck_Exhaustive.three_valued\<close>

fun dest_monadT
    (Type ("fun", [Type ("fun", [Type (\<^type_name>\<open>Quickcheck_Exhaustive.unknown\<close>, [T]),
      \<^typ>\<open>term list Quickcheck_Exhaustive.three_valued\<close>]),
      \<^typ>\<open>natural => term list Quickcheck_Exhaustive.three_valued\<close>])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], []);

fun mk_empty T = Const (\<^const_name>\<open>Quickcheck_Exhaustive.neg_bound_cps_empty\<close>, mk_monadT T)

fun mk_single t =
  let val T = fastype_of t
  in Const(\<^const_name>\<open>Quickcheck_Exhaustive.neg_bound_cps_single\<close>, T --> mk_monadT T) $ t end

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Quickcheck_Exhaustive.neg_bound_cps_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Quickcheck_Exhaustive.neg_bound_cps_plus\<close>

fun mk_if cond = Const (\<^const_name>\<open>Quickcheck_Exhaustive.neg_bound_cps_if\<close>,
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond

fun mk_iterate_upto _ _ = error "not implemented"

fun mk_not t =
  let
    val T = mk_monadT HOLogic.unitT
    val pT = \<^typ>\<open>(unit => (bool * Code_Evaluation.term list) option)\<close>
      --> \<^typ>\<open>natural => (bool * Code_Evaluation.term list) option\<close>
  in Const (\<^const_name>\<open>Quickcheck_Exhaustive.neg_bound_cps_not\<close>, pT --> T) $ t end

fun mk_Enum _ = error "not implemented"

fun mk_Eval _ = error "not implemented"

fun dest_Eval _ = error "not implemented"

fun mk_map _ _ _ _  = error "not implemented"

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;


structure RandomPredCompFuns =  (* FIXME proper signature *)
struct

fun mk_randompredT T =
  \<^typ>\<open>Random.seed\<close> --> HOLogic.mk_prodT (Predicate_Comp_Funs.mk_monadT T, \<^typ>\<open>Random.seed\<close>)

fun dest_randompredT (Type ("fun", [\<^typ>\<open>Random.seed\<close>, Type (\<^type_name>\<open>Product_Type.prod\<close>,
  [Type (\<^type_name>\<open>Predicate.pred\<close>, [T]), \<^typ>\<open>Random.seed\<close>])])) = T
  | dest_randompredT T = raise TYPE ("dest_randompredT", [T], [])

fun mk_empty T = Const(\<^const_name>\<open>Random_Pred.empty\<close>, mk_randompredT T)

fun mk_single t =
  let               
    val T = fastype_of t
  in
    Const (\<^const_name>\<open>Random_Pred.single\<close>, T --> mk_randompredT T) $ t
  end

fun mk_bind (x, f) =
  let
    val T as (Type ("fun", [_, U])) = fastype_of f
  in
    Const (\<^const_name>\<open>Random_Pred.bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Random_Pred.union\<close>

fun mk_if cond = Const (\<^const_name>\<open>Random_Pred.if_randompred\<close>,
  HOLogic.boolT --> mk_randompredT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (\<^const_name>\<open>Random_Pred.iterate_upto\<close>,
      [\<^typ>\<open>natural\<close> --> T, \<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>] ---> mk_randompredT T),
    [f, from, to])

fun mk_not t =
  let
    val T = mk_randompredT HOLogic.unitT
  in Const (\<^const_name>\<open>Random_Pred.not_randompred\<close>, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (\<^const_name>\<open>Random_Pred.map\<close>,
  (T1 --> T2) --> mk_randompredT T1 --> mk_randompredT T2) $ tf $ tp

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_randompredT, dest_monadT = dest_randompredT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end


structure DSequence_CompFuns =  (* FIXME proper signature *)
struct

fun mk_dseqT T = Type ("fun", [\<^typ>\<open>natural\<close>, Type ("fun", [\<^typ>\<open>bool\<close>,
  Type (\<^type_name>\<open>Option.option\<close>, [Type  (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [T])])])])

fun dest_dseqT (Type ("fun", [\<^typ>\<open>natural\<close>, Type ("fun", [\<^typ>\<open>bool\<close>,
  Type (\<^type_name>\<open>Option.option\<close>, [Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [T])])])])) = T
  | dest_dseqT T = raise TYPE ("dest_dseqT", [T], []);

fun mk_empty T = Const (\<^const_name>\<open>Limited_Sequence.empty\<close>, mk_dseqT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(\<^const_name>\<open>Limited_Sequence.single\<close>, T --> mk_dseqT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Limited_Sequence.bind\<close>, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Limited_Sequence.union\<close>;

fun mk_if cond = Const (\<^const_name>\<open>Limited_Sequence.if_seq\<close>,
  HOLogic.boolT --> mk_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto _ _ = raise Fail "No iterate_upto compilation"

fun mk_not t = let val T = mk_dseqT HOLogic.unitT
  in Const (\<^const_name>\<open>Limited_Sequence.not_seq\<close>, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (\<^const_name>\<open>Limited_Sequence.map\<close>,
  (T1 --> T2) --> mk_dseqT T1 --> mk_dseqT T2) $ tf $ tp

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_dseqT, dest_monadT = dest_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;


structure New_Pos_DSequence_CompFuns =  (* FIXME proper signature *)
struct

fun mk_pos_dseqT T =
  \<^typ>\<open>natural\<close> --> Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [T])

fun dest_pos_dseqT
      (Type ("fun", [\<^typ>\<open>natural\<close>, Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [T])])) = T
  | dest_pos_dseqT T = raise TYPE ("dest_pos_dseqT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Limited_Sequence.pos_empty\<close>, mk_pos_dseqT T)

fun mk_single t =
  let
    val T = fastype_of t
  in Const(\<^const_name>\<open>Limited_Sequence.pos_single\<close>, T --> mk_pos_dseqT T) $ t end

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Limited_Sequence.pos_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end
  
fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Limited_Sequence.pos_decr_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Limited_Sequence.pos_union\<close>

fun mk_if cond =
  Const (\<^const_name>\<open>Limited_Sequence.pos_if_seq\<close>,
    HOLogic.boolT --> mk_pos_dseqT HOLogic.unitT) $ cond

fun mk_iterate_upto _ _ = raise Fail "No iterate_upto compilation"

fun mk_not t =
  let
    val pT = mk_pos_dseqT HOLogic.unitT
    val nT =
      \<^typ>\<open>natural\<close> --> Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>,
        [Type (\<^type_name>\<open>Option.option\<close>, [\<^typ>\<open>unit\<close>])])
  in Const (\<^const_name>\<open>Limited_Sequence.pos_not_seq\<close>, nT --> pT) $ t end

fun mk_map T1 T2 tf tp =
  Const (\<^const_name>\<open>Limited_Sequence.pos_map\<close>,
    (T1 --> T2) --> mk_pos_dseqT T1 --> mk_pos_dseqT T2) $ tf $ tp

val depth_limited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_dseqT, dest_monadT = dest_pos_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_dseqT, dest_monadT = dest_pos_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end


structure New_Neg_DSequence_CompFuns =  (* FIXME proper signature *)
struct

fun mk_neg_dseqT T = \<^typ>\<open>natural\<close> -->
  Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [Type (\<^type_name>\<open>Option.option\<close>, [T])])

fun dest_neg_dseqT
    (Type ("fun", [\<^typ>\<open>natural\<close>,
      Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [Type (\<^type_name>\<open>Option.option\<close>, [T])])])) =
      T
  | dest_neg_dseqT T = raise TYPE ("dest_neg_dseqT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Limited_Sequence.neg_empty\<close>, mk_neg_dseqT T)

fun mk_single t =
  let
    val T = fastype_of t
  in Const(\<^const_name>\<open>Limited_Sequence.neg_single\<close>, T --> mk_neg_dseqT T) $ t end

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Limited_Sequence.neg_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end
  
fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Limited_Sequence.neg_decr_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Limited_Sequence.neg_union\<close>

fun mk_if cond =
  Const (\<^const_name>\<open>Limited_Sequence.neg_if_seq\<close>,
    HOLogic.boolT --> mk_neg_dseqT HOLogic.unitT) $ cond

fun mk_iterate_upto _ _ = raise Fail "No iterate_upto compilation"

fun mk_not t =
  let
    val nT = mk_neg_dseqT HOLogic.unitT
    val pT =
      \<^typ>\<open>natural\<close> --> Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>,
        [\<^typ>\<open>unit\<close>])
  in Const (\<^const_name>\<open>Limited_Sequence.neg_not_seq\<close>, pT --> nT) $ t end

fun mk_map T1 T2 tf tp =
  Const (\<^const_name>\<open>Limited_Sequence.neg_map\<close>,
    (T1 --> T2) --> mk_neg_dseqT T1 --> mk_neg_dseqT T2) $ tf $ tp

val depth_limited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_dseqT, dest_monadT = dest_neg_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_dseqT, dest_monadT = dest_neg_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end


structure New_Pos_Random_Sequence_CompFuns =  (* FIXME proper signature *)
struct

fun mk_pos_random_dseqT T =
  \<^typ>\<open>natural\<close> --> \<^typ>\<open>natural\<close> --> \<^typ>\<open>Random.seed\<close> -->
    \<^typ>\<open>natural\<close> --> Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [T])

fun dest_pos_random_dseqT
    (Type ("fun", [\<^typ>\<open>natural\<close>, Type ("fun", [\<^typ>\<open>natural\<close>,
      Type ("fun", [\<^typ>\<open>Random.seed\<close>, Type ("fun", [\<^typ>\<open>natural\<close>,
      Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [T])])])])])) = T
  | dest_pos_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Random_Sequence.pos_empty\<close>, mk_pos_random_dseqT T)

fun mk_single t =
  let
    val T = fastype_of t
  in Const(\<^const_name>\<open>Random_Sequence.pos_single\<close>, T --> mk_pos_random_dseqT T) $ t end

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Random_Sequence.pos_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Random_Sequence.pos_decr_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Random_Sequence.pos_union\<close>;

fun mk_if cond = Const (\<^const_name>\<open>Random_Sequence.pos_if_random_dseq\<close>,
  HOLogic.boolT --> mk_pos_random_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (\<^const_name>\<open>Random_Sequence.pos_iterate_upto\<close>,
      [\<^typ>\<open>natural\<close> --> T, \<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>]
        ---> mk_pos_random_dseqT T),
    [f, from, to])

fun mk_not t =
  let
    val pT = mk_pos_random_dseqT HOLogic.unitT
    val nT = \<^typ>\<open>natural\<close> --> \<^typ>\<open>natural\<close> --> \<^typ>\<open>Random.seed\<close> -->
      \<^typ>\<open>natural\<close> --> Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>,
        [Type (\<^type_name>\<open>Option.option\<close>, [\<^typ>\<open>unit\<close>])])

  in Const (\<^const_name>\<open>Random_Sequence.pos_not_random_dseq\<close>, nT --> pT) $ t end

fun mk_map T1 T2 tf tp =
  Const (\<^const_name>\<open>Random_Sequence.pos_map\<close>,
    (T1 --> T2) --> mk_pos_random_dseqT T1 --> mk_pos_random_dseqT T2) $ tf $ tp

val depth_limited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_random_dseqT, dest_monadT = dest_pos_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_random_dseqT, dest_monadT = dest_pos_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;


structure New_Neg_Random_Sequence_CompFuns =  (* FIXME proper signature *)
struct

fun mk_neg_random_dseqT T =
  \<^typ>\<open>natural\<close> --> \<^typ>\<open>natural\<close> --> \<^typ>\<open>Random.seed\<close> -->
    \<^typ>\<open>natural\<close> --> 
    Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [Type (\<^type_name>\<open>Option.option\<close>, [T])])

fun dest_neg_random_dseqT
    (Type ("fun", [\<^typ>\<open>natural\<close>, Type ("fun", [\<^typ>\<open>natural\<close>,
      Type ("fun", [\<^typ>\<open>Random.seed\<close>, Type ("fun", [\<^typ>\<open>natural\<close>,
        Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>,
          [Type (\<^type_name>\<open>Option.option\<close>, [T])])])])])])) = T
  | dest_neg_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Random_Sequence.neg_empty\<close>, mk_neg_random_dseqT T)

fun mk_single t =
  let
    val T = fastype_of t
  in Const(\<^const_name>\<open>Random_Sequence.neg_single\<close>, T --> mk_neg_random_dseqT T) $ t end

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Random_Sequence.neg_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Random_Sequence.neg_decr_bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Random_Sequence.neg_union\<close>

fun mk_if cond =
  Const (\<^const_name>\<open>Random_Sequence.neg_if_random_dseq\<close>,
    HOLogic.boolT --> mk_neg_random_dseqT HOLogic.unitT) $ cond

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (\<^const_name>\<open>Random_Sequence.neg_iterate_upto\<close>,
      [\<^typ>\<open>natural\<close> --> T, \<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>]
        ---> mk_neg_random_dseqT T),
    [f, from, to])

fun mk_not t =
  let
    val nT = mk_neg_random_dseqT HOLogic.unitT
    val pT = \<^typ>\<open>natural\<close> --> \<^typ>\<open>natural\<close> --> \<^typ>\<open>Random.seed\<close> -->
    \<^typ>\<open>natural\<close> --> Type (\<^type_name>\<open>Lazy_Sequence.lazy_sequence\<close>, [\<^typ>\<open>unit\<close>])
  in Const (\<^const_name>\<open>Random_Sequence.neg_not_random_dseq\<close>, pT --> nT) $ t end

fun mk_map T1 T2 tf tp =
  Const (\<^const_name>\<open>Random_Sequence.neg_map\<close>,
    (T1 --> T2) --> mk_neg_random_dseqT T1 --> mk_neg_random_dseqT T2) $ tf $ tp

val depth_limited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_random_dseqT, dest_monadT = dest_neg_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_random_dseqT, dest_monadT = dest_neg_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end


structure Random_Sequence_CompFuns =  (* FIXME proper signature *)
struct

fun mk_random_dseqT T =
  \<^typ>\<open>natural\<close> --> \<^typ>\<open>natural\<close> --> \<^typ>\<open>Random.seed\<close> -->
    HOLogic.mk_prodT (DSequence_CompFuns.mk_dseqT T, \<^typ>\<open>Random.seed\<close>)

fun dest_random_dseqT
    (Type ("fun", [\<^typ>\<open>natural\<close>, Type ("fun", [\<^typ>\<open>natural\<close>,
      Type ("fun", [\<^typ>\<open>Random.seed\<close>,
      Type (\<^type_name>\<open>Product_Type.prod\<close>, [T, \<^typ>\<open>Random.seed\<close>])])])])) =
      DSequence_CompFuns.dest_dseqT T
  | dest_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], [])

fun mk_empty T = Const (\<^const_name>\<open>Random_Sequence.empty\<close>, mk_random_dseqT T)

fun mk_single t =
  let
    val T = fastype_of t
  in Const(\<^const_name>\<open>Random_Sequence.single\<close>, T --> mk_random_dseqT T) $ t end

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (\<^const_name>\<open>Random_Sequence.bind\<close>, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop \<^const_name>\<open>Random_Sequence.union\<close>

fun mk_if cond =
  Const (\<^const_name>\<open>Random_Sequence.if_random_dseq\<close>,
    HOLogic.boolT --> mk_random_dseqT HOLogic.unitT) $ cond

fun mk_iterate_upto _ _ = raise Fail "No iterate_upto compilation"

fun mk_not t =
  let
    val T = mk_random_dseqT HOLogic.unitT
  in Const (\<^const_name>\<open>Random_Sequence.not_random_dseq\<close>, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (\<^const_name>\<open>Random_Sequence.map\<close>,
  (T1 --> T2) --> mk_random_dseqT T1 --> mk_random_dseqT T2) $ tf $ tp

val compfuns =
  Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_random_dseqT, dest_monadT = dest_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end

