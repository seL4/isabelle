(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_compilations.ML
    Author:     Lukas Bulwahn, TU Muenchen

Structures for different compilations of the predicate compiler.
*)

structure Predicate_Comp_Funs =
struct

fun mk_monadT T = Type (@{type_name Predicate.pred}, [T])

fun dest_monadT (Type (@{type_name Predicate.pred}, [T])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], []);

fun mk_empty T = Const (@{const_name Orderings.bot}, mk_monadT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Predicate.single}, T --> mk_monadT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Predicate.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name sup};

fun mk_if cond = Const (@{const_name Predicate.if_pred},
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (@{const_name Predicate.iterate_upto},
      [@{typ code_numeral} --> T, @{typ code_numeral}, @{typ code_numeral}] ---> mk_monadT T),
    [f, from, to])

fun mk_not t =
  let
    val T = mk_monadT HOLogic.unitT
  in Const (@{const_name Predicate.not_pred}, T --> T) $ t end

fun mk_Enum f =
  let val T as Type ("fun", [T', _]) = fastype_of f
  in
    Const (@{const_name Predicate.Pred}, T --> mk_monadT T') $ f    
  end;

fun mk_Eval (f, x) =
  let
    val T = dest_monadT (fastype_of f)
  in
    Const (@{const_name Predicate.eval}, mk_monadT T --> T --> HOLogic.boolT) $ f $ x
  end;

fun dest_Eval (Const (@{const_name Predicate.eval}, _) $ f $ x) = (f, x)

fun mk_map T1 T2 tf tp = Const (@{const_name Predicate.map},
  (T1 --> T2) --> mk_monadT T1 --> mk_monadT T2) $ tf $ tp;

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;

structure CPS_Comp_Funs =
struct

fun mk_monadT T = (T --> @{typ "Code_Evaluation.term list option"}) --> @{typ "Code_Evaluation.term list option"}

fun dest_monadT (Type ("fun", [Type ("fun", [T, @{typ "term list option"}]), @{typ "term list option"}])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], []);

fun mk_empty T = Const (@{const_name Quickcheck_Exhaustive.cps_empty}, mk_monadT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Quickcheck_Exhaustive.cps_single}, T --> mk_monadT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Quickcheck_Exhaustive.cps_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name Quickcheck_Exhaustive.cps_plus};

fun mk_if cond = Const (@{const_name Quickcheck_Exhaustive.cps_if},
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = error "not implemented yet"

fun mk_not t =
  let
    val T = mk_monadT HOLogic.unitT
  in Const (@{const_name Quickcheck_Exhaustive.cps_not}, T --> T) $ t end

fun mk_Enum f = error "not implemented"

fun mk_Eval (f, x) = error "not implemented"

fun dest_Eval t = error "not implemented"

fun mk_map T1 T2 tf tp = error "not implemented"

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;

structure Pos_Bounded_CPS_Comp_Funs =
struct

val resultT = @{typ "(bool * Code_Evaluation.term list) option"}
fun mk_monadT T = (T --> resultT) --> @{typ "code_numeral"} --> resultT

fun dest_monadT (Type ("fun", [Type ("fun", [T, @{typ "(bool * term list) option"}]),
  @{typ "code_numeral => (bool * term list) option"}])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], []);

fun mk_empty T = Const (@{const_name Quickcheck_Exhaustive.pos_bound_cps_empty}, mk_monadT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Quickcheck_Exhaustive.pos_bound_cps_single}, T --> mk_monadT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Quickcheck_Exhaustive.pos_bound_cps_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name Quickcheck_Exhaustive.pos_bound_cps_plus};

fun mk_if cond = Const (@{const_name Quickcheck_Exhaustive.pos_bound_cps_if},
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = error "not implemented yet"

fun mk_not t =
  let
    val nT = @{typ "(unit Quickcheck_Exhaustive.unknown =>
      Code_Evaluation.term list Quickcheck_Exhaustive.three_valued) => code_numeral =>
      Code_Evaluation.term list Quickcheck_Exhaustive.three_valued"}
    val T = mk_monadT HOLogic.unitT
  in Const (@{const_name Quickcheck_Exhaustive.pos_bound_cps_not}, nT --> T) $ t end

fun mk_Enum f = error "not implemented"

fun mk_Eval (f, x) = error "not implemented"

fun dest_Eval t = error "not implemented"

fun mk_map T1 T2 tf tp = error "not implemented"

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;

structure Neg_Bounded_CPS_Comp_Funs =
struct

fun mk_monadT T =
  (Type (@{type_name "Quickcheck_Exhaustive.unknown"}, [T])
    --> @{typ "Code_Evaluation.term list Quickcheck_Exhaustive.three_valued"})
    --> @{typ "code_numeral => Code_Evaluation.term list Quickcheck_Exhaustive.three_valued"}

fun dest_monadT (Type ("fun", [Type ("fun", [Type (@{type_name "Quickcheck_Exhaustive.unknown"}, [T]),
    @{typ "term list Quickcheck_Exhaustive.three_valued"}]),
    @{typ "code_numeral => term list Quickcheck_Exhaustive.three_valued"}])) = T
  | dest_monadT T = raise TYPE ("dest_monadT", [T], []);

fun mk_empty T = Const (@{const_name Quickcheck_Exhaustive.neg_bound_cps_empty}, mk_monadT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Quickcheck_Exhaustive.neg_bound_cps_single}, T --> mk_monadT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Quickcheck_Exhaustive.neg_bound_cps_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name Quickcheck_Exhaustive.neg_bound_cps_plus};

fun mk_if cond = Const (@{const_name Quickcheck_Exhaustive.neg_bound_cps_if},
  HOLogic.boolT --> mk_monadT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = error "not implemented"

fun mk_not t =
  let
    val T = mk_monadT HOLogic.unitT
    val pT = @{typ "(unit => (bool * Code_Evaluation.term list) option)"}
      --> @{typ "code_numeral => (bool * Code_Evaluation.term list) option"}
  in Const (@{const_name Quickcheck_Exhaustive.neg_bound_cps_not}, pT --> T) $ t end

fun mk_Enum f = error "not implemented"

fun mk_Eval (f, x) = error "not implemented"

fun dest_Eval t = error "not implemented"

fun mk_map T1 T2 tf tp = error "not implemented"

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_monadT, dest_monadT = dest_monadT, mk_empty = mk_empty,
    mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;


structure RandomPredCompFuns =
struct

fun mk_randompredT T =
  @{typ Random.seed} --> HOLogic.mk_prodT (Predicate_Comp_Funs.mk_monadT T, @{typ Random.seed})

fun dest_randompredT (Type ("fun", [@{typ Random.seed}, Type (@{type_name Product_Type.prod},
  [Type (@{type_name "Predicate.pred"}, [T]), @{typ Random.seed}])])) = T
  | dest_randompredT T = raise TYPE ("dest_randompredT", [T], []);

fun mk_empty T = Const(@{const_name Quickcheck.empty}, mk_randompredT T)

fun mk_single t =
  let               
    val T = fastype_of t
  in
    Const (@{const_name Quickcheck.single}, T --> mk_randompredT T) $ t
  end;

fun mk_bind (x, f) =
  let
    val T as (Type ("fun", [_, U])) = fastype_of f
  in
    Const (@{const_name Quickcheck.bind}, fastype_of x --> T --> U) $ x $ f
  end

val mk_plus = HOLogic.mk_binop @{const_name Quickcheck.union}

fun mk_if cond = Const (@{const_name Quickcheck.if_randompred},
  HOLogic.boolT --> mk_randompredT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (@{const_name Quickcheck.iterate_upto},
      [@{typ code_numeral} --> T, @{typ code_numeral}, @{typ code_numeral}] ---> mk_randompredT T),
    [f, from, to])

fun mk_not t =
  let
    val T = mk_randompredT HOLogic.unitT
  in Const (@{const_name Quickcheck.not_randompred}, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name Quickcheck.map},
  (T1 --> T2) --> mk_randompredT T1 --> mk_randompredT T2) $ tf $ tp

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_randompredT, dest_monadT = dest_randompredT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;

structure DSequence_CompFuns =
struct

fun mk_dseqT T = Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ bool},
  Type (@{type_name Option.option}, [Type  (@{type_name Lazy_Sequence.lazy_sequence}, [T])])])])

fun dest_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ bool},
  Type (@{type_name Option.option}, [Type (@{type_name Lazy_Sequence.lazy_sequence}, [T])])])])) = T
  | dest_dseqT T = raise TYPE ("dest_dseqT", [T], []);

fun mk_empty T = Const (@{const_name DSequence.empty}, mk_dseqT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name DSequence.single}, T --> mk_dseqT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name DSequence.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name DSequence.union};

fun mk_if cond = Const (@{const_name DSequence.if_seq},
  HOLogic.boolT --> mk_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = raise Fail "No iterate_upto compilation"

fun mk_not t = let val T = mk_dseqT HOLogic.unitT
  in Const (@{const_name DSequence.not_seq}, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name DSequence.map},
  (T1 --> T2) --> mk_dseqT T1 --> mk_dseqT T2) $ tf $ tp

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_dseqT, dest_monadT = dest_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

structure New_Pos_DSequence_CompFuns =
struct

fun mk_pos_dseqT T =
    @{typ code_numeral} --> Type (@{type_name Lazy_Sequence.lazy_sequence}, [T])

fun dest_pos_dseqT (Type ("fun", [@{typ code_numeral},
    Type (@{type_name Lazy_Sequence.lazy_sequence}, [T])])) = T
  | dest_pos_dseqT T = raise TYPE ("dest_pos_dseqT", [T], []);

fun mk_empty T = Const (@{const_name New_DSequence.pos_empty}, mk_pos_dseqT T);

fun mk_single t =
  let
    val T = fastype_of t
  in Const(@{const_name New_DSequence.pos_single}, T --> mk_pos_dseqT T) $ t end;

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_DSequence.pos_bind}, fastype_of x --> T --> U) $ x $ f
  end;
  
fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_DSequence.pos_decr_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name New_DSequence.pos_union};

fun mk_if cond = Const (@{const_name New_DSequence.pos_if_seq},
  HOLogic.boolT --> mk_pos_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = raise Fail "No iterate_upto compilation"

fun mk_not t =
  let
    val pT = mk_pos_dseqT HOLogic.unitT
    val nT =
      @{typ code_numeral} --> Type (@{type_name Lazy_Sequence.lazy_sequence},
        [Type (@{type_name Option.option}, [@{typ unit}])])
  in Const (@{const_name New_DSequence.pos_not_seq}, nT --> pT) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name New_DSequence.pos_map},
  (T1 --> T2) --> mk_pos_dseqT T1 --> mk_pos_dseqT T2) $ tf $ tp

val depth_limited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_dseqT, dest_monadT = dest_pos_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_dseqT, dest_monadT = dest_pos_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

structure New_Neg_DSequence_CompFuns =
struct

fun mk_neg_dseqT T = @{typ code_numeral} -->
  Type (@{type_name Lazy_Sequence.lazy_sequence}, [Type (@{type_name Option.option}, [T])])

fun dest_neg_dseqT (Type ("fun", [@{typ code_numeral},
    Type (@{type_name Lazy_Sequence.lazy_sequence}, [Type (@{type_name Option.option}, [T])])])) = T
  | dest_neg_dseqT T = raise TYPE ("dest_neg_dseqT", [T], []);

fun mk_empty T = Const (@{const_name New_DSequence.neg_empty}, mk_neg_dseqT T);

fun mk_single t =
  let
    val T = fastype_of t
  in Const(@{const_name New_DSequence.neg_single}, T --> mk_neg_dseqT T) $ t end;

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_DSequence.neg_bind}, fastype_of x --> T --> U) $ x $ f
  end;
  
fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_DSequence.neg_decr_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name New_DSequence.neg_union};

fun mk_if cond = Const (@{const_name New_DSequence.neg_if_seq},
  HOLogic.boolT --> mk_neg_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = raise Fail "No iterate_upto compilation"

fun mk_not t =
  let
    val nT = mk_neg_dseqT HOLogic.unitT
    val pT =
      @{typ code_numeral} --> Type (@{type_name Lazy_Sequence.lazy_sequence},
        [@{typ unit}])
  in Const (@{const_name New_DSequence.neg_not_seq}, pT --> nT) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name New_DSequence.neg_map},
  (T1 --> T2) --> mk_neg_dseqT T1 --> mk_neg_dseqT T2) $ tf $ tp

val depth_limited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_dseqT, dest_monadT = dest_neg_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_dseqT, dest_monadT = dest_neg_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

structure New_Pos_Random_Sequence_CompFuns =
struct

fun mk_pos_random_dseqT T =
  @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
    @{typ code_numeral} --> Type (@{type_name Lazy_Sequence.lazy_sequence}, [T])

fun dest_pos_random_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ code_numeral},
    Type ("fun", [@{typ Random.seed}, Type ("fun", [@{typ code_numeral},
    Type (@{type_name Lazy_Sequence.lazy_sequence}, [T])])])])])) = T
  | dest_pos_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], []);

fun mk_empty T = Const (@{const_name New_Random_Sequence.pos_empty}, mk_pos_random_dseqT T);

fun mk_single t =
  let
    val T = fastype_of t
  in Const(@{const_name New_Random_Sequence.pos_single}, T --> mk_pos_random_dseqT T) $ t end;

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_Random_Sequence.pos_bind}, fastype_of x --> T --> U) $ x $ f
  end;

fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_Random_Sequence.pos_decr_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name New_Random_Sequence.pos_union};

fun mk_if cond = Const (@{const_name New_Random_Sequence.pos_if_random_dseq},
  HOLogic.boolT --> mk_pos_random_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (@{const_name New_Random_Sequence.pos_iterate_upto},
      [@{typ code_numeral} --> T, @{typ code_numeral}, @{typ code_numeral}]
        ---> mk_pos_random_dseqT T),
    [f, from, to])

fun mk_not t =
  let
    val pT = mk_pos_random_dseqT HOLogic.unitT
    val nT = @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
      @{typ code_numeral} --> Type (@{type_name Lazy_Sequence.lazy_sequence},
        [Type (@{type_name Option.option}, [@{typ unit}])])

  in Const (@{const_name New_Random_Sequence.pos_not_random_dseq}, nT --> pT) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name New_Random_Sequence.pos_map},
  (T1 --> T2) --> mk_pos_random_dseqT T1 --> mk_pos_random_dseqT T2) $ tf $ tp

val depth_limited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_random_dseqT, dest_monadT = dest_pos_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_pos_random_dseqT, dest_monadT = dest_pos_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}
end;

structure New_Neg_Random_Sequence_CompFuns =
struct

fun mk_neg_random_dseqT T =
   @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
    @{typ code_numeral} --> 
    Type (@{type_name Lazy_Sequence.lazy_sequence}, [Type (@{type_name Option.option}, [T])])

fun dest_neg_random_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ code_numeral},
    Type ("fun", [@{typ Random.seed}, Type ("fun", [@{typ code_numeral},
      Type (@{type_name Lazy_Sequence.lazy_sequence},
        [Type (@{type_name Option.option}, [T])])])])])])) = T
  | dest_neg_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], []);

fun mk_empty T = Const (@{const_name New_Random_Sequence.neg_empty}, mk_neg_random_dseqT T);

fun mk_single t =
  let
    val T = fastype_of t
  in Const(@{const_name New_Random_Sequence.neg_single}, T --> mk_neg_random_dseqT T) $ t end;

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_Random_Sequence.neg_bind}, fastype_of x --> T --> U) $ x $ f
  end;

fun mk_decr_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name New_Random_Sequence.neg_decr_bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name New_Random_Sequence.neg_union};

fun mk_if cond = Const (@{const_name New_Random_Sequence.neg_if_random_dseq},
  HOLogic.boolT --> mk_neg_random_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (@{const_name New_Random_Sequence.neg_iterate_upto},
      [@{typ code_numeral} --> T, @{typ code_numeral}, @{typ code_numeral}]
        ---> mk_neg_random_dseqT T),
    [f, from, to])

fun mk_not t =
  let
    val nT = mk_neg_random_dseqT HOLogic.unitT
    val pT = @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
    @{typ code_numeral} --> Type (@{type_name Lazy_Sequence.lazy_sequence}, [@{typ unit}])
  in Const (@{const_name New_Random_Sequence.neg_not_random_dseq}, pT --> nT) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name New_Random_Sequence.neg_map},
  (T1 --> T2) --> mk_neg_random_dseqT T1 --> mk_neg_random_dseqT T2) $ tf $ tp

val depth_limited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_random_dseqT, dest_monadT = dest_neg_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_decr_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

val depth_unlimited_compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_neg_random_dseqT, dest_monadT = dest_neg_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

structure Random_Sequence_CompFuns =
struct

fun mk_random_dseqT T =
  @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
    HOLogic.mk_prodT (DSequence_CompFuns.mk_dseqT T, @{typ Random.seed})

fun dest_random_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ code_numeral},
  Type ("fun", [@{typ Random.seed},
  Type (@{type_name Product_Type.prod}, [T, @{typ Random.seed}])])])])) = DSequence_CompFuns.dest_dseqT T
  | dest_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], []);

fun mk_empty T = Const (@{const_name Random_Sequence.empty}, mk_random_dseqT T);

fun mk_single t =
  let
    val T = fastype_of t
  in Const(@{const_name Random_Sequence.single}, T --> mk_random_dseqT T) $ t end;

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Random_Sequence.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_plus = HOLogic.mk_binop @{const_name Random_Sequence.union};

fun mk_if cond = Const (@{const_name Random_Sequence.if_random_dseq},
  HOLogic.boolT --> mk_random_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = raise Fail "No iterate_upto compilation"

fun mk_not t =
  let
    val T = mk_random_dseqT HOLogic.unitT
  in Const (@{const_name Random_Sequence.not_random_dseq}, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name Random_Sequence.map},
  (T1 --> T2) --> mk_random_dseqT T1 --> mk_random_dseqT T2) $ tf $ tp

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_monadT = mk_random_dseqT, dest_monadT = dest_random_dseqT,
    mk_empty = mk_empty, mk_single = mk_single, mk_bind = mk_bind, mk_plus = mk_plus, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

