(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_compilations.ML
    Author:     Lukas Bulwahn, TU Muenchen

Structures for different compilations of the predicate compiler
*)

structure PredicateCompFuns =
struct

fun mk_predT T = Type (@{type_name Predicate.pred}, [T])

fun dest_predT (Type (@{type_name Predicate.pred}, [T])) = T
  | dest_predT T = raise TYPE ("dest_predT", [T], []);

fun mk_bot T = Const (@{const_name Orderings.bot}, mk_predT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Predicate.single}, T --> mk_predT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Predicate.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop @{const_name sup};

fun mk_if cond = Const (@{const_name Predicate.if_pred},
  HOLogic.boolT --> mk_predT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) =
  list_comb (Const (@{const_name Code_Numeral.iterate_upto},
      [@{typ code_numeral} --> T, @{typ code_numeral}, @{typ code_numeral}] ---> mk_predT T),
    [f, from, to])

fun mk_not t =
  let
    val T = mk_predT HOLogic.unitT
  in Const (@{const_name Predicate.not_pred}, T --> T) $ t end

fun mk_Enum f =
  let val T as Type ("fun", [T', _]) = fastype_of f
  in
    Const (@{const_name Predicate.Pred}, T --> mk_predT T') $ f    
  end;

fun mk_Eval (f, x) =
  let
    val T = fastype_of x
  in
    Const (@{const_name Predicate.eval}, mk_predT T --> T --> HOLogic.boolT) $ f $ x
  end;

fun dest_Eval (Const (@{const_name Predicate.eval}, _) $ f $ x) = (f, x)

fun mk_map T1 T2 tf tp = Const (@{const_name Predicate.map},
  (T1 --> T2) --> mk_predT T1 --> mk_predT T2) $ tf $ tp;

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_predT = mk_predT, dest_predT = dest_predT, mk_bot = mk_bot,
    mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;

structure RandomPredCompFuns =
struct

fun mk_randompredT T =
  @{typ Random.seed} --> HOLogic.mk_prodT (PredicateCompFuns.mk_predT T, @{typ Random.seed})

fun dest_randompredT (Type ("fun", [@{typ Random.seed}, Type (@{type_name "*"},
  [Type (@{type_name "Predicate.pred"}, [T]), @{typ Random.seed}])])) = T
  | dest_randompredT T = raise TYPE ("dest_randompredT", [T], []);

fun mk_bot T = Const(@{const_name Quickcheck.empty}, mk_randompredT T)

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

val mk_sup = HOLogic.mk_binop @{const_name Quickcheck.union}

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
    {mk_predT = mk_randompredT, dest_predT = dest_randompredT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map};

end;

structure DSequence_CompFuns =
struct

fun mk_dseqT T = Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ bool},
  Type (@{type_name Option.option}, [Type  (@{type_name Lazy_Sequence.lazy_sequence}, [T])])])])

fun dest_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ bool},
  Type (@{type_name Option.option}, [Type (@{type_name Lazy_Sequence.lazy_sequence}, [T])])])])) = T
  | dest_dseqT T = raise TYPE ("dest_dseqT", [T], []);

fun mk_bot T = Const (@{const_name DSequence.empty}, mk_dseqT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name DSequence.single}, T --> mk_dseqT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name DSequence.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop @{const_name DSequence.union};

fun mk_if cond = Const (@{const_name DSequence.if_seq},
  HOLogic.boolT --> mk_dseqT HOLogic.unitT) $ cond;

fun mk_iterate_upto T (f, from, to) = raise Fail "No iterate_upto compilation"

fun mk_not t = let val T = mk_dseqT HOLogic.unitT
  in Const (@{const_name DSequence.not_seq}, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name DSequence.map},
  (T1 --> T2) --> mk_dseqT T1 --> mk_dseqT T2) $ tf $ tp

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_predT = mk_dseqT, dest_predT = dest_dseqT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
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

fun mk_bot T = Const (@{const_name New_Random_Sequence.pos_empty}, mk_pos_random_dseqT T);

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

val mk_sup = HOLogic.mk_binop @{const_name New_Random_Sequence.pos_union};

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

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_predT = mk_pos_random_dseqT, dest_predT = dest_pos_random_dseqT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
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

fun mk_bot T = Const (@{const_name New_Random_Sequence.neg_empty}, mk_neg_random_dseqT T);

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

val mk_sup = HOLogic.mk_binop @{const_name New_Random_Sequence.neg_union};

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

val compfuns = Predicate_Compile_Aux.CompilationFuns
    {mk_predT = mk_neg_random_dseqT, dest_predT = dest_neg_random_dseqT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

structure Random_Sequence_CompFuns =
struct

fun mk_random_dseqT T =
  @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
    HOLogic.mk_prodT (DSequence_CompFuns.mk_dseqT T, @{typ Random.seed})

fun dest_random_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ code_numeral},
  Type ("fun", [@{typ Random.seed},
  Type (@{type_name "*"}, [T, @{typ Random.seed}])])])])) = DSequence_CompFuns.dest_dseqT T
  | dest_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], []);

fun mk_bot T = Const (@{const_name Random_Sequence.empty}, mk_random_dseqT T);

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

val mk_sup = HOLogic.mk_binop @{const_name Random_Sequence.union};

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
    {mk_predT = mk_random_dseqT, dest_predT = dest_random_dseqT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_iterate_upto = mk_iterate_upto, mk_not = mk_not, mk_map = mk_map}

end;

