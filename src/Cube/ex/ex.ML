(* Examples taken from
        H. Barendregt. Introduction to Generalised Type Systems.
        J. Functional Programming.
*)

fun strip_asms_tac thms  i =
    REPEAT(resolve_tac[strip_b,strip_s]i THEN DEPTH_SOLVE_1(ares_tac thms i));

val imp_elim = prove_goal thy "[| f:A->B; a:A; f^a:B ==> PROP P |] ==> PROP P"
        (fn asms => [REPEAT(resolve_tac (app::asms) 1)]);

val pi_elim = prove_goal thy
        "[| F:Prod(A,B); a:A; F^a:B(a) ==> PROP P |] ==> PROP P"
        (fn asms => [REPEAT(resolve_tac (app::asms) 1)]);

(* SIMPLE TYPES *)

goal thy "A:* |- A->A : ?T";
by (DEPTH_SOLVE (ares_tac simple 1));
uresult();

goal thy "A:* |- Lam a:A. a : ?T";
by (DEPTH_SOLVE (ares_tac simple 1));
uresult();

goal thy "A:* B:* b:B |- Lam x:A. b : ?T";
by (DEPTH_SOLVE (ares_tac simple 1));
uresult();

goal thy "A:* b:A |- (Lam a:A. a)^b: ?T";
by (DEPTH_SOLVE (ares_tac simple 1));
uresult();

goal thy "A:* B:* c:A b:B |- (Lam x:A. b)^ c: ?T";
by (DEPTH_SOLVE (ares_tac simple 1));
uresult();

goal thy "A:* B:* |- Lam a:A. Lam b:B. a : ?T";
by (DEPTH_SOLVE (ares_tac simple 1));
uresult();

(* SECOND-ORDER TYPES *)

goal L2_thy "|- Lam A:*. Lam a:A. a : ?T";
by (DEPTH_SOLVE (ares_tac L2 1));
uresult();

goal L2_thy "A:* |- (Lam B:*.Lam b:B. b)^A : ?T";
by (DEPTH_SOLVE (ares_tac L2 1));
uresult();

goal L2_thy "A:* b:A |- (Lam B:*.Lam b:B. b) ^ A ^ b: ?T";
by (DEPTH_SOLVE (ares_tac L2 1));
uresult();

goal L2_thy "|- Lam B:*.Lam a:(Pi A:*.A).a ^ ((Pi A:*.A)->B) ^ a: ?T";
by (DEPTH_SOLVE (ares_tac L2 1));
uresult();

(* Weakly higher-order proposiional logic *)

goal Lomega_thy "|- Lam A:*.A->A : ?T";
by (DEPTH_SOLVE (ares_tac Lomega 1));
uresult();

goal Lomega_thy "B:* |- (Lam A:*.A->A) ^ B : ?T";
by (DEPTH_SOLVE (ares_tac Lomega 1));
uresult();

goal Lomega_thy "B:* b:B |- (Lam y:B. b): ?T";
by (DEPTH_SOLVE (ares_tac Lomega 1));
uresult();

goal Lomega_thy "A:* F:*->* |- F^(F^A): ?T";
by (DEPTH_SOLVE (ares_tac Lomega 1));
uresult();

goal Lomega_thy "A:* |- Lam F:*->*.F^(F^A): ?T";
by (DEPTH_SOLVE (ares_tac Lomega 1));
uresult();

(* LF *)

goal LP_thy "A:* |- A -> * : ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->* a:A |- P^a: ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->A->* a:A |- Pi a:A. P^a^a: ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->* Q:A->* |- Pi a:A. P^a -> Q^a: ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->* |- Pi a:A. P^a -> P^a: ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->* |- Lam a:A. Lam x:P^a. x: ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->* Q:* |- (Pi a:A. P^a->Q) -> (Pi a:A. P^a) -> Q : ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

goal LP_thy "A:* P:A->* Q:* a0:A |- \
\       Lam x:Pi a:A. P^a->Q. Lam y:Pi a:A. P^a. x^a0^(y^a0): ?T";
by (DEPTH_SOLVE (ares_tac LP 1));
uresult();

(* OMEGA-ORDER TYPES *)

goal L2_thy "A:* B:* |- Pi C:*.(A->B->C)->C : ?T";
by (DEPTH_SOLVE (ares_tac L2 1));
uresult();

goal LOmega_thy "|- Lam A:*.Lam B:*.Pi C:*.(A->B->C)->C : ?T";
by (DEPTH_SOLVE (ares_tac LOmega 1));
uresult();

goal LOmega_thy "|- Lam A:*.Lam B:*.Lam x:A. Lam y:B. x : ?T";
by (DEPTH_SOLVE (ares_tac LOmega 1));
uresult();

goal LOmega_thy "A:* B:* |- ?p : (A->B) -> ((B->Pi P:*.P)->(A->Pi P:*.P))";
by (strip_asms_tac LOmega 1);
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac LOmega 1));
by (DEPTH_SOLVE_1(ares_tac LOmega 2));
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac LOmega 1));
by (DEPTH_SOLVE_1(ares_tac LOmega 2));
by (rtac lam_ss 1);
by (assume_tac 1);
by (DEPTH_SOLVE_1(ares_tac LOmega 2));
by (etac pi_elim 1);
by (assume_tac 1);
by (etac pi_elim 1);
by (assume_tac 1);
by (assume_tac 1);
uresult();

(* Second-order Predicate Logic *)

goal LP2_thy "A:* P:A->* |- Lam a:A. P^a->(Pi A:*.A) : ?T";
by (DEPTH_SOLVE (ares_tac LP2 1));
uresult();

goal LP2_thy "A:* P:A->A->* |- \
\       (Pi a:A. Pi b:A. P^a^b->P^b^a->Pi P:*.P) -> Pi a:A. P^a^a->Pi P:*.P : ?T";
by (DEPTH_SOLVE (ares_tac LP2 1));
uresult();

(* Antisymmetry implies irreflexivity: *)
goal LP2_thy "A:* P:A->A->* |- \
\       ?p: (Pi a:A. Pi b:A. P^a^b->P^b^a->Pi P:*.P) -> Pi a:A. P^a^a->Pi P:*.P";
by (strip_asms_tac LP2 1);
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac LP2 1));
by (DEPTH_SOLVE_1(ares_tac LP2 2));
by (rtac lam_ss 1);
by (assume_tac 1);
by (DEPTH_SOLVE_1(ares_tac LP2 2));
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac LP2 1));
by (DEPTH_SOLVE_1(ares_tac LP2 2));
by (REPEAT(EVERY[etac pi_elim 1, assume_tac 1, TRY(assume_tac 1)]));
uresult();

(* LPomega *)

goal LPomega_thy "A:* |- Lam P:A->A->*.Lam a:A. P^a^a : ?T";
by (DEPTH_SOLVE (ares_tac LPomega 1));
uresult();

goal LPomega_thy "|- Lam A:*.Lam P:A->A->*.Lam a:A. P^a^a : ?T";
by (DEPTH_SOLVE (ares_tac LPomega 1));
uresult();

(* CONSTRUCTIONS *)

goal CC_thy "|- Lam A:*.Lam P:A->*.Lam a:A. P^a->Pi P:*.P: ?T";
by (DEPTH_SOLVE (ares_tac CC 1));
uresult();

goal CC_thy "|- Lam A:*.Lam P:A->*.Pi a:A. P^a: ?T";
by (DEPTH_SOLVE (ares_tac CC 1));
uresult();

goal CC_thy "A:* P:A->* a:A |- ?p : (Pi a:A. P^a)->P^a";
by (strip_asms_tac CC 1);
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac CC 1));
by (DEPTH_SOLVE_1(ares_tac CC 2));
by (EVERY[etac pi_elim 1, assume_tac 1, assume_tac 1]);
uresult();

(* Some random examples *)

goal LP2_thy "A:* c:A f:A->A |- \
\       Lam a:A. Pi P:A->*.P^c -> (Pi x:A. P^x->P^(f^x)) -> P^a : ?T";
by (DEPTH_SOLVE(ares_tac LP2 1));
uresult();

goal CC_thy "Lam A:*.Lam c:A. Lam f:A->A. \
\       Lam a:A. Pi P:A->*.P^c -> (Pi x:A. P^x->P^(f^x)) -> P^a : ?T";
by (DEPTH_SOLVE(ares_tac CC 1));
uresult();

(* Symmetry of Leibnitz equality *)
goal LP2_thy "A:* a:A b:A |- ?p: (Pi P:A->*.P^a->P^b) -> (Pi P:A->*.P^b->P^a)";
by (strip_asms_tac LP2 1);
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac LP2 1));
by (DEPTH_SOLVE_1(ares_tac LP2 2));
by (eres_inst_tac [("a","Lam x:A. Pi Q:A->*.Q^x->Q^a")] pi_elim 1);
by (DEPTH_SOLVE_1(ares_tac LP2 1));
by (rewtac beta);
by (etac imp_elim 1);
by (rtac lam_bs 1);
by (DEPTH_SOLVE_1(ares_tac LP2 1));
by (DEPTH_SOLVE_1(ares_tac LP2 2));
by (rtac lam_ss 1);
by (DEPTH_SOLVE_1(ares_tac LP2 1));
by (DEPTH_SOLVE_1(ares_tac LP2 2));
by (assume_tac 1);
by (assume_tac 1);
uresult();
