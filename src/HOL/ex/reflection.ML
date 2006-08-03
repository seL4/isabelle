(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

A trial for automatical reification.
*)

signature REFLECTION = sig
  val genreify_tac: Proof.context -> thm list -> term option -> int -> tactic
  val reflection_tac: Proof.context -> thm list -> term option -> int -> tactic
end;

structure Reflection : REFLECTION
= struct

    (* Make a congruence rule out of a defining equation for the interpretation *)
        (* th is one defining equation of f, i.e.
           th is "f (Cp ?t1 ... ?tn) = P(f ?t1, .., f ?tn)" *)
        (* Cp is a constructor pattern and P is a pattern *)

        (* The result is:
         [|?A1 = f ?t1 ; .. ; ?An= f ?tn |] ==> P (?A1, .., ?An) = f (Cp ?t1 .. ?tn) *)
        (*  + the a list of names of the A1 .. An, Those are fresh in the ctxt*)

fun mk_congeq ctxt fs th =
  let
    val Const(fname,fT)$(Free(_,_))$_ =
        (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) th
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;
    fun dest_listT (Type ("List.list",[vT])) = vT;
    val vT = dest_listT (Term.domain_type fT);
    val (((_,_),[th']), ctxt') = Variable.import true [th] ctxt;
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th'));

    fun add_fterms (t as t1 $ t2 $ t3) =
          if exists (fn f => t1 aconv f) fs then insert (op aconv) t
          else add_fterms (t1 $ t2) #> add_fterms t3
      | add_fterms (t1 $ t2) = add_fterms t1 #> add_fterms t2
      | add_fterms (Abs _) = sys_error "FIXME"
      | add_fterms _ = I;
    val fterms = add_fterms rhs [];

    val (xs, ctxt'') = Variable.invent_fixes (replicate (length fterms) "x") ctxt';
    val tys = map fastype_of fterms
    val vs = map Free (xs ~~ tys);
    val env = fterms ~~ vs;

    fun replace_fterms (t as t1 $ t2 $ t3) =
          (case AList.lookup (op aconv) env t of
            SOME v => v
          | NONE => replace_fterms (t1 $ t2) $ replace_fterms t3)
      | replace_fterms (t1 $ t2) = replace_fterms t1 $ replace_fterms t2
      | replace_fterms t = t;

    fun mk_def (t, v) = HOLogic.mk_Trueprop (HOLogic.mk_eq (v, t));
    val cong = (Goal.prove ctxt'' [] (map mk_def env)
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, replace_fterms rhs)))
      (fn x => LocalDefs.unfold_tac (#context x) (#prems x) THEN rtac th' 1)) RS sym;

    val (cong' :: vars') = Variable.export ctxt'' ctxt
      (cong :: map (Drule.mk_term o cert) vs);
    val vs' = map (fst o fst o Term.dest_Var o Thm.term_of o Drule.dest_term) vars';
  in (vs', cong') end;

 (* congs is a list of pairs (P,th) where th is a theorem for *)
        (* [| f p1 = A1; ...; f pn = An|] ==> f (C p1 .. pn) = P *)
val FWD = curry (op OF);

 (* da is the decomposition for atoms, ie. it returns ([],g) where g
 returns the right instance f (AtC n) = t , where AtC is the Atoms
 constructor and n is the number of the atom corresponding to t *)

(* Generic decomp for reification : matches the actual term with the
rhs of one cong rule. The result of the matching guides the
proof synthesis: The matches of the introduced Variables A1 .. An are
processed recursively
 The rest is instantiated in the cong rule,i.e. no reification is needed *)

 fun decomp_genreif thy da ((vns,cong)::congs) t =
    ((let
        val cert = cterm_of thy
        val (_, tmenv) =
        Pattern.match thy
        ((fst o HOLogic.dest_eq o HOLogic.dest_Trueprop) (concl_of cong), t)
        (Envir.type_env (Envir.empty 0),Term.Vartab.empty)
        val (fnvs,invs) = List.partition (fn ((vn,_),_) => vn mem vns) (Vartab.dest tmenv)
        val (fts,its) = (map (snd o snd) fnvs,
                         map (fn ((vn,vi),(tT,t)) => (cert(Var ((vn,vi),tT)), cert t)) invs)
    in (fts, FWD (instantiate ([], its) cong))
    end)
      handle MATCH => decomp_genreif thy da congs t)
   | decomp_genreif thy da [] t = da t;

     (* We add the atoms here during reification *)
val env = ref ([]: (term list));

fun env_index t =
    let val i = find_index_eq t (!env)
    in if i = ~1 then (env:= (!env)@[t] ; (length (!env)) - 1) else i  end;

exception REIF of string;

          (* looks for the atoms equation and instantiates it with the right number *)
fun mk_decompatom thy eqs =
    let fun isateq (_$_$(Const("List.nth",_)$_$_)) = true
          | isateq _ = false
    in case List.find (isateq o HOLogic.dest_Trueprop o prop_of) eqs of
           NONE => raise REIF "Can not find the atoms equation"
         | SOME th =>
           fn t => ([],
                    fn ths =>
                       instantiate' [] [SOME(cterm_of thy (HOLogic.mk_nat(env_index t)))]
                                    (th RS sym))
    end;

  (* Generic reification procedure: *)
  (* creates all needed cong rules and then just uses the theorem synthesis *)
fun genreif ctxt raw_eqs t =
    let val ([x], ctxt') = Variable.invent_fixes ["vs"] ctxt
        val thy = ProofContext.theory_of ctxt'
        val cert = cterm_of thy
        val Const(fname,fT)$(Var(_,vT))$_ =
            (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) (hd raw_eqs)
        val cv = cert (Free(x, vT))
        val eqs = map (instantiate' [] [SOME cv]) raw_eqs
        val fs =
            foldr (fn (eq,fns) =>
                      let val f$_$_ =  (fst o HOLogic.dest_eq o
                                        HOLogic.dest_Trueprop o prop_of) eq
                      in f ins fns end) [] eqs
        val congs = map (mk_congeq ctxt' fs) eqs
        val _ = (env := [])
        val da = mk_decompatom thy eqs
        val [th] = Variable.export ctxt' ctxt
                 [divide_and_conquer (decomp_genreif thy da congs) t]
        val cv' = cterm_of (ProofContext.theory_of ctxt)
                           (HOLogic.mk_list I (body_type fT) (!env))
        val _ = (env := [])
        val th' = instantiate' [] [SOME cv'] th
        val t' = (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) th'
        val th'' = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t')))
                   (fn _ => Simp_tac 1)
    in FWD trans [th'',th']
    end;

fun genreflect ctxt corr_thm raw_eqs t =
    let val th = FWD trans [genreif ctxt raw_eqs t, corr_thm RS sym]
        val ft = (snd o Thm.dest_comb o snd o Thm.dest_comb o snd o Thm.dest_comb o cprop_of) th
        val rth = normalization_conv ft
    in simplify (HOL_basic_ss addsimps raw_eqs addsimps [nth_Cons_0, nth_Cons_Suc])
                (simplify (HOL_basic_ss addsimps [rth]) th)
    end

fun genreify_tac ctxt eqs to i = (fn st =>
  let
    val P = HOLogic.dest_Trueprop (List.nth (prems_of st, i - 1))
    val t = (case to of NONE => P | SOME x => x)
    val th = (genreif ctxt eqs t) RS ssubst
  in rtac th i st
  end);

    (* Reflection calls reification and uses the correctness *)
        (* theorem assumed to be the dead of the list *)
 fun reflection_tac ctxt (corr_thm::raw_eqs) to i =
    (fn st =>
        let val P = (HOLogic.dest_Trueprop (List.nth (prems_of st, i - 1)))
            val t = (case to of NONE => P | SOME x => x)
            val th = (genreflect ctxt corr_thm raw_eqs t) RS ssubst
        in rtac th i st end);

end
