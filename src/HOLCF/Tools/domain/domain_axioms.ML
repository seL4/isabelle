(*  Title:      HOLCF/Tools/domain/domain_axioms.ML
    ID:         $Id$
    Author:     David von Oheimb

Syntax generator for domain command.
*)

structure Domain_Axioms = struct

local

open Domain_Library;
infixr 0 ===>;infixr 0 ==>;infix 0 == ; 
infix 1 ===; infix 1 ~= ; infix 1 <<; infix 1 ~<<;
infix 9 `   ; infix 9 `% ; infix 9 `%%; infixr 9 oo;

fun calc_axioms comp_dname (eqs : eq list) n (((dname,_),cons) : eq)=
let

(* ----- axioms and definitions concerning the isomorphism ------------------ *)

  val dc_abs = %%:(dname^"_abs");
  val dc_rep = %%:(dname^"_rep");
  val x_name'= "x";
  val x_name = idx_name eqs x_name' (n+1);
  val dnam = Sign.base_name dname;

  val abs_iso_ax = ("abs_iso", mk_trp(dc_rep`(dc_abs`%x_name') === %:x_name'));
  val rep_iso_ax = ("rep_iso", mk_trp(dc_abs`(dc_rep`%x_name') === %:x_name'));

  val when_def = ("when_def",%%:(dname^"_when") == 
     foldr (uncurry /\ ) (/\x_name'((when_body cons (fn (x,y) =>
				Bound(1+length cons+x-y)))`(dc_rep`Bound 0))) (when_funs cons));
  
  val copy_def = let
    fun idxs z x arg = if is_rec arg
			 then (cproj (Bound z) eqs (rec_of arg))`Bound(z-x)
			 else Bound(z-x);
    fun one_con (con,args) =
        foldr /\# (list_ccomb (%%:con, mapn (idxs (length args)) 1 args)) args;
  in ("copy_def", %%:(dname^"_copy") ==
       /\ "f" (list_ccomb (%%:(dname^"_when"), map one_con cons))) end;

(* -- definitions concerning the constructors, discriminators and selectors - *)

  fun con_def m n (_,args) = let
    fun idxs z x arg = (if is_lazy arg then mk_up else I) (Bound(z-x));
    fun parms vs = mk_stuple (mapn (idxs(length vs)) 1 vs);
    fun inj y 1 _ = y
    |   inj y _ 0 = mk_sinl y
    |   inj y i j = mk_sinr (inj y (i-1) (j-1));
  in foldr /\# (dc_abs`(inj (parms args) m n)) args end;
  
  val con_defs = mapn (fn n => fn (con,args) =>
    (extern_name con ^"_def", %%:con == con_def (length cons) n (con,args))) 0 cons;
  
  val dis_defs = let
	fun ddef (con,_) = (dis_name con ^"_def",%%:(dis_name con) == 
		 list_ccomb(%%:(dname^"_when"),map 
			(fn (con',args) => (foldr /\#
			   (if con'=con then TT else FF) args)) cons))
	in map ddef cons end;

  val mat_defs = let
	fun mdef (con,_) = (mat_name con ^"_def",%%:(mat_name con) == 
		 list_ccomb(%%:(dname^"_when"),map 
			(fn (con',args) => (foldr /\#
			   (if con'=con
                               then mk_return (mk_ctuple (map (bound_arg args) args))
                               else mk_fail) args)) cons))
	in map mdef cons end;

  val pat_defs =
    let
      fun pdef (con,args) =
        let
          val ps = mapn (fn n => fn _ => %:("pat" ^ string_of_int n)) 1 args;
          val xs = map (bound_arg args) args;
          val r = Bound (length args);
          val rhs = case args of [] => mk_return HOLogic.unit
                                | _ => mk_ctuple_pat ps ` mk_ctuple xs;
          fun one_con (con',args') = foldr /\# (if con'=con then rhs else mk_fail) args';
        in (pat_name con ^"_def", list_comb (%%:(pat_name con), ps) == 
               list_ccomb(%%:(dname^"_when"), map one_con cons))
        end
    in map pdef cons end;

  val sel_defs = let
	fun sdef con n arg = Option.map (fn sel => (sel^"_def",%%:sel == 
		 list_ccomb(%%:(dname^"_when"),map 
			(fn (con',args) => if con'<>con then UU else
			 foldr /\# (Bound (length args - n)) args) cons))) (sel_of arg);
	in List.mapPartial I (List.concat(map (fn (con,args) => mapn (sdef con) 1 args) cons)) end;


(* ----- axiom and definitions concerning induction ------------------------- *)

  val reach_ax = ("reach", mk_trp(cproj (mk_fix (%%:(comp_dname^"_copy"))) eqs n
					`%x_name === %:x_name));
  val take_def = ("take_def",%%:(dname^"_take") == mk_lam("n",cproj
	     (mk_iterate (Bound 0, %%:(comp_dname^"_copy"), UU)) eqs n));
  val finite_def = ("finite_def",%%:(dname^"_finite") == mk_lam(x_name,
	mk_ex("n",(%%:(dname^"_take") $ Bound 0)`Bound 1 === Bound 1)));

in (dnam,
    [abs_iso_ax, rep_iso_ax, reach_ax],
    [when_def, copy_def] @
     con_defs @ dis_defs @ mat_defs @ pat_defs @ sel_defs @
    [take_def, finite_def])
end; (* let (calc_axioms) *)

fun infer_props thy = map (apsnd (FixrecPackage.legacy_infer_prop thy));

fun add_axioms_i x = snd o PureThy.add_axioms (map (Thm.no_attributes o apfst Binding.name) x);
fun add_axioms_infer axms thy = add_axioms_i (infer_props thy axms) thy;

fun add_defs_i x = snd o (PureThy.add_defs false) (map (Thm.no_attributes o apfst Binding.name) x);
fun add_defs_infer defs thy = add_defs_i (infer_props thy defs) thy;

fun add_matchers (((dname,_),cons) : eq) thy =
  let
    val con_names = map fst cons;
    val mat_names = map mat_name con_names;
    fun qualify n = Sign.full_name thy (Binding.name n);
    val ms = map qualify con_names ~~ map qualify mat_names;
  in FixrecPackage.add_matchers ms thy end;

in (* local *)

fun add_axioms (comp_dnam, eqs : eq list) thy' = let
  val comp_dname = Sign.full_bname thy' comp_dnam;
  val dnames = map (fst o fst) eqs;
  val x_name = idx_name dnames "x"; 
  fun copy_app dname = %%:(dname^"_copy")`Bound 0;
  val copy_def = ("copy_def" , %%:(comp_dname^"_copy") ==
				    /\ "f"(mk_ctuple (map copy_app dnames)));
  val bisim_def = ("bisim_def",%%:(comp_dname^"_bisim")==mk_lam("R",
    let
      fun one_con (con,args) = let
	val nonrec_args = filter_out is_rec args;
	val    rec_args = List.filter     is_rec args;
	val    recs_cnt = length rec_args;
	val allargs     = nonrec_args @ rec_args
				      @ map (upd_vname (fn s=> s^"'")) rec_args;
	val allvns      = map vname allargs;
	fun vname_arg s arg = if is_rec arg then vname arg^s else vname arg;
	val vns1        = map (vname_arg "" ) args;
	val vns2        = map (vname_arg "'") args;
	val allargs_cnt = length nonrec_args + 2*recs_cnt;
	val rec_idxs    = (recs_cnt-1) downto 0;
	val nonlazy_idxs = map snd (filter_out (fn (arg,_) => is_lazy arg)
					 (allargs~~((allargs_cnt-1) downto 0)));
	fun rel_app i ra = proj (Bound(allargs_cnt+2)) eqs (rec_of ra) $ 
			   Bound (2*recs_cnt-i) $ Bound (recs_cnt-i);
	val capps = foldr mk_conj (mk_conj(
	   Bound(allargs_cnt+1)===list_ccomb(%%:con,map (bound_arg allvns) vns1),
	   Bound(allargs_cnt+0)===list_ccomb(%%:con,map (bound_arg allvns) vns2)))
           (mapn rel_app 1 rec_args);
        in foldr mk_ex (Library.foldr mk_conj 
			      (map (defined o Bound) nonlazy_idxs,capps)) allvns end;
      fun one_comp n (_,cons) =mk_all(x_name(n+1),mk_all(x_name(n+1)^"'",mk_imp(
	 		proj (Bound 2) eqs n $ Bound 1 $ Bound 0,
         		foldr1 mk_disj (mk_conj(Bound 1 === UU,Bound 0 === UU)
					::map one_con cons))));
    in foldr1 mk_conj (mapn one_comp 0 eqs)end ));
  fun add_one (thy,(dnam,axs,dfs)) = thy
	|> Sign.add_path dnam
	|> add_defs_infer dfs
	|> add_axioms_infer axs
	|> Sign.parent_path;
  val thy = Library.foldl add_one (thy', mapn (calc_axioms comp_dname eqs) 0 eqs);
in thy |> Sign.add_path comp_dnam  
       |> add_defs_infer (bisim_def::(if length eqs>1 then [copy_def] else []))
       |> Sign.parent_path
       |> fold add_matchers eqs
end; (* let (add_axioms) *)

end; (* local *)
end; (* struct *)
