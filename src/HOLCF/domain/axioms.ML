(*  Title:      HOLCF/domain/axioms.ML
    ID:         $Id$
    Author : David von Oheimb
    Copyright 1995, 1996 TU Muenchen

syntax generator for domain section
*)

structure Domain_Axioms = struct

local

open Domain_Library;
infixr 0 ===>;infixr 0 ==>;infix 0 == ; 
infix 1 ===; infix 1 ~= ; infix 1 <<; infix 1 ~<<;
infix 9 `   ; infix 9 `% ; infix 9 `%%; infixr 9 oo;

fun infer_types thy' = map (inferT_axm (sign_of thy'));

fun calc_axioms comp_dname (eqs : eq list) n (((dname,_),cons) : eq)=
let

(* ----- axioms and definitions concerning the isomorphism ------------------ *)

  val dc_abs = %%(dname^"_abs");
  val dc_rep = %%(dname^"_rep");
  val x_name'= "x";
  val x_name = idx_name eqs x_name' (n+1);
  val dnam = Sign.base_name dname;

 val abs_iso_ax = ("abs_iso" ,mk_trp(dc_rep`(dc_abs`%x_name')=== %x_name'));
 val rep_iso_ax = ("rep_iso" ,mk_trp(dc_abs`(dc_rep`%x_name')=== %x_name'));

  val when_def = ("when_def",%%(dname^"_when") == 
     foldr (uncurry /\ ) (when_funs cons, /\x_name'((when_body cons (fn (x,y) =>
				Bound(1+length cons+x-y)))`(dc_rep`Bound 0))));

  fun con_def outer recu m n (_,args) = let
     fun idxs z x arg = (if is_lazy arg then fn t => %%"up"`t else Id)
			(if recu andalso is_rec arg then (cproj (Bound z) eqs
				  (rec_of arg))`Bound(z-x) else Bound(z-x));
     fun parms [] = %%"ONE"
     |   parms vs = foldr'(fn(x,t)=> %%"spair"`x`t)(mapn (idxs(length vs))1 vs);
     fun inj y 1 _ = y
     |   inj y _ 0 = %%"sinl"`y
     |   inj y i j = %%"sinr"`(inj y (i-1) (j-1));
  in foldr /\# (args, outer (inj (parms args) m n)) end;

  val copy_def = ("copy_def", %%(dname^"_copy") == /\"f" (dc_abs oo 
	foldl (op `) (%%(dname^"_when") , 
	              mapn (con_def Id true (length cons)) 0 cons)));

(* -- definitions concerning the constructors, discriminators and selectors - *)

  val con_defs = mapn (fn n => fn (con,args) => (extern_name con ^"_def",  
  %%con == con_def (fn t => dc_abs`t) false (length cons) n (con,args))) 0 cons;

  val dis_defs = let
	fun ddef (con,_) = (dis_name con ^"_def",%%(dis_name con) == 
		 mk_cfapp(%%(dname^"_when"),map 
			(fn (con',args) => (foldr /\#
			   (args,if con'=con then %%"TT" else %%"FF"))) cons))
	in map ddef cons end;

  val sel_defs = let
	fun sdef con n arg = (sel_of arg^"_def",%%(sel_of arg) == 
		 mk_cfapp(%%(dname^"_when"),map 
			(fn (con',args) => if con'<>con then %%"UU" else
			 foldr /\# (args,Bound (length args - n))) cons));
	in flat(map (fn (con,args) => mapn (sdef con) 1 args) cons) end;


(* ----- axiom and definitions concerning induction ------------------------- *)

  val reach_ax = ("reach", mk_trp(cproj (%%"fix"`%%(comp_dname^"_copy")) eqs n
					`%x_name === %x_name));
  val take_def = ("take_def",%%(dname^"_take") == mk_lam("n",cproj' 
	     (%%"iterate" $ Bound 0 $ %%(comp_dname^"_copy") $ %%"UU") eqs n));
  val finite_def = ("finite_def",%%(dname^"_finite") == mk_lam(x_name,
	mk_ex("n",(%%(dname^"_take") $ Bound 0)`Bound 1 === Bound 1)));

in (dnam,
    [abs_iso_ax, rep_iso_ax, reach_ax],
    [when_def, copy_def] @
     con_defs @ dis_defs @ sel_defs @
    [take_def, finite_def])
end; (* let *)

val add_axioms_i = PureThy.add_axioms_i o map Attribute.none;

in (* local *)

fun add_axioms (comp_dnam, eqs : eq list) thy' = let
  val comp_dname = Sign.full_name (sign_of thy') comp_dnam;
  val dnames = map (fst o fst) eqs;
  val x_name = idx_name dnames "x"; 
  fun copy_app dname = %%(dname^"_copy")`Bound 0;
  val copy_def = ("copy_def" , %%(comp_dname^"_copy") ==
				    /\"f"(foldr' cpair (map copy_app dnames)));
  val bisim_def = ("bisim_def",%%(comp_dname^"_bisim")==mk_lam("R",
    let
      fun one_con (con,args) = let
	val nonrec_args = filter_out is_rec args;
	val    rec_args = filter     is_rec args;
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
	val capps = foldr mk_conj (mapn rel_app 1 rec_args, mk_conj(
	   Bound(allargs_cnt+1)===mk_cfapp(%%con,map (bound_arg allvns) vns1),
	   Bound(allargs_cnt+0)===mk_cfapp(%%con,map (bound_arg allvns) vns2)));
        in foldr mk_ex (allvns, foldr mk_conj 
			      (map (defined o Bound) nonlazy_idxs,capps)) end;
      fun one_comp n (_,cons) =mk_all(x_name(n+1),mk_all(x_name(n+1)^"'",mk_imp(
	 		proj (Bound 2) eqs n $ Bound 1 $ Bound 0,
         		foldr' mk_disj (mk_conj(Bound 1 === UU,Bound 0 === UU)
					::map one_con cons))));
    in foldr' mk_conj (mapn one_comp 0 eqs)end ));
  fun add_one (thy,(dnam,axs,dfs)) = thy 
	|> Theory.add_path dnam
	|> add_axioms_i (infer_types thy' dfs)(*add_defs_i*)
	|> add_axioms_i (infer_types thy' axs)
	|> Theory.parent_path;
  val thy = foldl add_one (thy', mapn (calc_axioms comp_dname eqs) 0 eqs);
in thy |> Theory.add_path comp_dnam  
       |> add_axioms_i (infer_types thy' 
		(bisim_def::(if length eqs>1 then [copy_def] else [])))
       |> Theory.parent_path
end;

end; (* local *)
end; (* struct *)
