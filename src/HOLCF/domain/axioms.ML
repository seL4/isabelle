(* axioms.ML
   ID:         $Id$
   Author : David von Oheimb
   Created: 31-May-95
   Updated: 12-Jun-95 axioms for discriminators, selectors and induction
   Updated: 19-Jun-95 axiom for bisimulation
   Updated: 28-Jul-95 gen_by-section
   Updated: 29-Aug-95 simultaneous domain equations
   Copyright 1995 TU Muenchen
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

(* ----- axioms and definitions concerning the isomorphism ------------------------ *)

  val dc_abs = %%(dname^"_abs");
  val dc_rep = %%(dname^"_rep");
  val x_name'= "x";
  val x_name = idx_name eqs x_name' (n+1);

  val ax_abs_iso = (dname^"_abs_iso",mk_trp(dc_rep`(dc_abs`%x_name') === %x_name'));
  val ax_rep_iso = (dname^"_rep_iso",mk_trp(dc_abs`(dc_rep`%x_name') === %x_name'));

  val ax_when_def = (dname^"_when_def",%%(dname^"_when") == 
           foldr (uncurry /\ ) (when_funs cons, /\x_name'((when_body cons (fn (x,y) =>
                                Bound(1+length cons+x-y)))`(dc_rep`Bound 0))));

  val ax_copy_def = let
    fun simp_oo (Const ("fapp", _) $ (Const ("fapp", _) $ 
                 Const ("cfcomp", _) $ fc) $ Const ("ID", _)) = fc
    |   simp_oo t = t;
    fun simp_app (Const ("fapp", _) $ Const ("ID", _) $ t) = t
    |   simp_app t = t;
        fun mk_arg m n arg  = (if is_lazy arg 
                               then fn t => %%"lift"`(simp_oo (%%"up" oo t)) else Id)
                              (if_rec arg (cproj (Bound (2*min[n,m])) eqs) (%%"ID"));
        fun mk_prod (t1,t2)  = %%"ssplit"`(/\ "x" (/\ "y" (%%"spair"`
                                         simp_app(t1`Bound 1)`simp_app(t2`Bound 0))));
        fun one_con (_,args) = if args = [] then %%"ID" else
                               foldr' mk_prod (mapn (mk_arg (length args-1)) 1 args);
        fun mk_sum  (t1,t2)  = %%"sswhen"`(simp_oo (%%"sinl" oo t1))
                                         `(simp_oo (%%"sinr" oo t2));
        in (dname^"_copy_def", %%(dname^"_copy") == /\"f" 
                          (dc_abs oo foldr' mk_sum (map one_con cons) oo dc_rep)) end;

(* ----- definitions concerning the constructors, discriminators and selectors ---- *)

  val axs_con_def = let
        fun idxs z x arg = (if is_lazy arg then fn x => %%"up"`x else Id)(Bound(z-x));
        fun prms [] = %%"one"
        |   prms vs = foldr' (fn(x,t)=> %%"spair"`x`t) (mapn (idxs (length vs)) 1 vs);
        val injs    = bin_branchr (fn l=> l@["l"]) (fn l=> l@["r"]);
        fun cdef ((con,args),injs) = (extern_name con ^"_def",%%con == 
                 foldr /\# (args,dc_abs`
                (foldr (fn (i,t) => %%("sin"^i)`t ) (injs, prms args))));
        in map cdef (cons~~(mapn (fn n => K(injs [] cons n)) 0 cons)) end;

  val axs_dis_def = let
        fun ddef (con,_) = (dis_name con ^"_def",%%(dis_name con) == 
                 mk_cfapp(%%(dname^"_when"),map 
                        (fn (con',args) => (foldr /\#
                           (args,if con'=con then %%"TT" else %%"FF"))) cons))
        in map ddef cons end;

  val axs_sel_def = let
        fun sdef con n arg = (sel_of arg^"_def",%%(sel_of arg) == 
                 mk_cfapp(%%(dname^"_when"),map 
                        (fn (con',args) => if con'<>con then %%"UU" else
                         foldr /\# (args,Bound (length args - n))) cons));
        in flat(map (fn (con,args) => mapn (sdef con) 1 args) cons) end;


(* ----- axiom and definitions concerning induction ------------------------------- *)

  fun cproj' T = cproj T eqs n;
  val ax_reach    = (dname^"_reach"   , mk_trp(cproj'(%%"fix"`%%(comp_dname^"_copy"))
                                        `%x_name === %x_name));
  val ax_take_def = (dname^"_take_def",%%(dname^"_take") == mk_lam("n",
                    cproj'(%%"iterate" $ Bound 0 $ %%(comp_dname^"_copy") $ %%"UU")));
  val ax_finite_def = (dname^"_finite_def",%%(dname^"_finite") == mk_lam(x_name,
        mk_ex("n",(%%(dname^"_take") $ Bound 0)`Bound 1 === Bound 1)));

in [ax_abs_iso, ax_rep_iso, ax_when_def, ax_copy_def] @
    axs_con_def @ axs_dis_def @ axs_sel_def @
   [ax_reach, ax_take_def, ax_finite_def] end;


in (* local *)

fun add_axioms (comp_dname, eqs : eq list) thy' =let
  val dnames = map (fst o fst) eqs;
  val x_name = idx_name dnames "x"; 
  fun copy_app dname = %%(dname^"_copy")`Bound 0;
  val ax_copy_def  = (comp_dname^"_copy_def" , %%(comp_dname^"_copy") ==
                                           /\"f"(foldr' cpair (map copy_app dnames)));
  val ax_bisim_def = (comp_dname^"_bisim_def",%%(comp_dname^"_bisim") == mk_lam("R",
    let
      fun one_con (con,args) = let
        val nonrec_args = filter_out is_rec args;
        val    rec_args = filter     is_rec args;
        val nonrecs_cnt = length nonrec_args;
        val    recs_cnt = length    rec_args;
        val allargs     = nonrec_args @ rec_args
                                      @ map (upd_vname (fn s=> s^"'")) rec_args;
        val allvns      = map vname allargs;
        fun vname_arg s arg = if is_rec arg then vname arg^s else vname arg;
        val vns1        = map (vname_arg "" ) args;
        val vns2        = map (vname_arg "'") args;
        val allargs_cnt = nonrecs_cnt + 2*recs_cnt;
        val rec_idxs    = (recs_cnt-1) downto 0;
        val nonlazy_idxs = map snd (filter_out (fn (arg,_) => is_lazy arg)
                                           (allargs~~((allargs_cnt-1) downto 0)));
        fun rel_app i ra = proj (Bound(allargs_cnt+2)) dnames (rec_of ra) $ 
                           Bound (2*recs_cnt-i) $ Bound (recs_cnt-i);
        val capps = foldr mk_conj (mapn rel_app 1 rec_args,
         mk_conj(Bound(allargs_cnt+1)===mk_cfapp(%%con,map (bound_arg allvns) vns1),
                 Bound(allargs_cnt+0)===mk_cfapp(%%con,map (bound_arg allvns) vns2)));
        in foldr mk_ex (allvns, foldr mk_conj 
                                      (map (defined o Bound) nonlazy_idxs,capps)) end;
      fun one_comp n (_,cons) = mk_all(x_name (n+1), mk_all(x_name (n+1)^"'", mk_imp(
                        proj (Bound 2) dnames n $ Bound 1 $ Bound 0,
         foldr' mk_disj (mk_conj(Bound 1 === UU,Bound 0 === UU)::map one_con cons))));
    in foldr' mk_conj (mapn one_comp 0 eqs)end ));
  val thy_axs = flat (mapn (calc_axioms comp_dname eqs) 0 eqs) @
                (if length eqs>1 then [ax_copy_def] else []) @ [ax_bisim_def];
in thy' |> add_axioms_i (infer_types thy' thy_axs) end;


fun add_gen_by ((tname,finite),(typs,cnstrs)) thy' = let
  fun pred_name typ ="P"^(if typs=[typ] then "" else string_of_int(1+find(typ,typs)));
  fun lift_adm t = lift (fn typ => %%"adm" $ %(pred_name typ)) 
                        (if finite then [] else typs,t);
  fun lift_pred_UU t = lift (fn typ => %(pred_name typ) $ UU) (typs,t);
  fun one_cnstr (cnstr,vns,(args,res)) = let 
                        val rec_args = filter (fn (_,typ) => typ mem typs)(vns~~args);
                        val app = mk_cfapp(%%cnstr,map (bound_arg vns) vns);
                     in foldr mk_All (vns,
                         lift (fn (vn,typ) => %(pred_name typ) $ bound_arg vns vn)
                              (rec_args,defined app ==> %(pred_name res)$app)) end;
  fun one_conc typ = let val pn = pred_name typ in
                     %pn $ %("x"^implode(tl(explode pn))) end;
  val concl = mk_trp(foldr' mk_conj (map one_conc typs));
  val induct =(tname^"_induct",lift_adm(lift_pred_UU(
                        foldr (op ===>) (map one_cnstr cnstrs,concl))));
in thy' |> add_axioms_i (infer_types thy' [induct]) end;

end; (* local *)
end; (* struct *)
