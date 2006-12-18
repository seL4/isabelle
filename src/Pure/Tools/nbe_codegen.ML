(*  Title:      Pure/nbe_codegen.ML
    ID:         $Id$
    Author:     Klaus Aehlig, LMU Muenchen; Tobias Nipkow, TU Muenchen

Code generator for "normalization by evaluation".
*)

(* Global asssumptions:
   For each function: there is at least one defining eqns and
   all defining equations have same number of arguments.

FIXME
fun MLname
val quote = quote;

*)

signature NBE_CODEGEN =
sig
  val generate: theory -> (string -> bool) -> (string * thm list) list -> string option;
  val nterm_to_term: theory -> NBE_Eval.nterm -> term;
end


structure NBE_Codegen: NBE_CODEGEN =
struct

val Eval = "NBE_Eval";
val Eval_mk_Fun  = Eval ^ ".mk_Fun";
val Eval_apply   = Eval ^ ".apply";
val Eval_Constr  = Eval ^ ".Constr";
val Eval_C       = Eval ^ ".C";
val Eval_AbsN    = Eval ^ ".AbsN";
val Eval_Fun     = Eval ^ ".Fun";
val Eval_BVar    = Eval ^ ".BVar";
val Eval_new_name = Eval ^ ".new_name";
val Eval_to_term = Eval ^ ".to_term";

fun MLname s = "nbe_" ^ translate_string (fn "." => "_" | c => c) s;
fun MLvname s  = "v_" ^ MLname s;
fun MLparam n  = "p_" ^ string_of_int n;
fun MLintern s = "i_" ^ MLname s;

fun MLparams n = map MLparam (1 upto n);

structure S =
struct

val quote = quote; (* FIXME *)

fun app e1 e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun abs v e = "(fn" ^ v ^ " => " ^ e ^ ")";
fun tup es = "(" ^ commas es ^ ")";
fun list es = "[" ^ commas es ^ "]";

fun apps s ss = Library.foldl (uncurry app) (s, ss);
fun nbe_apps s ss =
  Library.foldr (fn (s,e) => app (app Eval_apply e) s) (ss,s);

fun eqns name ees =
  let fun eqn (es,e) = name ^ " " ^ space_implode " " es ^ " = " ^ e
  in space_implode "\n  | " (map eqn ees) end;

fun eqnss (es :: ess) = prefix "fun " es :: map (prefix "and ") ess
  |> space_implode "\n"
  |> suffix "\n";

fun Val v s = "val " ^ v ^ " = " ^ s;
fun Let ds e = "let\n" ^ (space_implode "\n" ds) ^ " in " ^ e ^ " end"

end

val tab_lookup = S.app "NBE.lookup";
val tab_update = S.app "NBE.update";

fun mk_nbeFUN(nm,e) =
  S.app Eval_Fun (S.tup [S.abs(S.list [MLvname nm])e,S.list [],"1",
      S.abs(S.tup [])(S.Let 
        [S.Val (MLintern "var") (S.app Eval_new_name (S.tup [])),
         S.Val (MLvname nm) (S.app Eval_BVar (S.tup [(MLintern "var"), S.list []]))]
	(S.app Eval_AbsN(S.tup[MLintern "var",(S.app Eval_to_term e)])))]);

fun take_last n xs = rev (Library.take(n, rev xs));
fun drop_last n xs = rev (Library.drop(n, rev xs));

fun selfcall nm ar args =
	if (ar <= length args) then 
	  S.nbe_apps (S.app (MLname nm) (S.list (take_last ar args)))
	             (drop_last ar args)
        else S.app Eval_Fun (S.tup [MLname nm,S.list args,
	           string_of_int(ar - (length args)),
		   S.abs (S.tup []) (S.app Eval_C
	(S.quote nm))]);

fun mk_rexpr defined names ar =
  let
    fun mk args (Const (c, _)) = 
          if member (op =) names c then selfcall c ar args
            else if defined c then S.nbe_apps (MLname c) args
            else S.app Eval_Constr (S.tup [S.quote c, S.list args])
      | mk args (Free (v, _)) = S.nbe_apps (MLvname v) args
      | mk args (t1 $ t2) = mk (args @ [mk [] t2]) t1
      | mk args (Abs (v, _, t)) = S.nbe_apps (mk_nbeFUN (v, mk [] t)) args;
  in mk [] end;

val mk_lexpr =
  let
    fun mk args (Const (c, _)) =
          S.app Eval_Constr (S.tup [S.quote c, S.list args])
      | mk args (Free (v, _)) = if null args then MLvname v else 
          sys_error "NBE mk_lexpr illegal higher order pattern"
      | mk args (t1 $ t2) = mk (args @ [mk [] t2]) t1
      | mk args (Abs _) =
          sys_error "NBE mk_lexpr illegal pattern";
  in mk [] end;

fun lookup nm = S.Val (MLname nm) (tab_lookup (S.quote nm));

fun generate thy defined [(_, [])] = NONE
  | generate thy defined raw_eqnss =
      let
        val eqnss0 = map (fn (name, thms as thm :: _) =>
          (name, ((length o snd o strip_comb o fst o Logic.dest_equals o prop_of) thm,
            map (apfst (snd o strip_comb) o Logic.dest_equals o Logic.unvarify
              o prop_of) thms)))
          raw_eqnss;
        val eqnss = (map o apsnd o apsnd o map) (fn (args, t) =>
          (map (NBE_Eval.prep_term thy) args, NBE_Eval.prep_term thy t)) eqnss0
        val names = map fst eqnss;
        val used_funs =
          []
          |> fold (fold (fold_aterms (fn Const (c, _) => insert (op =) c
                                      | _ => I)) o map snd o snd o snd) eqnss
          |> subtract (op =) names;
        fun mk_def (name, (ar, eqns)) =
          let
            fun mk_eqn (args, t) = ([S.list (map mk_lexpr (rev args))],
              mk_rexpr defined names ar t);
            val default_params = (S.list o rev o MLparams) ar;
            val default_eqn = ([default_params], S.app Eval_Constr (S.tup [S.quote name, default_params]));
          in S.eqns (MLname name) (map mk_eqn eqns @ [default_eqn]) end;
        val globals = map lookup (filter defined used_funs);
        fun register (name, (ar, _)) = tab_update
            (S.app Eval_mk_Fun (S.tup [S.quote name, MLname name, string_of_int ar]))
      in SOME (S.Let (globals @ [S.eqnss (map mk_def eqnss)]) (space_implode "; " (map register eqnss))) end;

open NBE_Eval;

fun nterm_to_term thy t =
  let
    fun to_term bounds (C s) tcount =
          let
            val (c, ty) = (CodegenConsts.typ_of_inst thy o the o CodegenNames.const_rev thy) s;
            val ty' = map_type_tvar (fn ((s,i),S) => TypeInfer.param (tcount + i) (s,S)) ty;
            val tcount' = tcount + maxidx_of_typ ty + 1;
          in (Const (c, ty'), tcount') end
      | to_term bounds (V s) tcount = (Free (s, dummyT), tcount)
      | to_term bounds (B i) tcount = (Bound (find_index (fn j => i = j) bounds), tcount)
      | to_term bounds (A (t1, t2)) tcount =
          tcount
          |> to_term bounds t1
          ||>> to_term bounds t2
          |-> (fn (t1', t2') => pair (t1' $ t2'))
      | to_term bounds (AbsN (i, t)) tcount =
          tcount
          |> to_term (i :: bounds) t
          |-> (fn t' => pair (Abs ("u", dummyT, t')));
  in fst (to_term [] t 0) end;

end;
