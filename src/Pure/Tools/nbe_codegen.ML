(*  ID:         $Id$
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
  val generate: (string -> bool) -> string * CodegenThingol.def -> string;
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
  in "fun " ^ space_implode "\n  | " (map eqn ees) ^ ";\n" end;


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

open BasicCodegenThingol;

fun mk_rexpr defined nm ar =
  let
    fun mk args = CodegenThingol.map_pure (mk' args)
    and mk' args (IConst (c, _)) =
          if c = nm then selfcall nm ar args
          else if defined c then S.nbe_apps (MLname c) args
          else S.app Eval_Constr (S.tup [S.quote c, S.list args])
      | mk' args (IVar s) = S.nbe_apps (MLvname s) args
      | mk' args (e1 `$ e2) = mk (args @ [mk [] e2]) e1
      | mk' args ((nm, _) `|-> e) = S.nbe_apps (mk_nbeFUN (nm, mk [] e)) args;
  in mk [] end;

val mk_lexpr =
  let
    fun mk args = CodegenThingol.map_pure (mk' args)
    and mk' args (IConst (c, _)) =
          S.app Eval_Constr (S.tup [S.quote c, S.list args])
      | mk' args (IVar s) = if args = [] then MLvname s else 
          sys_error "NBE mk_lexpr illegal higher order pattern"
      | mk' args (e1 `$ e2) = mk (args @ [mk [] e2]) e1
      | mk' args (_ `|-> _) =
          sys_error "NBE mk_lexpr illegal pattern";
  in mk [] end;

fun mk_eqn defined nm ar (lhs,e) =
  if has_duplicates (op =) (fold CodegenThingol.add_varnames lhs []) then [] else
  [([S.list(map mk_lexpr (rev lhs))], mk_rexpr defined nm ar e)];

fun lookup nm = S.Val (MLname nm) (tab_lookup (S.quote nm));

fun generate defined (nm, CodegenThingol.Fun (eqns, _)) =
      let
        val ar = (length o fst o hd) eqns;
        val params = (S.list o rev o MLparams) ar;
        val funs =
          []
          |> fold (fn (_, e) => CodegenThingol.add_constnames e) eqns
          |> remove (op =) nm;
        val globals = map lookup (filter defined funs);
        val default_eqn = ([params], S.app Eval_Constr (S.tup[S.quote nm,params]));
        val code = S.eqns (MLname nm)
                          (Library.flat(map (mk_eqn defined nm ar) eqns) 
                           @ [default_eqn])
        val register = tab_update
            (S.app Eval_mk_Fun (S.tup[S.quote nm, MLname nm, string_of_int ar]))
      in
        S.Let (globals @ [code]) register
      end
  | generate _ _ = "";

open NBE_Eval;

fun nterm_to_term thy t =
  let
    fun consts_of (C s) = insert (op =) s
      | consts_of (V _) = I
      | consts_of (B _) = I
      | consts_of (A (t1, t2)) = consts_of t1 #> consts_of t2
      | consts_of (AbsN (_, t)) = consts_of t;
    val consts = consts_of t [];
    val the_const = the o AList.lookup (op =)
      (consts ~~ CodegenPackage.consts_of_idfs thy consts);
    fun to_term bounds (C s) = Const (the_const s)
      | to_term bounds (V s) = Free (s, dummyT)
      | to_term bounds (B i) = Bound (find_index (fn j => i = j) bounds)
      | to_term bounds (A (t1, t2)) = to_term bounds t1 $ to_term bounds t2
      | to_term bounds (AbsN (i, t)) =
          Abs("u", dummyT, to_term (i::bounds) t);
  in to_term [] t end;

end;
