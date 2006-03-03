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
  let fun mk args t = case t of
    IConst((s,_),_) => 
    if s=nm then selfcall nm ar args
    else if defined s then S.nbe_apps (MLname s) args
    else S.app Eval_Constr (S.tup [S.quote s,S.list args ])
  | IVar s => S.nbe_apps (MLvname s) args
  | e1 `$ e2 => mk (args @ [mk [] e2]) e1
  | (nm, _) `|-> e =>
      S.nbe_apps (mk_nbeFUN(nm, mk [] e)) args
  | IAbs (_, e) => mk args e
  | ICase (_, e) => mk args e
  | _ => sys_error "NBE mkexpr"
  in mk [] end;

val mk_lexpr =
  let fun mk args t = case t of
    IConst((s,_),_) =>
      S.app Eval_Constr (S.tup [S.quote s, S.list args])
  | IVar s => if args = [] then MLvname s else 
      sys_error "NBE mk_lexpr illegal higher order pattern"
  | e1 `$ e2 => mk (args @ [mk [] e2]) e1
  | IAbs (_, e) => mk args e
  | ICase (_, e) => mk args e
  | _ => sys_error "NBE mk_lexpr illegal pattern"
  in mk [] end;

fun mk_eqn defined nm ar (lhs,e) =
  ([S.list(map mk_lexpr (rev lhs))], mk_rexpr defined nm ar e);

fun consts_of (IConst ((s, _), _)) = insert (op =) s
  | consts_of (e1 `$ e2) =
      consts_of e1 #> consts_of e2
  | consts_of (_ `|-> e) = consts_of e
  | consts_of (IAbs (_, e)) = consts_of e
  | consts_of (ICase (_, e)) = consts_of e
  | consts_of _ = I;

fun lookup nm = S.Val (MLname nm) (tab_lookup (S.quote nm));

fun generate defined (nm, CodegenThingol.Fun (eqns, _)) =
      let
        val ar = length(fst(hd eqns));
        val params = S.list (rev (MLparams ar));
        val funs = Library.flat(map (fn (_,e) => consts_of e []) eqns) \ nm;
        val globals = map lookup (filter defined funs);
        val default_eqn = ([params], S.app Eval_Constr (S.tup[S.quote nm,params]));
        val code = S.eqns (MLname nm)
                          (map (mk_eqn defined nm ar) eqns @ [default_eqn])
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
    val the_const = AList.lookup (op =)
      (consts ~~ CodegenPackage.consts_of_idfs thy consts)
      #> the_default ("", dummyT);
    fun to_term bounds (C s) = Const (the_const s)
      | to_term bounds (V s) = Free (s, dummyT)
      | to_term bounds (B i) = Bound (find_index (fn j => i = j) bounds)
      | to_term bounds (A (t1, t2)) = to_term bounds t1 $ to_term bounds t2
      | to_term bounds (AbsN (i, t)) =
          Abs("u", dummyT, to_term (i::bounds) t);
  in to_term [] t end;

end;

(*

val use_show = fn s => (writeln ("\n---generated code:\n"^ s);
     use_text(writeln o enclose "\n---compiler echo:\n" "\n---\n",
              writeln o enclose "\n--- compiler echo (with error!):\n" 
                                "\n---\n")
      true s);

val dummyIT = CodegenThingol.IType("DUMMY",[]);

use_show(NBE_Codegen.generate (the_context()) ("append",CodegenThingol.Fun(
  [([CodegenThingol.IConst(("Nil",dummyIT),[]),
     CodegenThingol.IVarE("ys",dummyIT)],
    CodegenThingol.IVarE("ys",dummyIT)),
   ([CodegenThingol.IApp(
       CodegenThingol.IApp(
         CodegenThingol.IConst(("Cons",dummyIT),[]),
         CodegenThingol.IVarE("x",dummyIT)),
       CodegenThingol.IVarE("xs",dummyIT)),
     CodegenThingol.IVarE("ys",dummyIT)],
    CodegenThingol.IApp(
       CodegenThingol.IApp(
         CodegenThingol.IConst(("Cons",dummyIT),[]),
         CodegenThingol.IVarE("x",dummyIT)),
       CodegenThingol.IApp(
         CodegenThingol.IApp(
           CodegenThingol.IConst(("append",dummyIT),[]),
           CodegenThingol.IVarE("xs",dummyIT)),
         CodegenThingol.IVarE("ys",dummyIT))))]
  ,([],dummyIT))));


let
fun test a b = if a=b then () else error "oops!";

val CNil = Const("Nil",dummyT);
val CCons = Const("Cons",dummyT);
val Cappend = Const("append",dummyT);
val Fx = Free("x",dummyT);
val Fy = Free("y",dummyT);
val Fxs = Free("xs",dummyT);
val Fys = Free("ys",dummyT);
open NBE_Eval
in
test (nbe(CNil)) (C "Nil");
test (nbe(CCons)) (C "Cons");
test (nbe(Cappend)) (C "append");
test (nbe(Cappend $ CNil $ CNil)) (C "Nil");
test (nbe(Cappend $ Fxs)) (A (C "append", V "xs"));
test (nbe(Cappend $ Fxs $ Fys)) (A (A (C "append", V "xs"), V "ys"));
test (nbe(Cappend $ CNil $ Fxs)) (V "xs");
test (nbe(Cappend $ (CCons $ Fx $ Fxs) $ Fys))
     (A (A (C "Cons", V "x"), A (A (C "append", V "xs"), V "ys")));
test (nbe(Cappend $ (CCons $ Fx $ Fxs) $ (CCons $ Fy $ Fys)))
     (A (A (C "Cons", V "x"), A (A (C "append", V "xs"), A (A (C "Cons", V "y"), V "ys"))));
test (nbe(Cappend $ (CCons $ Fx $ (CCons $ Fy $ Fxs)) $ (CCons$Fy$Fys)))
 (A
      (A (C "Cons", V "x"),
         A
            (A (C "Cons", V "y"),
               A (A (C "append", V "xs"), A (A (C "Cons", V "y"), V "ys")))))

end;


use_show(NBE_Codegen.generate (the_context()) ("app",CodegenThingol.Fun(
  [
  ([CodegenThingol.IConst(("Nil",dummyIT),[])],
    CodegenThingol.IAbs(CodegenThingol.IVarE("ys",dummyIT),
                        CodegenThingol.IVarE("ys",dummyIT))),

   ([CodegenThingol.IApp(
       CodegenThingol.IApp(
         CodegenThingol.IConst(("Cons",dummyIT),[]),
         CodegenThingol.IVarE("x",dummyIT)),
       CodegenThingol.IVarE("xs",dummyIT))],
    CodegenThingol.IAbs(CodegenThingol.IVarE("ys",dummyIT),
    CodegenThingol.IApp(
       CodegenThingol.IApp(
         CodegenThingol.IConst(("Cons",dummyIT),[]),
         CodegenThingol.IVarE("x",dummyIT)),
       CodegenThingol.IApp(
         CodegenThingol.IApp(
           CodegenThingol.IConst(("app",dummyIT),[]),
           CodegenThingol.IVarE("xs",dummyIT)),
         CodegenThingol.IVarE("ys",dummyIT)))))]
  ,([],dummyIT))));


let
fun test a b = if a=b then () else error "oops!";

val CNil = Const("Nil",dummyT);
val CCons = Const("Cons",dummyT);
val Cappend = Const("app",dummyT);
val Fx = Free("x",dummyT);
val Fy = Free("y",dummyT);
val Fxs = Free("xs",dummyT);
val Fys = Free("ys",dummyT);
open NBE_Eval
in
test (nbe(CNil)) (C "Nil");
test (nbe(CCons)) (C "Cons");
test (nbe(Cappend)) (C "app");
test (nbe(Cappend $ CNil)) (AbsN (1, B 1));
test (nbe(Cappend $ CNil $ CNil)) (C "Nil");
test (nbe(Cappend $ Fxs)) (A (C "app", V "xs"));
test (nbe(Cappend $ Fxs $ Fys)) (A (A (C "app", V "xs"), V "ys"));
test (nbe(Cappend $ CNil $ Fxs)) (V "xs");
test (nbe(Cappend $ (CCons $ Fx $ Fxs) $ Fys))
     (A (A (C "Cons", V "x"), A (A (C "app", V "xs"), V "ys")));
test (nbe(Cappend $ (CCons $ Fx $ Fxs))) 
   (AbsN (1, A (A (C "Cons", V "x"), A (A (C "app", V "xs"), B 1))));
test (nbe(Cappend $ (CCons $ Fx $ Fxs) $ (CCons $ Fy $ Fys)))
     (A (A (C "Cons", V "x"), A (A (C "app", V "xs"), A (A (C "Cons", V "y"), V "ys"))));
test (nbe(Cappend $ (CCons $ Fx $ (CCons $ Fy $ Fxs)) $ (CCons$Fy$Fys)))
 (A
      (A (C "Cons", V "x"),
         A
            (A (C "Cons", V "y"),
               A (A (C "app", V "xs"), A (A (C "Cons", V "y"), V "ys")))));
()
end;


use_show(NBE_Codegen.generate (the_context()) ("add",CodegenThingol.Fun(
  [
  ([CodegenThingol.IConst(("0",dummyIT),[])],
    CodegenThingol.IAbs(CodegenThingol.IVarE("n",dummyIT),
                        CodegenThingol.IVarE("n",dummyIT))),
   ([CodegenThingol.IApp(
       CodegenThingol.IConst(("S",dummyIT),[]),
       CodegenThingol.IVarE("n",dummyIT))],
    CodegenThingol.IAbs(CodegenThingol.IVarE("m",dummyIT),
      CodegenThingol.IApp(
         CodegenThingol.IConst(("S",dummyIT),[]),
           CodegenThingol.IApp(
             CodegenThingol.IApp(
               CodegenThingol.IConst(("add",dummyIT),[]),
               CodegenThingol.IVarE("n",dummyIT)),
             CodegenThingol.IVarE("m",dummyIT)))))]
  ,([],dummyIT))));


let
fun test a b = if a=b then () else error "oops!";

val C0 = Const("0",dummyT);
val CS = Const("S",dummyT);
val Cadd = Const("add",dummyT);
val Fx = Free("x",dummyT);
val Fy = Free("y",dummyT);
open NBE_Eval
in
test (nbe(Cadd $ C0)) (AbsN (1, B 1));
test (nbe(Cadd $ C0 $ C0)) (C "0");
test (nbe(Cadd $ (CS $ (CS $ (CS $ Fx))) $ (CS $ (CS $ (CS $ Fy)))))
(A (C "S", A (C "S", A (C "S", A (A (C "add", V "x"), A (C "S", A (C "S", A (C "S", V "y")))))))
)
end;



use_show(NBE_Codegen.generate (the_context()) ("mul",CodegenThingol.Fun(
  [
  ([CodegenThingol.IConst(("0",dummyIT),[])],
    CodegenThingol.IAbs(CodegenThingol.IVarE("n",dummyIT),
                        CodegenThingol.IConst(("0",dummyIT),[]))),
   ([CodegenThingol.IApp(
       CodegenThingol.IConst(("S",dummyIT),[]),
       CodegenThingol.IVarE("n",dummyIT))],
    CodegenThingol.IAbs(CodegenThingol.IVarE("m",dummyIT),
      CodegenThingol.IApp(
       CodegenThingol.IApp(
         CodegenThingol.IConst(("add",dummyIT),[]),
        CodegenThingol.IVarE("m",dummyIT)),
           CodegenThingol.IApp(
             CodegenThingol.IApp(
               CodegenThingol.IConst(("mul",dummyIT),[]),
               CodegenThingol.IVarE("n",dummyIT)),
             CodegenThingol.IVarE("m",dummyIT)))))]
  ,([],dummyIT))));


let
fun test a b = if a=b then () else error "oops!";

val C0 = Const("0",dummyT);
val CS = Const("S",dummyT);
val Cmul = Const("mul",dummyT);
val Fx = Free("x",dummyT);
val Fy = Free("y",dummyT);
open NBE_Eval
in
test (nbe(Cmul $ C0)) (AbsN (1, C "0"));
test (nbe(Cmul $ C0 $ Fx)) (C "0");
test (nbe(Cmul $ (CS $ (CS $ (CS $ C0)))))
(AbsN (1, A (A (C "add", B 1), A (A (C "add", B 1), A (A (C "add", B 1), C "0")))));
test (nbe(Cmul $ (CS $ (CS $ (CS $ Fx)))))
 (AbsN (1, A (A (C "add", B 1), A (A (C "add", B 1),
                     A (A (C "add", B 1), A (A (C "mul", V "x"), B 1))))));
test (nbe(Cmul $ (CS $ (CS $ Fx)) $ (CS $ (CS $ (CS $ Fy)))))
(A (C "S", A(C "S",A(C "S",A(A (C "add", V "y"),A(C "S",A(C "S",A(C "S",A
 (A (C "add", V "y"),A(A (C "mul", V "x"),A(C "S",A(C "S",A(C "S", V"y")))))))))))));
()
end;
*)
