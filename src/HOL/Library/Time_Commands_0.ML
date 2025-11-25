signature ZERO_FUNCS =
sig

val is_zero : theory -> string * typ -> bool

end

structure Zero_Funcs : ZERO_FUNCS =
struct

fun get_constrs thy (Type (n, _)) = these (Ctr_Sugar.ctr_sugar_of_global thy n |> Option.map #ctrs)
  | get_constrs _ _ = []
(* returns if something is a constructor (found in smt_normalize.ML) *)
fun is_constr thy (n, T) =
    let fun match (Const (m, U)) = m = n andalso Sign.typ_instance thy (T, U)
          | match _ = error "Internal error: unknown constructor"
    in can (the o find_first match o get_constrs thy o Term.body_type) T end


structure ZeroFuns = Theory_Data(
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (K true));

fun add_zero f = ZeroFuns.map (Symtab.insert_set f);
fun is_zero_decl lthy f = Option.isSome ((Symtab.lookup o ZeroFuns.get) lthy f);
(* Zero should be everything which is a constructor or something like a constant or variable *)
fun is_zero ctxt (n, (T as Type (Tn,_))) = (Tn <> "fun" orelse is_constr ctxt (n, T) orelse is_zero_decl ctxt n)
  | is_zero _ _  = false

fun save func thy =
let
val fterm = Syntax.read_term (Proof_Context.init_global thy) func;
val name = (case fterm of Const (n,_) => n | _ => raise Fail "Invalid function")
val _ = writeln ("Adding \"" ^ name ^ "\" to 0 functions")
in add_zero name thy
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>time_fun_0\<close> "ML setup for global theory"
    (Parse.prop >> (Toplevel.theory o save));

end