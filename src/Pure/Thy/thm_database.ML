(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Tobias Nipkow
    Copyright   1995 TU Muenchen
*)

signature THMDB =
sig
  type thm_db_type

  val thm_db: thm_db_type
  val store_thm_db: string * thm -> thm
  val thms_containing: string list -> (string * thm) list
  val findI:         int -> (string * thm)list
  val findEs:        int -> (string * thm)list
  val findE:  int -> int -> (string * thm)list
end;

functor ThmDBFun(): THMDB =
struct

(*** ignore and top_const could be turned into functor-parameters, but are
currently identical for all object logics ***)

(* Constants not to be used for theorem indexing *)
val ignore = ["Trueprop", "all", "==>", "=="];

(* top_const: main constant, ignoring Trueprop *)
fun top_const (_ $ t) = (case head_of t of Const(c,_) => Some c
                                         | _          => None);

type thm_db_type = (int * ((int * (string * thm)) list) Symtab.table) ref;

(*Symtab which associates a constant with a list of theorems that contain the
  constant (theorems are represented as numbers)*)
val thm_db = ref (0,
           (Symtab.make ([] : (string * ((int * (string * thm)) list)) list)));
                      (*number of next theorem and symtab containing theorems*)

(*list all relevant constants a term contains*)
fun list_consts t =
  let fun consts (Const (c, _)) = if c mem ignore then [] else [c]
        | consts (Free _) = []
        | consts (Var _) = []
        | consts (Bound _) = []
        | consts (Abs (_, _, t)) = consts t
        | consts (t1$t2) = (consts t1) union (consts t2);
  in distinct (consts t) end;

(*store a theorem in database*)
fun store_thm_db (named_thm as (name, thm)) =
  let val {prop, hyps, ...} = rep_thm thm;

      val consts = distinct (flat (map list_consts (prop :: hyps)));

      val (num, db) = !thm_db;

      val tagged_thm = (num + 1, named_thm);

      fun update_db _ [] result = result
        | update_db warned (c :: cs) result =
            let
              val old_thms = Symtab.lookup_multi (result, c);

              val warned' =
                case find_first (fn (_, (n, _)) => n = name) old_thms of
                    Some (_, (_, t)) =>
                      if eq_thm (t, thm) then
                        (if not warned then
                           writeln ("Warning: Theorem database already \
                                    \contains copy of theorem " ^ quote name)
                         else ();
                         true)
                     else error ("Duplicate theorem name " ^ quote name
                                 ^ " used in theorem database")
                 | None => warned;
            in update_db warned' cs
                 (if warned' then result
                  else (Symtab.update ((c, tagged_thm :: old_thms), result)))
            end;
  in if consts = [] then writeln ("Warning: Theorem " ^ name ^
                                  " cannot be stored in ThmDB\n\t because it \
                                  \contains no or only ignored constants.")
                    else ();
     thm_db := (num+1, update_db false consts db);
     thm
  end;

(*intersection of two descending theorem lists*)
infix desc_inter;
fun ([] : (int*'a) list) desc_inter (ys : (int*'a) list) = []
  | xs desc_inter [] = []
  | (xss as ((x as (xi,_)) :: xs)) desc_inter (yss as ((yi,_) :: ys)) =
      if xi = yi then x :: (xs desc_inter ys)
      else if xi > yi then xs desc_inter yss
      else xss desc_inter ys;

(*get all theorems from database that contain a list of constants*)
fun thms_containing constants =
  let fun collect [] _ result = map snd result
        | collect (c :: cs) first result =
            let val new_thms = Symtab.lookup_multi (snd (!thm_db), c);
            in collect cs false (if first then new_thms
                                          else (result desc_inter new_thms))
            end;

      val look_for = constants \\ ignore;
  in if null look_for then
       error ("No or only ignored constants were specified for theorem \
              \database search:\n  " ^ commas (map quote ignore))
     else ();
     collect look_for true [] end;

val intro_const = top_const o concl_of;

fun elim_const thm = case prems_of thm of [] => None | p::_ => top_const(p);

(* In case faster access is necessary, the thm db should provide special
functions

index_intros, index_elims: string -> (string * thm) list

where thm [| A1 ; ...; An |] ==> B is returned by
- index_intros c if B  is of the form c t1 ... tn
- index_elims c  if A1 is of the form c t1 ... tn
*)

(* could be provided by thm db *)
fun index_intros c =
  let fun topc(_,thm) = intro_const thm = Some(c);
      val named_thms = thms_containing [c]
  in filter topc named_thms end;

(* could be provided by thm db *)
fun index_elims c =
  let fun topc(_,thm) = elim_const thm = Some(c);
      val named_thms = thms_containing [c]
  in filter topc named_thms end;

(*assume that parameters have unique names*)
fun goal_params i =
  let val gi = getgoal i
      val frees = map Free (Logic.strip_params gi)
  in (gi,frees) end;

fun concl_of_goal i =
  let val (gi,frees) = goal_params i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(frees,B) end;

fun prems_of_goal i =
  let val (gi,frees) = goal_params i
      val As = Logic.strip_assums_hyp gi
  in map (fn A => subst_bounds(frees,A)) As end;

fun select_match(obj,signobj,named_thms,extract) =
  let fun matches(prop,tsig) =
            case extract prop of
              None => false
            | Some pat => Pattern.matches tsig (pat,obj);

      fun select((p as (_,thm))::named_thms,sels) =
            let val {prop,sign,...} = rep_thm thm
            in select(named_thms,
                      if Sign.subsig(sign,signobj) andalso
                         matches(prop,#tsig(Sign.rep_sg signobj))
                      then p::sels else sels)
            end
        | select([],sels) = sels

  in select(named_thms,[]) end;

fun find_matching(prop,sign,index,extract) =
  (case top_const prop of
     Some c => select_match(prop,sign,index c,extract)
   | _      => []);

fun find_intros(prop,sign) =
  find_matching(prop,sign,index_intros,Some o Logic.strip_imp_concl);

fun find_elims sign prop =
  let fun major prop = case Logic.strip_imp_prems prop of
                         [] => None | p::_ => Some p
  in find_matching(prop,sign,index_elims,major) end;

fun findI i = find_intros(concl_of_goal i,#sign(rep_thm(topthm())));

fun findEs i =
  let fun eq_nth((n1,th1),(n2,th2)) = n1=n2 andalso eq_thm(th1,th2);
      val sign = #sign(rep_thm(topthm()))
      val thmss = map (find_elims sign) (prems_of_goal i)
  in foldl (gen_union eq_nth) ([],thmss) end;

fun findE i j =
  let val sign = #sign(rep_thm(topthm()))
  in find_elims sign (nth_elem(j-1, prems_of_goal i)) end;

end;
