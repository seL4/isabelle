(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Carsten Clasohm
    Copyright   1995 TU Muenchen
*)

signature THMDB =
sig
  type thm_db_type

  val thm_db: thm_db_type
  val store_thm_db: string * thm -> thm
  val thms_containing: string list -> (string * thm) list
(*val thms_resolving_with: term * Sign.sg -> (string * thm) list*)
end;


functor ThmdbFUN(val ignore: string list): THMDB =
               (*ignore: constants that must not be used for theorem indexing*)
struct

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
fun store_thm_db (named_thm as (name, t)) =
  let val {prop, hyps, ...} = rep_thm t;

      val consts = distinct (flat (map list_consts (prop :: hyps)));

      val (num, db) = !thm_db;

      val tagged_thm = (num + 1, named_thm);

      fun update_db [] result = result
        | update_db (c :: cs) result =
            let val old_thms = Symtab.lookup_multi (result, c);
            in update_db cs (Symtab.update ((c, tagged_thm :: old_thms),
                                            result))
            end;
  in if consts = [] then writeln ("Warning: Theorem " ^ name ^
                                  " cannot be stored in ThmDB\n\t because it \
                                  \contains no or only ignored constants.")
                    else ();
     thm_db := (num+1, update_db consts db);
     t
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

(*This will probably be changed or removed:
(*get all theorems which can be unified with term t*)
fun thms_unifying_with(t:term, signt:Sign.sg, thms:(string*thm) list) =
  let val maxt = maxidx_of_term t
      fun select((named_thm as (name,thm))::thms,sels) =
            let val {prop,maxidx,sign,...} = rep_thm thm
                val u = Logic.incr_indexes([],maxidx+1) t
                val env = Envir.empty(max[maxt,maxidx]+1)
                val seq = Unify.unifiers(sign,env,[(u,prop)])
            in select(thms,
                 if Sign.subsig(signt,sign)
                 then case Sequence.pull(seq) of
                        None => sels
                      | Some _ => named_thm::sels
                 else sels)
            end
        | select([],sels) = sels
  in select(thms,[]) end;

(*get all theorems which resolve to a given term*)
fun thms_resolving_with (t, sg) =
  let val thms = thms_containing (list_consts t);
  in thms_unifying_with (t, sg, thms) end;
*)
end;
