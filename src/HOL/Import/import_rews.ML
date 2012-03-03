(*  Title:      HOL/Import/import_rews.ML
    Author:     Sebastian Skalberg (TU Muenchen)
*)

structure StringPair = Table(type key = string * string val ord = prod_ord string_ord string_ord);

type holthm = (term * term) list * thm

datatype ImportStatus =
         NoImport
       | Generating of string
       | Replaying of string

structure HOL4DefThy = Theory_Data
(
  type T = ImportStatus
  val empty = NoImport
  val extend = I
  fun merge (NoImport, NoImport) = NoImport
    | merge _ = (warning "Import status set during merge"; NoImport)
)

structure ImportSegment = Theory_Data
(
  type T = string
  val empty = ""
  val extend = I
  fun merge ("",arg) = arg
    | merge (arg,"") = arg
    | merge (s1,s2) =
      if s1 = s2
      then s1
      else error "Trying to merge two different import segments"
)

val get_import_segment = ImportSegment.get
val set_import_segment = ImportSegment.put

structure HOL4UNames = Theory_Data
(
  type T = string list
  val empty = []
  val extend = I
  fun merge ([], []) = []
    | merge _ = error "Used names not empty during merge"
)

structure HOL4Dump = Theory_Data
(
  type T = string * string * string list
  val empty = ("","",[])
  val extend = I
  fun merge (("","",[]),("","",[])) = ("","",[])
    | merge _ = error "Dump data not empty during merge"
)

structure HOL4Moves = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

structure HOL4Imports = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun get_segment2 thyname thy =
  Symtab.lookup (HOL4Imports.get thy) thyname

fun set_segment thyname segname thy =
    let
        val imps = HOL4Imports.get thy
        val imps' = Symtab.update_new (thyname,segname) imps
    in
        HOL4Imports.put imps' thy
    end

structure HOL4CMoves = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

structure HOL4Maps = Theory_Data
(
  type T = string option StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4Thms = Theory_Data
(
  type T = holthm StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4ConstMaps = Theory_Data
(
  type T = (bool * string * typ option) StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4Rename = Theory_Data
(
  type T = string StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4DefMaps = Theory_Data
(
  type T = string StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4TypeMaps = Theory_Data
(
  type T = (bool * string) StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4Pending = Theory_Data
(
  type T = ((term * term) list * thm) StringPair.table
  val empty = StringPair.empty
  val extend = I
  fun merge data = StringPair.merge (K true) data
)

structure HOL4Rewrites = Theory_Data
(
  type T = thm list
  val empty = []
  val extend = I
  val merge = Thm.merge_thms
)

val hol4_debug = Unsynchronized.ref false
fun message s = if !hol4_debug then writeln s else ()

fun add_hol4_rewrite (Context.Theory thy, th) =
    let
        val _ = message "Adding HOL4 rewrite"
        val th1 = th RS @{thm eq_reflection}
                  handle THM _ => th
        val current_rews = HOL4Rewrites.get thy
        val new_rews = insert Thm.eq_thm th1 current_rews
        val updated_thy  = HOL4Rewrites.put new_rews thy
    in
        (Context.Theory updated_thy,th1)
    end
  | add_hol4_rewrite (context, th) = (context,
      (th RS @{thm eq_reflection} handle THM _ => th)
    );

fun ignore_hol4 bthy bthm thy =
    let
        val _ = message ("Ignoring " ^ bthy ^ "." ^ bthm)
        val curmaps = HOL4Maps.get thy
        val newmaps = StringPair.update_new ((bthy,bthm),NONE) curmaps
        val upd_thy = HOL4Maps.put newmaps thy
    in
        upd_thy
    end

val opt_get_output_thy = #2 o HOL4Dump.get

fun get_output_thy thy =
    case #2 (HOL4Dump.get thy) of
        "" => error "No theory file being output"
      | thyname => thyname

val get_output_dir = #1 o HOL4Dump.get

fun add_hol4_move bef aft thy =
    let
        val curmoves = HOL4Moves.get thy
        val newmoves = Symtab.update_new (bef, aft) curmoves
    in
        HOL4Moves.put newmoves thy
    end

fun get_hol4_move bef thy =
  Symtab.lookup (HOL4Moves.get thy) bef

fun follow_name thmname thy =
    let
        val moves = HOL4Moves.get thy
        fun F thmname =
            case Symtab.lookup moves thmname of
                SOME name => F name
              | NONE => thmname
    in
        F thmname
    end

fun add_hol4_cmove bef aft thy =
    let
        val curmoves = HOL4CMoves.get thy
        val newmoves = Symtab.update_new (bef, aft) curmoves
    in
        HOL4CMoves.put newmoves thy
    end

fun get_hol4_cmove bef thy =
  Symtab.lookup (HOL4CMoves.get thy) bef

fun follow_cname thmname thy =
    let
        val moves = HOL4CMoves.get thy
        fun F thmname =
            case Symtab.lookup moves thmname of
                SOME name => F name
              | NONE => thmname
    in
        F thmname
    end

fun add_hol4_mapping bthy bthm isathm thy =
    let 
       (* val _ = writeln ("Before follow_name: "^isathm)  *)
      val isathm = follow_name isathm thy
       (* val _ = writeln ("Adding theorem map: " ^ bthy ^ "." ^ bthm ^ " --> " ^ isathm)*)
        val curmaps = HOL4Maps.get thy
        val newmaps = StringPair.update_new ((bthy,bthm),SOME isathm) curmaps
        val upd_thy = HOL4Maps.put newmaps thy
    in
        upd_thy
    end;

fun get_hol4_type_mapping bthy tycon thy =
    let
        val maps = HOL4TypeMaps.get thy
    in
        StringPair.lookup maps (bthy,tycon)
    end

fun get_hol4_mapping bthy bthm thy =
    let
        val curmaps = HOL4Maps.get thy
    in
        StringPair.lookup curmaps (bthy,bthm)
    end;

fun add_hol4_const_mapping bthy bconst internal isaconst thy =
    let
        val thy = case opt_get_output_thy thy of
                      "" => thy
                    | output_thy => if internal
                                    then add_hol4_cmove (Sign.full_bname thy bconst) (output_thy ^ "." ^ bthy ^ "." ^ bconst) thy
                                    else thy
        val _ = message ("Adding cmap " ^ bthy ^ "." ^ bconst ^ " -> " ^ isaconst ^ (if internal then " (*)" else ""))
        val curmaps = HOL4ConstMaps.get thy
        val newmaps = StringPair.update_new ((bthy,bconst),(internal,isaconst,NONE)) curmaps
        val upd_thy = HOL4ConstMaps.put newmaps thy
    in
        upd_thy
    end;

fun add_hol4_const_renaming bthy bconst newname thy =
    let
        val currens = HOL4Rename.get thy
        val _ = message ("Adding renaming " ^ bthy ^ "." ^ bconst ^ " -> " ^ newname)
        val newrens = StringPair.update_new ((bthy,bconst),newname) currens
        val upd_thy = HOL4Rename.put newrens thy
    in
        upd_thy
    end;

fun get_hol4_const_renaming bthy bconst thy =
    let
        val currens = HOL4Rename.get thy
    in
        StringPair.lookup currens (bthy,bconst)
    end;

fun get_hol4_const_mapping bthy bconst thy =
    let
        val bconst = case get_hol4_const_renaming bthy bconst thy of
                         SOME name => name
                       | NONE => bconst
        val maps = HOL4ConstMaps.get thy
    in
        StringPair.lookup maps (bthy,bconst)
    end

fun add_hol4_const_wt_mapping bthy bconst internal isaconst typ thy =
    let
        val thy = case opt_get_output_thy thy of
                      "" => thy
                    | output_thy => if internal
                                    then add_hol4_cmove (Sign.full_bname thy bconst) (output_thy ^ "." ^ bthy ^ "." ^ bconst) thy
                                    else thy
        val _ = message ("Adding cmap " ^ bthy ^ "." ^ bconst ^ " -> " ^ isaconst ^ (if internal then " (*)" else ""))
        val curmaps = HOL4ConstMaps.get thy
        val newmaps = StringPair.update_new ((bthy,bconst),(internal,isaconst,SOME typ)) curmaps
        val upd_thy = HOL4ConstMaps.put newmaps thy
    in
        upd_thy
    end;

fun add_hol4_type_mapping bthy bconst internal isaconst thy =
    let
        val curmaps = HOL4TypeMaps.get thy
        val _ = writeln ("Adding tmap " ^ bthy ^ "." ^ bconst ^ " -> " ^ isaconst ^ (if internal then " (*)" else ""))
        val newmaps = StringPair.update_new ((bthy,bconst),(internal,isaconst)) curmaps
               (* FIXME avoid handle x *)
               handle x => let val (_, isaconst') = the (StringPair.lookup curmaps (bthy, bconst)) in
                      warning ("couldn't map type "^bthy^"."^bconst^" to "^isaconst^": already mapped to "^isaconst'); raise x end
        val upd_thy = HOL4TypeMaps.put newmaps thy
    in
        upd_thy
    end;

fun add_hol4_pending bthy bthm hth thy =
    let
        val thmname = Sign.full_bname thy bthm
        val _ = message ("Add pending " ^ bthy ^ "." ^ bthm)
        val curpend = HOL4Pending.get thy
        val newpend = StringPair.update_new ((bthy,bthm),hth) curpend
        val upd_thy = HOL4Pending.put newpend thy
        val thy' = case opt_get_output_thy upd_thy of
                       "" => add_hol4_mapping bthy bthm thmname upd_thy
                     | output_thy =>
                       let
                           val new_thmname = output_thy ^ "." ^ bthy ^ "." ^ bthm
                       in
                           upd_thy |> add_hol4_move thmname new_thmname
                                   |> add_hol4_mapping bthy bthm new_thmname
                       end
    in
        thy'
    end;

fun get_hol4_theorem thyname thmname thy =
  let
    val isathms = HOL4Thms.get thy
  in
    StringPair.lookup isathms (thyname,thmname)
  end;

fun add_hol4_theorem thyname thmname hth =
  let
    val _ = message ("Adding HOL4 theorem " ^ thyname ^ "." ^ thmname)
  in
    HOL4Thms.map (StringPair.update_new ((thyname, thmname), hth))
  end;

fun export_hol4_pending thy =
  let
    val rews = HOL4Rewrites.get thy;
    val pending = HOL4Pending.get thy;
    fun process ((bthy,bthm), hth as (_,thm)) thy =
      let
        val thm1 = rewrite_rule (map (Thm.transfer thy) rews) (Thm.transfer thy thm);
        val thm2 = Drule.export_without_context thm1;
      in
        thy
        |> Global_Theory.store_thm (Binding.name bthm, thm2)
        |> snd
        |> add_hol4_theorem bthy bthm hth
      end;
  in
    thy
    |> StringPair.fold process pending
    |> HOL4Pending.put StringPair.empty
  end;

fun setup_dump (dir,thyname) thy =
    HOL4Dump.put (dir,thyname,["(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)"]) thy

fun add_dump str thy =
    let
        val (dir,thyname,curdump) = HOL4Dump.get thy
    in
        HOL4Dump.put (dir,thyname,str::curdump) thy
    end

fun flush_dump thy =
    let
        val (dir,thyname,dumpdata) = HOL4Dump.get thy
        val os = TextIO.openOut (OS.Path.joinDirFile {dir=dir,
                                                      file=thyname ^ ".thy"})
        val _  = app (fn s => TextIO.output(os,s ^ "\n\n")) (rev dumpdata)
        val  _ = TextIO.closeOut os
    in
        HOL4Dump.put ("","",[]) thy
    end

fun set_generating_thy thyname thy =
    case HOL4DefThy.get thy of
        NoImport => HOL4DefThy.put (Generating thyname) thy
      | _ => error "Import already in progess"

fun set_replaying_thy thyname thy =
    case HOL4DefThy.get thy of
        NoImport => HOL4DefThy.put (Replaying thyname) thy
      | _ => error "Import already in progess"

fun clear_import_thy thy =
    case HOL4DefThy.get thy of
        NoImport => error "No import in progress"
      | _ => HOL4DefThy.put NoImport thy

fun get_generating_thy thy =
    case HOL4DefThy.get thy of
        Generating thyname => thyname
      | _ => error "No theory being generated"

fun get_replaying_thy thy =
    case HOL4DefThy.get thy of
        Replaying thyname => thyname
      | _ => error "No theory being replayed"

fun get_import_thy thy =
    case HOL4DefThy.get thy of
        Replaying thyname => thyname
      | Generating thyname => thyname
      | _ => error "No theory being imported"

fun should_ignore thyname thy thmname =
    case get_hol4_mapping thyname thmname thy of
        SOME NONE => true 
      | _ => false

val trans_string =
    let
        fun quote s = "\"" ^ s ^ "\""
        fun F [] = []
          | F (#"\\" :: cs) = patch #"\\" cs
          | F (#"\"" :: cs) = patch #"\"" cs
          | F (c     :: cs) = c :: F cs
        and patch c rest = #"\\" :: c :: F rest
    in
        quote o String.implode o F o String.explode
    end

fun dump_import_thy thyname thy =
    let
        val output_dir = get_output_dir thy
        val output_thy = get_output_thy thy
        val input_thy = Context.theory_name thy
        val import_segment = get_import_segment thy
        val os = TextIO.openOut (OS.Path.joinDirFile {dir=output_dir,
                                                      file=thyname ^ ".imp"})
        fun out s = TextIO.output(os,s)
    val (ignored, mapped) = StringPair.fold
      (fn ((bthy, bthm), v) => fn (ign, map) =>
        if bthy = thyname
        then case v
         of NONE => (bthm :: ign, map)
          | SOME w => (ign, (bthm, w) :: map)
        else (ign, map)) (HOL4Maps.get thy) ([],[]);
    fun mk init = StringPair.fold
      (fn ((bthy, bthm), v) => if bthy = thyname then cons (bthm, v) else I) init [];
    val constmaps = mk (HOL4ConstMaps.get thy);
    val constrenames = mk (HOL4Rename.get thy);
    val typemaps = mk (HOL4TypeMaps.get thy);
    val defmaps = mk (HOL4DefMaps.get thy);
        fun new_name internal isa =
            if internal
            then
                let
                    val paths = Long_Name.explode isa
                    val i = drop (length paths - 2) paths
                in
                    case i of
                        [seg,con] => output_thy ^ "." ^ seg ^ "." ^ con
                      | _ => error "import_rews.dump internal error"
                end
            else
                isa

        val _ = out "import\n\n"

        val _ = out ("import_segment " ^ trans_string import_segment ^ "\n\n")
        val _ = if null defmaps
                then ()
                else out "def_maps"
        val _ = app (fn (hol,isa) =>
                        out ("\n  " ^ (trans_string hol) ^ " > " ^ (trans_string isa))) defmaps
        val _ = if null defmaps
                then ()
                else out "\n\n"

        val _ = if null typemaps
                then ()
                else out "type_maps"
        val _ = app (fn (hol,(internal,isa)) =>
                        out ("\n  " ^ (trans_string hol) ^ " > " ^ (trans_string (new_name internal isa)))) typemaps
        val _ = if null typemaps
                then ()
                else out "\n\n"

        val _ = if null constmaps
                then ()
                else out "const_maps"
        val _ = app (fn (hol,(_,isa,opt_ty)) =>
                        (out ("\n  " ^ (trans_string hol) ^ " > " ^ (trans_string (follow_cname isa thy)));
                         case opt_ty of
                             SOME ty => out (" :: \"" ^ Syntax.string_of_typ_global thy ty ^ "\"")
                           | NONE => ())) constmaps
        val _ = if null constmaps
                then ()
                else out "\n\n"

        val _ = if null constrenames
                then ()
                else out "const_renames"
        val _ = app (fn (old,new) =>
                        out ("\n  " ^ (trans_string old) ^ " > " ^ (trans_string new))) constrenames
        val _ = if null constrenames
                then ()
                else out "\n\n"

        fun gen2replay in_thy out_thy s = 
            let
                val ss = Long_Name.explode s
            in
                if (hd ss = in_thy) then 
                    Long_Name.implode (out_thy::(tl ss))
                else
                    s
            end 

        val _ = if null mapped
                then ()
                else out "thm_maps"
        val _ = app (fn (hol,isa) => out ("\n  " ^ (trans_string hol) ^ " > " ^ (trans_string (gen2replay input_thy output_thy isa)))) mapped
        val _ = if null mapped 
                then ()
                else out "\n\n"

        val _ = if null ignored
                then ()
                else out "ignore_thms"
        val _ = app (fn ign => out ("\n  " ^ (trans_string ign))) ignored
        val _ = if null ignored
                then ()
                else out "\n\n"

        val _ = out "end\n"
        val _ = TextIO.closeOut os
    in
        thy
    end

fun set_used_names names thy =
    let
        val unames = HOL4UNames.get thy
    in
        case unames of
            [] => HOL4UNames.put names thy
          | _ => error "import_rews.set_used_names called on initialized data!"
    end

val clear_used_names = HOL4UNames.put [];

fun get_defmap thyname const thy =
    let
        val maps = HOL4DefMaps.get thy
    in
        StringPair.lookup maps (thyname,const)
    end

fun add_defmap thyname const defname thy =
    let
        val _ = message ("Adding defmap " ^ thyname ^ "." ^ const ^ " --> " ^ defname)
        val maps = HOL4DefMaps.get thy
        val maps' = StringPair.update_new ((thyname,const),defname) maps
        val thy' = HOL4DefMaps.put maps' thy
    in
        thy'
    end

fun get_defname thyname name thy =
    let
        val maps = HOL4DefMaps.get thy
        fun F dname = (dname,add_defmap thyname name dname thy)
    in
        case StringPair.lookup maps (thyname,name) of
            SOME thmname => (thmname,thy)
          | NONE =>
            let
                val used = HOL4UNames.get thy
                val defname = Thm.def_name name
                val pdefname = name ^ "_primdef"
            in
                if not (member (op =) used defname)
                then F defname                 (* name_def *)
                else if not (member (op =) used pdefname)
                then F pdefname                (* name_primdef *)
                else F (singleton (Name.variant_list used) pdefname) (* last resort *)
            end
    end

local
    fun handle_meta [x as Ast.Appl [Ast.Appl [Ast.Constant "_constrain", Ast.Constant @{const_syntax "=="}, _],_,_]] = x
      | handle_meta [x as Ast.Appl [Ast.Appl [Ast.Constant "_constrain", Ast.Constant @{const_syntax all}, _],_]] = x
      | handle_meta [x as Ast.Appl [Ast.Appl [Ast.Constant "_constrain", Ast.Constant @{const_syntax "==>"}, _],_,_]] = x
      | handle_meta [x] = Ast.Appl [Ast.Constant @{const_syntax Trueprop}, x]
      | handle_meta _ = error "import_rews error: Trueprop not applied to single argument"
in
val smarter_trueprop_parsing = [(@{const_syntax Trueprop},handle_meta)]
end

local
    fun initial_maps thy =
        thy |> add_hol4_type_mapping "min" "bool" false @{type_name bool}
            |> add_hol4_type_mapping "min" "fun" false "fun"
            |> add_hol4_type_mapping "min" "ind" false @{type_name ind}
            |> add_hol4_const_mapping "min" "=" false @{const_name HOL.eq}
            |> add_hol4_const_mapping "min" "==>" false @{const_name HOL.implies}
            |> add_hol4_const_mapping "min" "@" false @{const_name "Eps"}
in
val hol4_setup =
  initial_maps #>
  Attrib.setup @{binding import_rew}
    (Scan.succeed (Thm.mixed_attribute add_hol4_rewrite)) "HOL4 rewrite rule"

end
