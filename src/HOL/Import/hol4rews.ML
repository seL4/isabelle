structure StringPair = TableFun(type key = string * string val ord = prod_ord string_ord string_ord);

type holthm = (term * term) list * thm

datatype ImportStatus =
	 NoImport
       | Generating of string
       | Replaying of string

structure HOL4DefThyArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/import_status"
type T = ImportStatus
val empty = NoImport
val copy = I
val prep_ext = I
fun merge (NoImport,NoImport) = NoImport
  | merge _ = (warning "Import status set during merge"; NoImport)
fun print sg import_status =
    Pretty.writeln (Pretty.str (case import_status of NoImport => "No current import" | Generating thyname => ("Generating " ^ thyname) | Replaying thyname => ("Replaying " ^ thyname)))
end;

structure HOL4DefThy = TheoryDataFun(HOL4DefThyArgs);

structure ImportSegmentArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/import"
type T = string
val empty = ""
val copy = I
val prep_ext = I
fun merge ("",arg) = arg
  | merge (arg,"") = arg
  | merge (s1,s2) =
    if s1 = s2
    then s1
    else error "Trying to merge two different import segments"
fun print sg import_segment =
    Pretty.writeln (Pretty.str ("Import segment: " ^ import_segment))
end;

structure ImportSegment = TheoryDataFun(ImportSegmentArgs);

val get_import_segment = ImportSegment.get
val set_import_segment = ImportSegment.put

structure HOL4UNamesArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/used_names"
type T = string list
val empty = []
val copy = I
val prep_ext = I
fun merge ([],[]) = []
  | merge _ = error "Used names not empty during merge"
fun print sg used_names =
    Pretty.writeln (Pretty.str "Printing of HOL4/used_names Not implemented")
end;

structure HOL4UNames = TheoryDataFun(HOL4UNamesArgs);

structure HOL4DumpArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/dump_data"
type T = string * string * string list
val empty = ("","",[])
val copy = I
val prep_ext = I
fun merge (("","",[]),("","",[])) = ("","",[])
  | merge _ = error "Dump data not empty during merge"
fun print sg dump_data =
    Pretty.writeln (Pretty.str "Printing of HOL4/dump_data Not implemented")
end;

structure HOL4Dump = TheoryDataFun(HOL4DumpArgs);

structure HOL4MovesArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/moves"
type T = string Symtab.table
val empty = Symtab.empty
val copy = I
val prep_ext = I
val merge = Symtab.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 moves:"
	(Symtab.foldl (fn (xl,(bef,aft)) => (Pretty.str (bef ^ " --> " ^ aft)::xl)) ([],tab)))
end;

structure HOL4Moves = TheoryDataFun(HOL4MovesArgs);

structure HOL4ImportsArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/imports"
type T = string Symtab.table
val empty = Symtab.empty
val copy = I
val prep_ext = I
val merge = Symtab.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 imports:"
	(Symtab.foldl (fn (xl,(thyname,segname)) => (Pretty.str (thyname ^ " imported from segment " ^ segname)::xl)) ([],tab)))
end;

structure HOL4Imports = TheoryDataFun(HOL4ImportsArgs);

fun get_segment2 thyname thy =
    let
	val imps = HOL4Imports.get thy
    in
	Symtab.lookup(imps,thyname)
    end

fun set_segment thyname segname thy =
    let
	val imps = HOL4Imports.get thy
	val imps' = Symtab.update_new((thyname,segname),imps)
    in
	HOL4Imports.put imps' thy
    end

structure HOL4CMovesArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/constant_moves"
type T = string Symtab.table
val empty = Symtab.empty
val copy = I
val prep_ext = I
val merge = Symtab.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 constant moves:"
	(Symtab.foldl (fn (xl,(bef,aft)) => (Pretty.str (bef ^ " --> " ^ aft)::xl)) ([],tab)))
end;

structure HOL4CMoves = TheoryDataFun(HOL4CMovesArgs);

structure HOL4MapsArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/mappings"
type T = (string option) StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 mappings:"
	(StringPair.foldl (fn (xl,((bthy,bthm),isathm)) => (Pretty.str (bthy ^ "." ^ bthm ^ (case isathm of Some th => " --> " ^ th | None => "IGNORED"))::xl)) ([],tab)))
end;

structure HOL4Maps = TheoryDataFun(HOL4MapsArgs);

structure HOL4ThmsArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/theorems"
type T = holthm StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 mappings:"
	(StringPair.foldl (fn (xl,((bthy,bthm),(_,thm))) => (Pretty.str (bthy ^ "." ^ bthm ^ ":")::(Display.pretty_thm thm)::xl)) ([],tab)))
end;

structure HOL4Thms = TheoryDataFun(HOL4ThmsArgs);

structure HOL4ConstMapsArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/constmappings"
type T = (bool * string * typ option) StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 constant mappings:"
	(StringPair.foldl (fn (xl,((bthy,bconst),(internal,isaconst,_))) => (Pretty.str (bthy ^ "." ^ bconst ^ " --> " ^ isaconst ^ (if internal then " (*)" else ""))::xl)) ([],tab)))
end;

structure HOL4ConstMaps = TheoryDataFun(HOL4ConstMapsArgs);

structure HOL4RenameArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/renamings"
type T = string StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 constant renamings:"
	(StringPair.foldl (fn (xl,((bthy,bconst),newname)) => (Pretty.str (bthy ^ "." ^ bconst ^ " --> " ^ newname)::xl)) ([],tab)))
end;

structure HOL4Rename = TheoryDataFun(HOL4RenameArgs);

structure HOL4DefMapsArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/def_maps"
type T = string StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 constant definitions:"
	(StringPair.foldl (fn (xl,((bthy,bconst),newname)) => (Pretty.str (bthy ^ "." ^ bconst ^ ": " ^ newname)::xl)) ([],tab)))
end;

structure HOL4DefMaps = TheoryDataFun(HOL4DefMapsArgs);

structure HOL4TypeMapsArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/typemappings"
type T = (bool * string) StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 type mappings:"
	(StringPair.foldl (fn (xl,((bthy,bconst),(internal,isaconst))) => (Pretty.str (bthy ^ "." ^ bconst ^ " --> " ^ isaconst ^ (if internal then " (*)" else ""))::xl)) ([],tab)))
end;

structure HOL4TypeMaps = TheoryDataFun(HOL4TypeMapsArgs);

structure HOL4PendingArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/pending"
type T = ((term * term) list * thm) StringPair.table
val empty = StringPair.empty
val copy = I
val prep_ext = I
val merge = StringPair.merge (K true)
fun print sg tab =
    Pretty.writeln (Pretty.big_list "HOL4 pending theorems:"
	(StringPair.foldl (fn (xl,((bthy,bthm),(_,th))) => (Pretty.chunks [Pretty.str (bthy ^ "." ^ bthm ^ ":"),Display.pretty_thm th]::xl)) ([],tab)))
end;

structure HOL4Pending = TheoryDataFun(HOL4PendingArgs);

structure HOL4RewritesArgs: THEORY_DATA_ARGS =
struct
val name = "HOL4/rewrites"
type T = thm list
val empty = []
val copy = I
val prep_ext = I
val merge = Library.gen_union Thm.eq_thm
fun print sg thms =
    Pretty.writeln (Pretty.big_list "HOL4 rewrite rules:"
				    (map Display.pretty_thm thms))
end;

structure HOL4Rewrites = TheoryDataFun(HOL4RewritesArgs);

val hol4_debug = ref false
fun message s = if !hol4_debug then writeln s else ()

fun add_hol4_rewrite (thy,th) =
    let
	val _ = message "Adding HOL4 rewrite"
	val th1 = th RS eq_reflection
	val current_rews = HOL4Rewrites.get thy
	val new_rews = gen_ins Thm.eq_thm (th1,current_rews)
	val updated_thy  = HOL4Rewrites.put new_rews thy
    in
	(updated_thy,th1)
    end;

fun ignore_hol4 bthy bthm thy =
    let
	val _ = message ("Ignoring " ^ bthy ^ "." ^ bthm)
	val curmaps = HOL4Maps.get thy
	val newmaps = StringPair.update_new(((bthy,bthm),None),curmaps)
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
	val newmoves = Symtab.update_new((bef,aft),curmoves)
    in
	HOL4Moves.put newmoves thy
    end

fun get_hol4_move bef thy =
    let
	val moves = HOL4Moves.get thy
    in
	Symtab.lookup(moves,bef)
    end

fun follow_name thmname thy =
    let
	val moves = HOL4Moves.get thy
	fun F thmname =
	    case Symtab.lookup(moves,thmname) of
		Some name => F name
	      | None => thmname
    in
	F thmname
    end

fun add_hol4_cmove bef aft thy =
    let
	val curmoves = HOL4CMoves.get thy
	val newmoves = Symtab.update_new((bef,aft),curmoves)
    in
	HOL4CMoves.put newmoves thy
    end

fun get_hol4_cmove bef thy =
    let
	val moves = HOL4CMoves.get thy
    in
	Symtab.lookup(moves,bef)
    end

fun follow_cname thmname thy =
    let
	val moves = HOL4CMoves.get thy
	fun F thmname =
	    case Symtab.lookup(moves,thmname) of
		Some name => F name
	      | None => thmname
    in
	F thmname
    end

fun add_hol4_mapping bthy bthm isathm thy =
    let
	val isathm = follow_name isathm thy
	val _ = message ("Adding theorem map: " ^ bthy ^ "." ^ bthm ^ " --> " ^ isathm)
	val curmaps = HOL4Maps.get thy
	val newmaps = StringPair.update_new(((bthy,bthm),Some isathm),curmaps)
	val upd_thy = HOL4Maps.put newmaps thy
    in
	upd_thy
    end;

fun get_hol4_type_mapping bthy tycon thy =
    let
	val maps = HOL4TypeMaps.get thy
    in
	StringPair.lookup(maps,(bthy,tycon))
    end

fun get_hol4_mapping bthy bthm thy =
    let
	val curmaps = HOL4Maps.get thy
    in
	StringPair.lookup(curmaps,(bthy,bthm))
    end;

fun add_hol4_const_mapping bthy bconst internal isaconst thy =
    let
	val thy = case opt_get_output_thy thy of
		      "" => thy
		    | output_thy => if internal
				    then add_hol4_cmove (Sign.full_name (sign_of thy) bconst) (output_thy ^ "." ^ bthy ^ "." ^ bconst) thy
				    else thy
	val _ = message ("Adding cmap " ^ bthy ^ "." ^ bconst ^ " -> " ^ isaconst ^ (if internal then " (*)" else ""))
	val curmaps = HOL4ConstMaps.get thy
	val newmaps = StringPair.update_new(((bthy,bconst),(internal,isaconst,None)),curmaps)
	val upd_thy = HOL4ConstMaps.put newmaps thy
    in
	upd_thy
    end;

fun add_hol4_const_renaming bthy bconst newname thy =
    let
	val currens = HOL4Rename.get thy
	val _ = message ("Adding renaming " ^ bthy ^ "." ^ bconst ^ " -> " ^ newname)
	val newrens = StringPair.update_new(((bthy,bconst),newname),currens)
	val upd_thy = HOL4Rename.put newrens thy
    in
	upd_thy
    end;

fun get_hol4_const_renaming bthy bconst thy =
    let
	val currens = HOL4Rename.get thy
    in
	StringPair.lookup(currens,(bthy,bconst))
    end;

fun get_hol4_const_mapping bthy bconst thy =
    let
	val bconst = case get_hol4_const_renaming bthy bconst thy of
			 Some name => name
		       | None => bconst
	val maps = HOL4ConstMaps.get thy
    in
	StringPair.lookup(maps,(bthy,bconst))
    end

fun add_hol4_const_wt_mapping bthy bconst internal isaconst typ thy =
    let
	val thy = case opt_get_output_thy thy of
		      "" => thy
		    | output_thy => if internal
				    then add_hol4_cmove (Sign.full_name (sign_of thy) bconst) (output_thy ^ "." ^ bthy ^ "." ^ bconst) thy
				    else thy
	val _ = message ("Adding cmap " ^ bthy ^ "." ^ bconst ^ " -> " ^ isaconst ^ (if internal then " (*)" else ""))
	val curmaps = HOL4ConstMaps.get thy
	val newmaps = StringPair.update_new(((bthy,bconst),(internal,isaconst,Some typ)),curmaps)
	val upd_thy = HOL4ConstMaps.put newmaps thy
    in
	upd_thy
    end;

fun add_hol4_type_mapping bthy bconst internal isaconst thy =
    let
	val curmaps = HOL4TypeMaps.get thy
	val _ = message ("Adding tmap " ^ bthy ^ "." ^ bconst ^ " -> " ^ isaconst ^ (if internal then " (*)" else ""))
	val newmaps = StringPair.update_new(((bthy,bconst),(internal,isaconst)),curmaps)
	val upd_thy = HOL4TypeMaps.put newmaps thy
    in
	upd_thy
    end;

fun add_hol4_pending bthy bthm hth thy =
    let
	val thmname = Sign.full_name (sign_of thy) bthm
	val _ = message ("Add pending " ^ bthy ^ "." ^ bthm)
	val curpend = HOL4Pending.get thy
	val newpend = StringPair.update_new(((bthy,bthm),hth),curpend)
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
	StringPair.lookup (isathms,(thyname,thmname))
    end

fun add_hol4_theorem thyname thmname hth thy =
    let
	val _ = message ("Adding HOL4 theorem " ^ thyname ^ "." ^ thmname)
	val isathms = HOL4Thms.get thy
	val isathms' = StringPair.update_new (((thyname,thmname),hth),isathms)
	val thy' = HOL4Thms.put isathms' thy
    in
	thy'
    end

fun export_hol4_pending thy =
    let
	val rews    = HOL4Rewrites.get thy
	val outthy  = get_output_thy thy
	fun process (thy,((bthy,bthm),hth as (_,thm))) =
	    let
		val sg      = sign_of thy
		val thm1 = rewrite_rule (map (transfer_sg sg) rews) (transfer_sg sg thm)
		val thm2 = standard thm1
		val (thy2,_) = PureThy.store_thm((bthm,thm2),[]) thy
		val thy5 = add_hol4_theorem bthy bthm hth thy2
	    in
		thy5
	    end

	val pending = HOL4Pending.get thy
	val thy1    = StringPair.foldl process (thy,pending)
	val thy2    = HOL4Pending.put (StringPair.empty) thy1
    in
	thy2
    end;

fun setup_dump (dir,thyname) thy =
    HOL4Dump.put (dir,thyname,[]) thy

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
	Some None => true 
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
	val import_segment = get_import_segment thy
	val sg = sign_of thy
	val os = TextIO.openOut (OS.Path.joinDirFile {dir=output_dir,
						      file=thyname ^ ".imp"})
	fun out s = TextIO.output(os,s)
	val (ignored,mapped) =
	    StringPair.foldl (fn ((ign,map),((bthy,bthm),v)) =>
				 if bthy = thyname
				 then (case v of
					   None => (bthm::ign,map)
					 | Some w => (ign,(bthm,w)::map))
				 else (ign,map))
				 (([],[]),HOL4Maps.get thy)
	val constmaps =
	    StringPair.foldl (fn (map,((bthy,bthm),v)) =>
				 if bthy = thyname
				 then (bthm,v)::map
				 else map)
				 ([],HOL4ConstMaps.get thy)

	val constrenames =
	    StringPair.foldl (fn (map,((bthy,bthm),v)) =>
				 if bthy = thyname
				 then (bthm,v)::map
				 else map)
				 ([],HOL4Rename.get thy)

	val typemaps =
	    StringPair.foldl (fn (map,((bthy,bthm),v)) =>
				 if bthy = thyname
				 then (bthm,v)::map
				 else map)
				 ([],HOL4TypeMaps.get thy)

	val defmaps =
	    StringPair.foldl (fn (map,((bthy,bthm),v)) =>
				 if bthy = thyname
				 then (bthm,v)::map
				 else map)
				 ([],HOL4DefMaps.get thy)

	fun new_name internal isa =
	    if internal
	    then
		let
		    val paths = NameSpace.unpack isa
		    val i = drop(length paths - 2,paths)
		in
		    case i of
			[seg,con] => output_thy ^ "." ^ seg ^ "." ^ con
		      | _ => error "hol4rews.dump internal error"
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
	val _ = app (fn (hol,(internal,isa,opt_ty)) =>
			(out ("\n  " ^ (trans_string hol) ^ " > " ^ (trans_string (follow_cname isa thy)));
			 case opt_ty of
			     Some ty => out (" :: \"" ^ (string_of_ctyp (ctyp_of sg ty)) ^ "\"")
			   | None => ())) constmaps
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

	val _ = if null mapped
		then ()
		else out "thm_maps"
	val _ = app (fn (hol,isa) => out ("\n  " ^ (trans_string hol) ^ " > " ^ (trans_string isa))) mapped
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
	  | _ => error "hol4rews.set_used_names called on initialized data!"
    end

val clear_used_names = HOL4UNames.put HOL4UNamesArgs.empty

fun get_defmap thyname const thy =
    let
	val maps = HOL4DefMaps.get thy
    in
	StringPair.lookup(maps,(thyname,const))
    end

fun add_defmap thyname const defname thy =
    let
	val _ = message ("Adding defmap " ^ thyname ^ "." ^ const ^ " --> " ^ defname)
	val maps = HOL4DefMaps.get thy
	val maps' = StringPair.update_new(((thyname,const),defname),maps)
	val thy' = HOL4DefMaps.put maps' thy
    in
	thy'
    end

fun get_defname thyname name thy =
    let
	val maps = HOL4DefMaps.get thy
	fun F dname = (dname,add_defmap thyname name dname thy)
    in
	case StringPair.lookup(maps,(thyname,name)) of
	    Some thmname => (thmname,thy)
	  | None =>
	    let
		val used = HOL4UNames.get thy
		val defname = def_name name
		val pdefname = name ^ "_primdef"
	    in
		if not (defname mem used)
		then F defname                 (* name_def *)
		else if not (pdefname mem used)
		then F pdefname                (* name_primdef *)
		else F (variant used pdefname) (* last resort *)
	    end
    end

local
    fun handle_meta [x as Appl[Appl[Constant "_constrain", Constant "==", _],_,_]] = x
      | handle_meta [x as Appl[Appl[Constant "_constrain", Constant "all", _],_]] = x
      | handle_meta [x as Appl[Appl[Constant "_constrain", Constant "==>", _],_,_]] = x
      | handle_meta [x] = Appl[Constant "Trueprop",x]
in
val smarter_trueprop_parsing = [("Trueprop",handle_meta)]
end

local
    fun initial_maps thy =
	thy |> add_hol4_type_mapping "min" "bool" false "bool"
	    |> add_hol4_type_mapping "min" "fun" false "fun"
	    |> add_hol4_type_mapping "min" "ind" false "Nat.ind"
	    |> add_hol4_const_mapping "min" "=" false "op ="
	    |> add_hol4_const_mapping "min" "==>" false "op -->"
	    |> add_hol4_const_mapping "min" "@" false "Hilbert_Choice.Eps"
in
val hol4_setup =
    [HOL4Rewrites.init,
     HOL4Maps.init,
     HOL4UNames.init,
     HOL4DefMaps.init,
     HOL4Moves.init,
     HOL4CMoves.init,
     HOL4ConstMaps.init,
     HOL4Rename.init,
     HOL4TypeMaps.init,
     HOL4Pending.init,
     HOL4Thms.init,
     HOL4Dump.init,
     HOL4DefThy.init,
     HOL4Imports.init,
     ImportSegment.init,
     initial_maps,
     Attrib.add_attributes [("hol4rew",
			     (Attrib.no_args add_hol4_rewrite,
			      Attrib.no_args Attrib.undef_local_attribute),
			     "HOL4 rewrite rule")]]
end
