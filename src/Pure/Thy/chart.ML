(*  ID:         $Id$
    Author:	Mateja Jamnik, University of Cambridge
    Copyright   1995  University of Cambridge

   Generator of the dependency charts of Isabelle theories.
*)


(* --------------------
   Declaration of the variables carrying the name 
   of the location of source files:
   
   path -    location where the generated HTML files
	     should be stored
   srcpath - location where the source files are stored
	     (ie. the graphics files)
   -------------------- *)

val htmlpath = "/homes/lcp/html_isa/";
val srcpath = "/homes/lcp/Isa/Theory/";



(* --------------------
   Notices that display the legend for every dependency 
   chart, and the link back to the main listing of all
   theories.
   -------------------- *)

val notice1 =
"<BR>\n"^"The name of the file is linked to the theory file <BR>\n";

val notice2 =
"<IMG SRC = \""^srcpath^"red_arrow.gif\" ALT = (sub)></A>\n"^
" stands for subtheories (child theories) <BR>\n"^

"<IMG SRC = \""^srcpath^"blue_arrow.gif\" ALT = (super)></A>\n"^
" stands for supertheories (parent theories) <BR>\n<BR>\n";


val back = "<A HREF = \""^htmlpath^"00-chart.html\">Back</A>\n"^
" to the original listing of all the theories. <BR>\n<HR>\n<BR>\n";



(* --------------------
   Get a list of all theory files in Isabelle
   that have been loaded.
   -------------------- *)

print_depth 1000;

val theory_list = !loaded_thys;

val files = Symtab.alist_of (theory_list);



(* --------------------
   Get a list of all theory files and their children.
   -------------------- *)

fun subtheory (tname, ThyInfo{children,...}) = (tname,children);

val subtheories = map subtheory (files);



(* --------------------
   Extract a list of all theory files only.
   -------------------- *)

fun theory ( [], list ) = list
  | theory ( (string, _)::rest, list ) = theory(rest, string::list);



(* --------------------
   Use quick sort to sort the theories in
   the alphabetic order. Variable a as the first 
   element of the list is used as a pivot value.
   -------------------- *)

fun quick [] = []
  | quick [x] = [x]
  | quick (a::bs) = let
          fun part (l,r,[]) : string list = (quick l) @ (a::quick r)
            | part (l,r,x::xs) = if x<=a then part(x::l, r, xs)
                                         else part(l, x::r, xs)
          in part([], [], bs) end;

val theories = quick(theory(subtheories,[]));



(* --------------------
   Insert the identifier of the supertheory
   matrix for every row. Also insert elements
   into the list of identifier's parents in
   alphabetic order.
   -------------------- *)

fun listins ( l, [], x:string ) = l@[x]
  | listins ( l, e::r, x ) = if x>e then listins( l@[e], r, x )
                                    else if x<>e then l@[x,e]@r
					         else l@[x]@r;



(* --------------------
   Arguments:
   t         - accumulator of the resulting supertheory matrix
   result    - temporary resulting matrix (up until now)
   (e,ident) - a list of identifier and its child
   The child e of subtheory matrix becomes identifier ident of
   the supertheory matrix. The identifier ident of subtheory
   matrix becomes the parent elem of supertheory matrix.
   Call function:
		- listins
   -------------------- *)

fun matins ( t, [], (ident:string, elem:string) ) = t@[(ident,[elem])]
  | matins ( t, (x:string,y:string list)::b, 
	        (ident:string, elem:string) ) =
    if x=ident then t@[(x,listins([],y,elem))]@b
               else matins (t@[(x,y)], b, (ident,elem));



(* --------------------
   Instantiate the identifier ident, and the list of
   its children (e::l), where e is its first child.
   Call function:
		- matins
   -------------------- *)

fun rowins ( (ident, []), result ) = result
  | rowins ( (ident, e::l), result ) =
    rowins ( (ident, l), matins([],result,(e,ident)) );



(* --------------------
   Extract recursively one row at a time of the
   subtheory matrix.
   Call function:
		-rowins
   -------------------- *)

fun matinv ( [], result ) = result
  | matinv ( l::b, result ) = matinv( b, rowins(l, result) );



(* --------------------
   Holds the value of supertheory matrix.
   Call function:
		-matinv
   -------------------- *)

val supertheories = matinv ( subtheories, [] );




(* ---------------------------------------------------------------------- *)




(* --------------------
   Entries for the main chart of all the theories.
   Every theory name is a link to the theory definition.
   Down arrow is a link to the subtheory chart of that theory.
   Up arrow is a link to the supertheory chart of that theory.
   -------------------- *)

fun entries x = "\n"^
    "<A HREF = \""^htmlpath^x^
    "_sub.html\">\n<IMG SRC = \""^srcpath^
    "red_arrow.gif\" ALT = (sub)></A>\n"^

    "<A HREF = \""^htmlpath^x^
    "_sup.html\">\n<IMG SRC = \""^srcpath^
    "blue_arrow.gif\" ALT = (super)></A> \n"^
    "<A HREF = \""^htmlpath^x^".html\">"^x^"</A><BR>\n";

fun all_list x = map entries x;



(* --------------------
   Convert a list of characters and strings
   into a string.
   -------------------- *)

fun join ([],res) = res
  | join (x::xs,res) = join(xs,res^x);



val bottom =
"<HR>\n\n"^
"<! ---------------------------------------------------------------- >\n\n";



(* --------------------
   Find the row of the matrix into which
   the parent (or children) theories
   are going to be inserted.
   -------------------- *)

fun findline (_,[]) = []
  | findline (th:string,(id,row:string list)::mat) =
    if th=id then row else findline(th,mat);



(* --------------------
   Once a parent (or child) theory has been identified
   make an entry for it with appropriate indentation and with
   further links to its parent (or child) dependency chart.
   It contains the subfunction:
           - maketableentry
   -------------------- *)

fun dependencies (th, mat) =
    let
	val stringlist = findline(th,mat);
	fun maketableentry name =
	    "<LI> <A HREF=\""^htmlpath^name^".html\">"^name^"</A>\n"^
	    " <A HREF = \""^htmlpath^name^
	    "_sub.html\">\n<IMG SRC = \""^srcpath^
	    "red_arrow.gif\" ALT = (sub)></A> \n"^
	    "<A HREF = \""^htmlpath^name^
	    "_sup.html\">\n<IMG SRC = \""^srcpath^
	    "blue_arrow.gif\" ALT = (super)></A>\n"^
	    "<UL>\n"^
	    join(dependencies(name,mat),"")^
	    "</UL>\n"
    in
	map maketableentry stringlist
    end;



(* --------------------
   Create individual super- and sub-theory charts for
   each theory. Store them in separate files.
   It contains the subfunction:
             - page
   -------------------- *)

fun pages ([],_,_,_) = 0
  | pages (th::theories,theorymatrix,suffix,headline) =
    let
	fun page th =
	    let

		(* Open files for output of individual charts. *)

		val outf_each = open_out (htmlpath^th^"_"^suffix^".html")
	    in

		(* Recursively write to the output files the *)
                (* dependent theories with appropriate links *)
		(* depending upon the suffix.		     *)

		output(outf_each,

			(* Heading of each dependency chart. *)

		       "<A NAME=\""^th^"_"^suffix^".html\"></a>\n"^
		       "<BR><H1>"^headline^"</H1>\n\n"^notice1^notice2^back^
		       "\n"^"<A HREF=\""^htmlpath^th^".html\">"^th^"</A>\n"^
		       (if suffix="sup"
			    then ("<A HREF = \""^htmlpath^th^
				 "_sub.html\">\n<IMG SRC = \""^srcpath^
				 "red_arrow.gif\" ALT = (sub)></A>\n")
			    else ("<A HREF = \""^htmlpath^th^
				 "_sup.html\">\n<IMG SRC = \""^srcpath^
				 "blue_arrow.gif\" ALT = (super)></A>\n"))^
				 "<UL>\n");

		(* Recursively call the function dependencies  *)
		(* to create an entry in the chart for all the *)
		(* levels of dependencies in the hierarchical  *)
		(* structure of theory files for a given       *)
		(* theory.                                     *)

		output(outf_each,
		       join(dependencies(th,theorymatrix),""));

		output(outf_each,
		       "</UL>\n"^bottom);

		(* Close for output the individual *)
	        (* dependency charts.              *)

		close_out (outf_each)
	    end;
    in

	(* Anti-bugging technique to follow the *) 
	(* execution of the program.	       *)

	output(std_out,"theory: "^th^"\n");


	(* The main driver for the creation of the dependencies *)
	(* which calls the functions page and pages. This will  *)
	(* go into depth of dependency of each theory with the  *)
	(* appropriate indentation.				*)

	page(th);
	pages(theories,theorymatrix,suffix,headline)
    end;




(* ---------------------------------------------------------------------- *)




(* --------------------
   Generate the main chart 00-chart.html containing 
   the listing of all the theories and the links to charts.
   -------------------- *)

val outtext = htmlpath^"00-chart.html";
val outfile = open_out outtext;

val head = "<HTML>\n<HEAD>\n<TITLE>"^outtext^
    "</TITLE>\n</HEAD>\n\n"^"<BODY>\n";

val title = "<H1>Dependency Diagram</H1></P>\n\n"^notice1^notice2;
val page1part1 = "<H2>Subtheories and Supertheories</H2>\n<BR>\n\n"^
    join(all_list(theories),"")^"<BR>\n";
val page1part3 = bottom;

val tail = "</BODY>\n"^"</HTML>";

output(outfile,head);
output(outfile,title);
output(outfile,page1part1);
output(outfile,page1part3);



(* ---------------------------------------------------------------------- *)



(* --------------------
   The main driver to create individual super- and sub-theory
   charts for each individual theory. The arguments passed are:
          - the list of all the theories
          - the super- or sub-theory matrix
	  - the appropriate suffix sup or sub
	  - the title of the chart
   It calls the function:
          - pages
   -------------------- *)

pages(theories,subtheories,"sub","Subtheories");
pages(theories,supertheories,"sup","Supertheories");
output(outfile,tail);



(* --------------------
   Close file for output.
   -------------------- *)
close_out(outfile);
