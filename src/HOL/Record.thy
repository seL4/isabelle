(*  Title:      HOL/Record.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Extensible records with structural subtyping in HOL.  See
Tools/record_package.ML for the actual implementation.
*)

Record = Prod +


(* concrete syntax *)

nonterminals
  ident field fields

syntax
  ""		    :: "id => ident"			("_")
  ""		    :: "longid => ident"		("_")
  "_field"	    :: "[ident, 'a] => field"		("(2_ =/ _)")
  ""	            :: "field => fields"		("_")
  "_fields"	    :: "[field, fields] => fields"	("_,/ _")
  "_record"	    :: "fields => 'a"			("({: _ :})")
  "_record_scheme"  :: "[fields, 'a] => 'b"		("({: _,/ (2... =/ _) :})")


(* type class for record extensions *)

global		(*compatibility with global_names flag!*)

axclass more < term

local

instance unit :: more
instance "*" :: (term, more) more


(* initialize the package *)

setup
  RecordPackage.setup


end
