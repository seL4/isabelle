#!/usr/bin/perl -s-	 # -*-Perl-*-

#---------------------------------------------------------------------
#The following script file is useful to convert old theory files into a
#style consistent with new naming conventions. Now, the names of the
#files must be the same as the names of the theories they define (with
#a ".thy" suffix) and corresponding ML files must also be renamed.
#
#To make this renaming easier, the following perl script can be used.
#It traverses the given directory recursively.  For each file of the
#form abc.thy, this script does the following steps:
#
#1. Reads the file and grabs the first identifier, say Abc (skipping comments
#   (*...*) and white space).
#2. Outputs the commands needed to rename the file abc.thy to Abc.thy,
#   including the appropriate CVS commands.
#3. If abc.ML also exists, it outputs appropriate commands to rename it
#   to Abc.ML.
#
#These commands can be put into a file, which can then be executed.
#If you are not using cvs, use "grep" to extract just the "mv" commands.
#
#						- Sara Kalvala
#						  (sk@cl.cam.ac.uk)
#---------------------------------------------------------------------

open(MATCH_FILES, "find . -name \"*thy\" -print |");

foreach $each_match (<MATCH_FILES>) {
 chop($each_match);
 if($each_match =~ /(.*\/)(\w*)\.thy/) {$dirpart = $1;}
 else {print "something wrong with finding path!\n";
       $dirpart = "";}
 open (CONTENTS, $each_match);
 @readit = <CONTENTS>;
 chop(@readit); $oneline = join(" ",@readit);
 $oneline =~ s/\(\*([^\*]|(\*[^\)]))*\*\)//g ;
# comments: have to remove strings of anything but stars or stars
# followed by anything but right parenthesis 
 if($oneline =~ /\s*([^ ]*)\s*=.*/)
 {$th_name = $1;
  $new_name = $dirpart . $th_name . ".thy";
  print "mv -i $each_match $new_name \n";
  print "cvs rm $each_match ; cvs add $new_name \n";
# for ML files
  $each_ML = $each_match;
  $each_ML =~ s/.thy/.ML/;
  if (-e $each_ML) { $new_ML = $dirpart . $th_name . ".ML";
		     print "mv -i $each_ML $new_ML \n";
		     print "cvs rm $each_ML ; cvs add $new_ML \n";}}
 else {print "something wrong with format of theory file!\n";}
}

