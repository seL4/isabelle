#!/usr/local/dist/bin/perl
'di';
'ig00';
###############################################
# Title:      Tools/8bit/perl/generators/gen-isa2latex
# ID:         $Id$
# Author:     Franz Regensburger
# Copyright   1996 TU Muenchen
#
# generates documentation form on the basis of the configuration
# files for keyboard map and translations
#
# Franz Regensburger <regensbu@informatik.tu-muenchen.de> 8.3.95
###############################################

# I like to see the output as it happens (flushed output)

$| = 1;

# cash current working directory 
require "pwd.pl";
&initpwd;

$initial_dir = $ENV{'PWD'};

########################
# comand line processing
# processes all known switches and ingnores others.
# First non-switch which is the name of a text file is 
# interpreted as name of translation file.
# Second non-switch which is the name of a text file is 
# interpreted as name of the keymap file.
#

# initialize
$translation_file="";
$keymap_file="";
$do_debug = 0;
$do_ddebug = 0;
$latex2e = 0;


while (@ARGV){
    $cur_arg = shift @ARGV;
    if ($cur_arg eq '-d')  {$do_debug = 1;}
    elsif ($cur_arg eq '-dd') {$do_debug = 1; $do_ddebug = 1;}
    elsif ($cur_arg eq '-2e') {$latex2e = 1;}
    elsif ((-T $cur_arg) && !$translation_file) {$translation_file = $cur_arg;}
    elsif ((-T $cur_arg) && !$keymap_file) {$keymap_file = $cur_arg;}
}

# complain if no translationsfile is found

if ($translation_file eq "") {
    print "\nno translation file suplied or argument is not a text file\n\n";
    print "usage gen-isadoc [-d -dd -2e ] translation-file keymap-file\n", 
          "options must be seperated by blanks!";
    die "\n";
}

if ($keymap_file eq "") {
    print "\nno keymap file suplied or argument is not a text file\n\n";
    print "usage gen-isadoc [-d -dd -2e] translation-file keymap-file\n", 
          "options must be seperated by blanks!";
    die "\n";
}

print "debug mode is on\n" if $do_debug;
print "double debug mode is on\n" if $do_ddebug;
print "documentation is produced with LaTeX-2e\n" if ($do_debug & $latex2e);
print "documentation is produced with LaTeX 2.09\n" if ($do_debug &!$latex2e);
print "name of translation file is $translation_file\n" if $do_debug;
print "name of keymap file is $keymap_file\n" if $do_debug;

########################
# open the translations  file

open(INFILE,$translation_file) || die "can't open $translation_file: $!\n";
print "opened translation file,\nprocessing\n" if $do_debug;

########################
# configuration of HI_TABLE
print "\nsetup for HI_TABLE\n" if $do_debug;

########################
# search for START_HI_TABLE
#
$start_hi_table = 
    &look_for_value('^\s*START_HI_TABLE\s*"(\d+)"',"START_HI_TABLE");

if ($start_hi_table eq "") {
    die "\ncan't find START_HI_TABLE in translation file\n";}

if ($start_hi_table < 128 || 255 < $start_hi_table) {
    die "\nSTART_HI_TABLE not in range 128 - 255\n";}

########################
# search for BEGIN_HI_TABLE

$found = &look_for_label('^\s*BEGIN_HI_TABL(E)',"BEGIN_HI_TABLE");

if ($found eq "") {
    die "\ncan't find BEGIN_HI_TABLE in translation file\n";}

########################
# read the HI_TABLE

$index = 0;
#$max_hi_len = 0; # for pretty printing
$found = 0;
$end_hi_table = 0;
$pattern = '^>\s*"([^"]*)"\s*"([^"]*)"\s*"([^"]*)"';

while (<INFILE> ){
    if (/^\s*END_HI_TABLE/){
	    print "line $.: END_HI_TABLE found\n" if $do_debug;
	    $found = 1;
	    $end_hi_table = $start_hi_table + $index - 1;
	    last;}
    elsif (($temp1,$temp2,$temp3) = /$pattern/){
	# no doubling of backslashes needed for docu files
#	$max_hi_len = length($temp2) if $max_hi_len < length($temp2);
	$hi_table[$index]= join('"',$temp2,$temp3);
	 # the " as seperator is perfect since it cannot occur inside the strings
	 # backslashes are duplicated
	printf "line $.: \"%s\" \t\t \"%s\"\n", 
	       $temp2,$temp3 if $do_ddebug;
	$index++;
    }
}

if (!$found){
	die "\ncan't find END_HI_TABLE in translation file\n";}

if ($end_hi_table < $start_hi_table || 255 < $end_hi_table ){
	die "\nEND_HI_TABLE $end_hi_table not in range $start_low_table - 255\n";}
    else {print "computed index for END_HI_TABLE is $end_hi_table\n"  if $do_debug;
#          print "maximal length of entries is $max_hi_len\n"   if $do_ddebug;
}

########################
# configuration of SEQ_TABLE
print "\nsetup for SEQ_TABLE\n" if $do_debug;

########################
# search for BEGIN_SEQ_TABLE

$found = &look_for_label('^\s*BEGIN_SEQ_TABL(E)',"BEGIN_SEQ_TABLE");

if ($found eq "") {
    die "\ncan't find BEGIN_SEQ_TABLE in translation file\n";}


########################
# read the SEQ_TABLE

$index = 0;
#$max_seq_len = 0; # for pretty printing
$found = 0;
$seq_table = 0;
$pattern = '^>\s*"([^"]*)"\s*"([^"]*)"\s*"([^"]*)"\s*"([^"]*)"';

while (<INFILE> ){
    if (/^\s*END_SEQ_TABLE/){
	    print "line $.: END_SEQ_TABLE found\n" if $do_debug;
	    $found = 1;
	    $seq_table = $index;
	    last;}
        elsif (($temp1,$temp2,$temp3,$temp4) = /$pattern/){
#	    $max_seq_len = length($temp1) if $max_seq_len < length($temp1);
	    $seq_table[$index]= join('"',$temp1,$temp4);
	     # the " as seperator is perfect since it cannot occur inside the strings
	     # backslashes are only expanded in the latex replacement
	    printf "line $.: \"%s\" \t\t \"%s\"\n", 
	           $temp3, $temp4 if $do_ddebug;
	    $index +=1;
	}
}

if ($found == 0) {
    die "\ncan't find END_SEQ_TABLE in translation file\n";}
    else {print "computed index for SEQ_TABLE is $seq_table\n"  if $do_debug;
#          print "maximal length of entries is $max_seq_len\n"   if $do_ddebug;
}

########################
# we reached the end of the translation file

print "\nprocessing of translation file completed\n" if $do_debug;

########################
# close the handle for config file
close(INFILE);
print "closed translation file\n" if $do_debug;

########################
# open the keymap file

open(INFILE,$keymap_file) || die "can't open $keymap_file: $!\n";
print "opened keymap file,\nprocessing\n" if $do_debug;

########################
# search for PACK

$pack = $ENV{'ISABELLE8BIT'};

if ($pack eq "") {
    die "\ncan't find label PACK in keymap file\n";}

if (! (-d $pack)){
    die "\nPACK is not a directory\n";}


########################
# configuration of KEY_MAP
print "\nsetup for KEY_MAP\n" if $do_debug;

########################
# search for BEGIN_KEY_MAP

$found = &look_for_label('^\s*BEGIN_KEY_MA(P)',"BEGIN_KEY_MAP");

if ($found eq "") {
    die "\ncan't find BEGIN_KEY_MAP in keymap file\n";}
				 
########################
# read the KEY_MAP

$index = 0;
$found = 0;
$end_key_map = 0; 
$pattern = 
'^\s*MOD\s*(None|Mod1|Mod2|Mod4|Shift|Ctrl)\s*KEY\s*([a-zA-Z]+|F\d{1,2})\s*CODE\s*([0-9a-fA-F][0-9a-fA-F](\s*,\s*[0-9a-fA-F][0-9a-fA-F])*)\s*$';

#'

while (<INFILE> ){
    if (/^\s*END_KEY_MAP/){
	    print "line $.: END_KEY_MAP found\n" if $do_debug;
	    $found = 1;
	    $end_key_map = $index - 1;
	    last;}
    elsif (($modifiers,$key,$codeseq) = /$pattern/){
	$key_map[$index]= join(':',$modifiers,$key,$codeseq);
	print "line $.: \"$key_map[$index]\"\n" if $do_ddebug;
	$index +=1;
    }
    else {
	print "Is this a comment? line $.: $_\n" ;}
}
if (!$found){
	die "\ncan't find END_KEY_MAP in keymap file\n";}

if ($end_low_table < $start_low_table){
	die "\nNo entries in KEY_MAP\n";}
    else {print 
	"computed index for END_KEY_MAP is $end_key_map\n" if $do_debug;}

########################
# we reached the end of the keymap file

print "\nprocessing of keymap file completed\n" if $do_debug;

########################
# close the handle for config file 
close(INFILE);
print "closed keymap file\n" if $do_debug;

#######################################################################
# generate the documentation
#######################################################################

########################
# change to directory `doc' 
				 
chdir $pack."/doc" || die "can't cd to directory $pack/doc: $!\n";


########################
# open the file `fontindex.tex' 
print "generating LaTeX file `fontindex.tex'\n" if $do_debug;

$filename = "fontindex.tex";
open(OUTFILE,">$filename") || die "can't open file $filename: $!\n";
print "opened $filename for writing\n" if $do_ddebug;


########################
# generate the fonttable
# 

#initialize the fonttable

$index = $start_hi_table;
while ($index <= $end_hi_table) {
    $fonttable[$index - $start_hi_table]=$hi_table[$index - $start_hi_table]; 
    $index++;
}

# append information from the keymap

$index = 0;
while ($index <= $end_key_map) {
    ($mod,$key,$code) = split(/:/,$key_map[$index]);
    # split the sequence of key codes
    @codelist = split(/\s*,\s*/,$code);

    if ($#codelist == 0 && # not a code sequence
        $start_hi_table <= hex($codelist[0]) && 
        hex($codelist[0]) <= $end_hi_table ) { # we are in range of hi_table

      #translate the modifier
      if ($mod eq "None") { # delete if None modifier 
         $mod = "";}
      elsif ($mod eq "Mod1"){ 
         $mod = "Meta";}
      elsif ($mod eq "Mod2"){
         $mod = "Alt";}
      elsif ($mod eq "Mod4"){ 
         $mod = "AltGraph";}
      elsif ($mod eq "Ctrl"){ 
         $mod = "Ctrl";}

      $fonttable[hex($codelist[0]) - $start_hi_table] = join('"',
            split(/\"/,$fonttable[hex($codelist[0]) - $start_hi_table]),
            $mod." ".$key);
      }
    $index++;
}


## print the TeX prelude
if ($latex2e){
printf OUTFILE 
'\documentclass[a4paper,11pt]{article}
\usepackage{latexsym,amssymb,supertab}

\begin{document}

\begin{center}
{\Large 
  Description of Isabelle Font \\\\ 
      Indexed by Code}\\\\
  Date: \today 

\vspace*{.5cm}

\tablehead{\hline
Oct & Dec & Hex & ASCII & \LaTeX & Key Sequence\\\\
\hline}
\tabletail{\hline}

\begin{supertabular}{|l|l|l|l|l|l|}
';
}
else{
printf OUTFILE 
'\documentstyle[a4,11pt,latexsym,amssymb,supertab]{article}
\begin{document}

\begin{center}
{\Large 
  Description of Isabelle Font \\\\ 
      Indexed by Code}\\\\
  Date: \today 

\vspace*{.5cm}

\tablehead{\hline
Oct & Dec & Hex & ASCII & \LaTeX & Key Sequence\\\\
\hline}
\tabletail{\hline}

\begin{supertabular}{|l|l|l|l|l|l|}
';
}
## print the fonttable

$index = $start_hi_table;
while ($index <= $end_hi_table) {
    ($ascii,$latex,$keystring) = split(/\"/,
                                     $fonttable[$index - $start_hi_table],3);

    # generate List of Keystrokes
    @keylist = split(/\"/,$keystring);

    $keystring= shift(@keylist);
    foreach $string (@keylist){
   	$keystring .= ", $string";}

    if ($index == $end_hi_table) {
        $postfix = "\\\\";}
    else {$postfix = "\\nextline";}
       
   
    printf(OUTFILE "%o & %d & %x & %s & %s & %s$postfix\n", 
                 $index,
                 $index,
                 $index,
                 "\\verb*\"".$ascii."\"",
                 $latex,
                 $keystring);

    $index++;
}

## print rest of TeX
printf OUTFILE 
'\end{supertabular}
\end{center}
\end{document}
';

close(OUTFILE);
print "closed $filename\n" if $do_ddebug;

########################
# open the file `keyindex.tex' 
print "generating LaTeX file `keyindex.tex'\n" if $do_debug;

$filename = "keyindex.tex";
open(OUTFILE,">$filename") || die "can't open file $filename: $!\n";
print "opened $filename for writing\n" if $do_ddebug;


########################
# generate an assoc array of those lex-expressions in seq_table that consist
# purely of hexnumbers or graphical characters (with highest bit set). 
# These are candidates for the codesequences in key_map.
#
# This is just a simple heuristic!
# 

print "compute the assoc array of code sequences\n" if $do_ddebug;

$index = 0;
while ($index < $seq_table ) {
    ($temp1,$temp2) = split(/\"/,$seq_table[$index]); 
    if ($temp1 =~ /^(\\x[0-9a-fA-F][0-9a-fA-F])+$/){# filter out the pure hex sequences
       	$temp1 =~ s/\\x([0-9a-fA-F][0-9a-fA-F])/$1,/g;
	chop($temp1);
	print "found candidate: key $temp1  latex $temp2\n" if $do_ddebug;
	$assoc_seq_table{$temp1} = $temp2;}
    elsif ($temp1 =~ /^([\x80-\xff])+$/){# filter out the pure graphical characters
	$temp1 = unpack("H*",$temp1);
        $temp1 =~ /^([0-9a-f][0-9a-f])+$/;
       	$temp1 =~ s/([0-9a-f][0-9a-f])/$1,/g;
	chop($temp1);
	print "found candidate: key $temp1  latex $temp2\n" if $do_ddebug;
	$assoc_seq_table{$temp1} = $temp2;}

    $index++;
}

########################
# generate the keytable
# 

$index = 0;
while ($index <= $end_key_map) {
     ($mod,$key,$code) = split(/:/,$key_map[$index]);

     #translate the modifier `None' for sorting; a dirty trick
     if ($mod eq "None") { # delete if None modifier 
        $mod = "AAAA";}
     
     @codelist = split(/\s*,\s*/,$code);
     if ($#codelist != 0){ # we have  a code sequence, look up in assoc array
	 $latex = $assoc_seq_table{join(',',@codelist)};
	 if ($latex eq "") {# there was no assoc
	    $latex = "unknown";}
	}	 
     elsif ( $start_hi_table <= hex($codelist[0]) && 
             hex($codelist[0]) <= $end_hi_table ) {# we are in range of hi_table
       @temp4 = split(/\"/,$hi_table[hex($codelist[0]) - $start_hi_table]);
       $latex = pop(@temp4);}

     else { # we can"t associate a LaTeX code
	 $latex = "unknown";}

     $keytable[$index]= join('"',$mod,$key,join(',',@codelist),$latex);
     $index++;
}

########################
# sort the keytable
# 

@keytable = sort(sortbykey @keytable);


## print the TeX prelude
if ($latex2e){
printf OUTFILE 
'\documentclass[a4paper,11pt]{article}
\usepackage{latexsym,amssymb,supertab}

\begin{document}

\begin{center}
{\Large 
  Description of Keyboard Mapping\\\\
      Indexed by Key Sequence}\\\\
  Date: \today 

\vspace*{.5cm}

\tablehead{\hline
Key Sequence & Code Sequence in Hex & \LaTeX \\\\
\hline}
\tabletail{\hline}

\begin{supertabular}{|l|l|l|}
';
}
else {
printf OUTFILE 
'\documentstyle[a4,11pt,latexsym,amssymb,supertab]{article}
\begin{document}

\begin{center}
{\Large 
  Description of Keyboard Mapping\\\\
      Indexed by Key Sequence}\\\\
  Date: \today 

\vspace*{.5cm}

\tablehead{\hline
Key Sequence & Code Sequence in Hex & \LaTeX \\\\
\hline}
\tabletail{\hline}

\begin{supertabular}{|l|l|l|}
';
}
## print the keyboard mapping

$index = 0;
while ($index <= $end_key_map) {
    ($mod,$key,$code,$latex) = split(/\"/,$keytable[$index]);

    #translate the modifier
      if ($mod eq "AAAA") { # delete if AAAA rsp. None modifier 
         $mod = "";}
      elsif ($mod eq "Mod1"){ 
         $mod = "Meta";}
      elsif ($mod eq "Mod2"){
         $mod = "Alt";}
      elsif ($mod eq "Mod4"){ 
         $mod = "AltGraph";}
      elsif ($mod eq "Ctrl"){ 
         $mod = "Ctrl";}

    if ($index == $end_key_map) {
        $postfix = "\\\\";}
    else {$postfix = "\\nextline";}

    printf(OUTFILE "%s & %s & %s$postfix\n", 
                 $mod." ".$key,
                 $code,
	   $latex);

    $index++;
}


## print rest of TeX
printf OUTFILE 
'\end{supertabular}
\end{center}
\end{document}
';

close(OUTFILE);
print "closed $filename\n" if $do_ddebug;

########################
# open the file `fkmatrix.tex' 
print "generating LaTeX file `fkmatrix.tex'\n" if $do_debug;

$filename = "fkmatrix.tex";
open(OUTFILE,">$filename") || die "can't open file $filename: $!\n";
print "opened $filename for writing\n" if $do_ddebug;


########################
# generate the matrix for function key mappings
# 
# we support only documentation of keys F1 - F12 

# initialize the assoc array

$fkmat{"AAAA"} = join('"',(" "," "," "," "," "," "," "," "," "," "," "," "));
$fkmat{"Mod1"} = join('"',(" "," "," "," "," "," "," "," "," "," "," "," "));
$fkmat{"Mod2"} = join('"',(" "," "," "," "," "," "," "," "," "," "," "," "));
$fkmat{"Mod4"} = join('"',(" "," "," "," "," "," "," "," "," "," "," "," "));
$fkmat{"Ctrl"} = join('"',(" "," "," "," "," "," "," "," "," "," "," "," "));

print "building fkmatrix\n" if $do_ddebug;

$index = 0;
while ($index <= $end_key_map) {
    local (@keylist);

    ($mod,$key,$code,$latex) = split(/\"/,$keytable[$index]);

    if ($key =~ /^F\d{1,2}$/){ # key is a function key
	$key =~ s/^F(\d{1,2})$/$1/;
	@keylist = split(/\"/,$fkmat{$mod});
	if( 0<$key && $key<=12){
            # we support only F1 - F12
	    $keylist[$key-1]=$latex;}
	$fkmat{$mod} = join('"',@keylist);    
    }
    $index++;
}
print "fkmatrix completed\n" if $do_ddebug;

## print the TeX prelude
if ($latex2e){
printf OUTFILE 
'\documentclass[a4paper,11pt]{article}
\usepackage{latexsym,latexsym,amssymb,supertab}

\begin{document}

\begin{center}
{\Large 
  Keyboard Mapping for Function Keys F1 - F12}\\\\ 
  Date: \today 

\vspace*{.5cm}

\tablehead{\hline
Modifier & F1 &F2 &F3 &F4 &F5 &F6 &F7 &F8 &F9 & F10 &F11 &F12\\\\
\hline}
\tabletail{\hline}

\begin{supertabular}{|l|l|l|l|l|l|l|l|l|l|l|l|l|}
';}
else {
printf OUTFILE 
'\documentstyle[a4,11pt,latexsym,amssymb,supertab]{article}
\begin{document}

\begin{center}
{\Large 
  Keyboard Mapping for Function Keys F1 - F12}\\\\ 
  Date: \today 

\vspace*{.5cm}

\tablehead{\hline
Modifier & F1 &F2 &F3 &F4 &F5 &F6 &F7 &F8 &F9 & F10 &F11 &F12\\\\
\hline}
\tabletail{\hline}

\begin{supertabular}{|l|l|l|l|l|l|l|l|l|l|l|l|l|}
';
}
## print the matrix
printf(OUTFILE "None&%s\\nextline\n",
       join('&',split(/\"/,$fkmat{"AAAA"})));
printf(OUTFILE "\\hline\n");
printf(OUTFILE "Shift&%s\\nextline\n",
       join('&',split(/\"/,$fkmat{"Shift"})));
printf(OUTFILE "\\hline\n");
printf(OUTFILE "Ctrl&%s\\\\\n",
       join('&',split(/\"/,$fkmat{"Ctrl"})));
printf(OUTFILE "\\hline\n");
printf(OUTFILE "Alt&%s\\nextline\n",
       join('&',split(/\"/,$fkmat{"Mod2"})));
printf(OUTFILE "\\hline\n");
printf(OUTFILE "AltGraph&%s\\nextline\n",
       join('&',split(/\"/,$fkmat{"Mod4"})));
printf(OUTFILE "\\hline\n");
printf(OUTFILE "Meta&%s\\nextline\n",
       join('&',split(/\"/,$fkmat{"Mod1"})));

## print rest of TeX
printf OUTFILE 
'\end{supertabular}
\end{center}
\end{document}
';

close(OUTFILE);
print "closed $filename\n" if $do_ddebug;

########################
# execute  Makefile

print "\nexecuting Makefile\n" if $do_debug;
$status = system("make fontdocfiles") ;
if ($status) { die "\"make fontdocfiles\" executed abnormally: $!\n";}

#print "\nexecuting Makefile, cleaning up\n" if $do_debug;
#$status = system("make clean");
#if ($status) { die "\"make clean\" executed abnormally: $!\n";}

########################
# END of script
# 

print "\ngeneration of font and keymap documentation properly terminated\n\n";
exit(0);

#######################################################################
# subroutines
#######################################################################

sub look_for_value {
    local ($pattern,$label) = @_;
    local ($temp) = "";

    while (<INFILE> ){
	if (($temp) = /$pattern/){
	    print "line $.: $label is $temp\n" if $do_debug;
	    last;}
    }
    return $temp;
}


sub look_for_label {
    local ($pattern,$label) = @_;
    local ($temp) = "";

    while (<INFILE> ){
	if (($temp) = /$pattern/){
	    print "line $.: $label found\n" if $do_debug;
	    last;}
    }
    return $temp;
}

sub replicate_until {
    local ($pattern,$label) = @_;
    local ($temp) = "";

    while (<INFILE> ){
	if (($temp) = /$pattern/){
	    print "line $.: $label found\n" if $do_debug;
	    last;}
	else {printf(OUTFILE "%s",$_);}
    }
    return $temp;
}

sub skip_until {
    local ($pattern,$label) = @_;
    local ($temp) = "";

    while (<INFILE> ){
	if (($temp) = /$pattern/){
	    print "line $.: $label found\n" if $do_debug;
	    last;}
    }
    return $temp;
}

sub double_bs {
    local ($string) = @_;
    local ($element);
    local (@temp1);
    local (@temp2) = (); 

    # find the hex-numbers
    @temp1 = split(/(\\x[0-9a-fA-F][0-9a-fA-F])/,$string);

    #duplicate all backslashes in elements which are not hexnumbers
    while(@temp1) { 
	$element = shift(@temp1);
	if ($element =~ /\\x[0-9a-fA-F][0-9a-fA-F]/){
	    push(@temp2,$element);} 
	else{
	    $element =~ s/\\/\\\\/g;
	    push(@temp2,$element);}
    }
    return (join('',@temp2));
}

sub squeeze_bs {
    local ($string) = @_;

    $string =~ s/\\\\/\\/g;
    return $string;
}

sub show_blanks {
    local ($string) = @_;

    $string =~ s/ /\\_/g;
    return $string;
}

sub sortbykey {
    local ($mod1,$key1,$code1,$latex1) = split(/\"/,$a);
    local ($mod2,$key2,$code2,$latex2) = split(/\"/,$b);

    if ($mod1 eq $mod2){ # subsort by key 
	if ($key1 =~ /^F\d{1,2}$/){ # key1 is a function key
	    if ($key2 =~ /^F\d{1,2}$/){ # key2 is a function key too 
		$key1 =~ s/^F(\d{1,2})$/$1/;
		$key2 =~ s/^F(\d{1,2})$/$1/;
		return (int($key1) <=> int($key2));}
	    else {return 1;}  # function is always greater
	    } 
	elsif ($key2 =~ /^F\d{1,2}$/){ # key2 is a function key, key1 not
	      return -1;} # non function is always less
	else { # both are non function keys
	    return ($key1 cmp $key2);}
    }
    else { return ($mod1 cmp $mod2);}
}
###############################################################

    # These next few lines are legal in both Perl and nroff.

.00;                       # finish .ig
 
'di           \" finish diversion--previous line must be blank
.nr nl 0-1    \" fake up transition to first page again
.nr % 0         \" start at page 1
'; __END__ ##### From here on it's a standard manual page #####
