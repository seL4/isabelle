#!/usr/local/dist/DIR/perl4/bin/perl
'di';
'ig00';
###############################################
# Title:      Tools/8bit/perl/generators/gen-isa2latex
# ID:         $Id$
# Author:     Franz Regensburger
# Copyright   1996 TU Muenchen
#
# configures the converter isa2latex with user provided settings
#
# Franz Regensburger <regensbu@informatik.tu-muenchen.de> 8.3.95
# 
###############################################

# I like to see the output as it happens (flushed output)

$| = 1;

# cash current working directory 
require "pwd.pl";
&initpwd;

$initial_dir = $ENV{'PWD'};
$GMAKE= "gmake";

########################
# comand line processing
# processes all known switches and ingnores others.
# first non-switch which is the name of a text file is 
# interpreted as name of configuration file.
#

# initialize
$config_file="";
$do_debug = 0;
$do_ddebug = 0;
#$install_source = 0;
#$cleanup = 0;

while (@ARGV){
    $cur_arg = shift @ARGV;
    if ($cur_arg eq '-d')  {$do_debug = 1;}
    elsif ($cur_arg eq '-dd') {$do_debug = 1; $do_ddebug = 1;}
#    elsif ($cur_arg eq '-c')  {$cleanup = 1;}
#    elsif ($cur_arg eq '-s')  {$install_source = 1;}
    elsif ((-T $cur_arg) && !$config_file) {$config_file = $cur_arg;}
}

# complain if no configuration file is found

if ($config_file eq "") {
    print "\nno configuration file suplied or argument is not a text file\n\n";
    print "usage gen-isa2latex [-d -dd ] configfile\n", 
#    print "usage gen-isa2latex [-d -dd -s -c ] configfile\n", 
          "options must be separated by blanks!";
    die "\n";
}

print "debug mode is on\n" if $do_debug;
print "double debug mode is on\n" if $do_ddebug;
print "name of configuration file is $config_file\n" if $do_debug;

########################
# open the configuration file

open(CONFIG,$config_file) || die "can't open $config_file: $!\n";
print "opened configuration file,\nprocessing\n" if $do_debug;

########################
# search for general setup variables

print "\ngeneral setup\n" if $do_debug;

########################
# search for CONV_SOURCE_DIR

$conv_source_dir = 
    &look_for_value('^\s*CONV_SOURCE_DIR\s*"(.*)"',"CONV_SOURCE_DIR");

if ($conv_source_dir eq "") {
    die "\ncan't find CONV_SOURCE_DIR  in configuration file\n";}

if (! (-d $conv_source_dir)){
    die "\nCONV_SOURCE_DIR is not a directory\n";}

if (! (-r $conv_source_dir)){
    die "\nno read permission for directory CONV_SOURCE_DIR \n";}

#if ($install_source && !(-w $conv_source_dir)){
#    die "\noption -s used but no write permission for directory CONV_SOURCE_DIR\n";}


########################
# search for CONV_TEMP_DIR

#$conv_temp_dir = &look_for_value('^\s*CONV_TEMP_DIR\s*"(.*)"',"CONV_TEMP_DIR");

#if ($conv_temp_dir eq "") {
#    die "\ncan't find CONV_TEMP_DIR  in configuration file\n";}

#if (! (-d $conv_temp_dir)){
#    die "\nCONV_TEMP_DIR is not a directory\n";}

#if (!(-r $conv_temp_dir && -w $conv_temp_dir && -x $conv_temp_dir)){
#    die "\nneed read, write and execute permission for directory CONV_TEMP_DIR\n";}


########################
# search for CONV_SUB_DIR

#$conv_sub_dir = &look_for_value('^\s*CONV_SUB_DIR\s*"(.*)"',"CONV_SUB_DIR");

#if ($conv_sub_dir eq "") {
#    die "\ncan't find CONV_SUB_DIR  in configuration file\n";}

########################
# process switsch -c for cleanup

#if ($cleanup) { # cleanup $conv_sub_dir
#    chdir $conv_temp_dir || die "can't cd to $conv_temp_dir: $!\n";
#    $status = system("rm -rf $conv_sub_dir/*; rmdir $conv_sub_dir");
#    if ($status) {die "can't remove subdirectory $conv_sub_dir: $!\n";}
#    print "cleanup done, exit configuration script\n";
#    exit(0);
#}


########################
# configuration of LOW_TABLE
print "\nsetup for LOW_TABLE\n" if $do_debug;

########################
# search for START_LOW_TABLE

$start_low_table = 
    &look_for_value('^\s*START_LOW_TABLE\s*"(\d+)"',"START_LOW_TABLE");

if ($start_low_table eq "") {
    die "\ncan't find START_LOW_TABLE in configuration file\n";}

if ($start_low_table < 32 || 127 < $start_low_table) {
    die "\nSTART_LOW_TABLE not in range 32 .. 127\n";}


########################
# search for BEGIN_LOW_TABLE

$found = &look_for_label('^\s*BEGIN_LOW_TABL(E)',"BEGIN_LOW_TABLE");

if ($found eq "") {
    die "\ncan't find BEGIN_LOW_TABLE in configuration file\n";}

########################
# read the LOW_TABLE

$index = 0;
$found = 0;
$end_low_table = 0;
$pattern = '^>\s*"([^"]*)"';

while (<CONFIG> ){
    if (/^\s*END_LOW_TABLE/){
	    print "line $.: END_LOW_TABLE found\n" if $do_debug;
	    $found = 1;
	    $end_low_table = $start_low_table + $index - 1;
	    last;}
    elsif (($temp) = /$pattern/){
	$low_table[$index]= &double_bs($temp);
	 # backslashes are duplicated
	print "line $.: \"$low_table[$index]\"\n" if $do_ddebug;
	$index +=1;
    }
}
if (!$found){
	die "\ncan't find END_LOW_TABLE in configuration file\n";}

if ($end_low_table < $start_low_table || 127 < $end_low_table){
	die "\nEND_LOW_TABLE $end_low_table not in range $start_low_table .. 127\n";}
    else {print 
	"computed index for END_LOW_TABLE is $end_low_table\n" if $do_debug;}

########################
# configuration of HI_TABLE
print "\nsetup for HI_TABLE\n" if $do_debug;

########################
# search for START_HI_TABLE
#
$start_hi_table = 
    &look_for_value('^\s*START_HI_TABLE\s*"(\d+)"',"START_HI_TABLE");

if ($start_hi_table eq "") {
    die "\ncan't find START_HI_TABLE in configuration file\n";}

if ($start_hi_table < 128 || 255 < $start_hi_table) {
    die "\nSTART_HI_TABLE not in range 128 .. 255\n";}

########################
# search for BEGIN_HI_TABLE

$found = &look_for_label('^\s*BEGIN_HI_TABL(E)',"BEGIN_HI_TABLE");

if ($found eq "") {
    die "\ncan't find BEGIN_HI_TABLE in configuration file\n";}

########################
# read the HI_TABLE

$index = 0;
$max_hi_len1 = 0; # for pretty printing
$max_hi_len2 = 0; # for pretty printing
$max_hi_len3 = 0; # for pretty printing
$found = 0;
$end_hi_table = 0;
$pattern = '^>\s*"([^"]*)"\s*"([^"]*)"\s*"([^"]*)"';

while (<CONFIG> ){
    if (/^\s*END_HI_TABLE/){
	    print "line $.: END_HI_TABLE found\n" if $do_debug;
	    $found = 1;
	    $end_hi_table = $start_hi_table + $index - 1;
	    last;}
    elsif (($temp_1,$temp_2,$temp_3) = /$pattern/){
	$temp1 =            $temp_1 ;
	$temp2 = &double_bs($temp_2);
	$temp3 = &double_bs($temp_3);
	$max_hi_len1 = length($temp1) if $max_hi_len1 < length($temp1);
	$max_hi_len2 = length($temp2) if $max_hi_len2 < length($temp2);
	$max_hi_len3 = length($temp3) if $max_hi_len3 < length($temp3);
	$hi_table[$index]= join('"',$temp1, $temp2, $temp3);
	# the " as seperator is perfect since it cannot occur inside the strings
	# backslashes are duplicated
	printf "line $.: \"%s\" \t\t \"%s\" \t\t \"%s\"\n", 
	                 $temp1, $temp2, $temp3          if $do_ddebug;
	$index +=1;
    }
}

if (!$found){
	die "\ncan't find END_HI_TABLE in configuration file\n";}

if ($end_hi_table < $start_hi_table || 255 < $end_hi_table ){
	die "\nEND_HI_TABLE $end_hi_table not in range $start_low_table .. 255\n";}
else 
  {print "computed index for END_HI_TABLE is $end_hi_table\n"  if $do_debug; }



########################
# configuration of SEQ_TABLE
print "\nsetup for SEQ_TABLE\n" if $do_debug;

########################
# search for BEGIN_SEQ_TABLE

$found = &look_for_label('^\s*BEGIN_SEQ_TABL(E)',"BEGIN_SEQ_TABLE");

if ($found eq "") {
    die "\ncan't find BEGIN_SEQ_TABLE in configuration file\n";}


########################
# read the SEQ_TABLE

$index = 0;
$max_seq_len1 = 0; # for pretty printing
$max_seq_len2 = 0; # for pretty printing
$max_seq_len3 = 0; # for pretty printing
$max_seq_len4 = 0; # for pretty printing
$found = 0;
$seq_table = 0;
$pattern = '^>\s*"([^"]*)"\s*"([^"]*)"\s*"([^"]*)"\s*"([^"]*)"';

while (<CONFIG> ){
    if (/^\s*END_SEQ_TABLE/){
	    print "line $.: END_SEQ_TABLE found\n" if $do_debug;
	    $found = 1;
	    $seq_table = $index;
	    last;}
        elsif (($temp_1,$temp_2,$temp_3,$temp_4) = /$pattern/){
	    $temp1 =            $temp_1 ;
	    $temp2 =            $temp_2 ;
	    $temp3 = &double_bs($temp_3) ;
	    $temp4 = &double_bs($temp_4);
	    $max_seq_len1 = length($temp1) if $max_seq_len1 < length($temp1);
	    $max_seq_len2 = length($temp2) if $max_seq_len2 < length($temp2);
	    $max_seq_len3 = length($temp4) if $max_seq_len3 < length($temp3);
	    $max_seq_len4 = length($temp3) if $max_seq_len4 < length($temp4);
	    $seq_table[$index]= join('"',$temp1, $temp2, $temp3, $temp4);
	     # the " as seperator is perfect since it cannot occur inside the strings
	     # backslashes are only expanded in the latex replacement
	    printf "line $.: \"%s\" \t\t \"%s\" \t\t \"%s\" \t\t \"%s\"\n", 
	                     $temp1, $temp2, $temp3, $temp4   if $do_ddebug;
	    $index +=1;
	}
}

if ($found == 0) {
    die "\ncan't find END_SEQ_TABLE in configuration file\n";}
else {print "computed index for SEQ_TABLE is $seq_table\n"  if $do_debug; }


########################
# we reached the end of the configuration file

print "\nprocessing of configuration file completed\n" if $do_debug;

########################
# close the handle for config file
close(CONFIG);
print "closed configuration file\n" if $do_debug;

#######################################################################
# copy sources and modify them
#######################################################################

########################
# change to temporary directory, 
# make subdir and copy sources
# change to subdir

#print "\ncopying sources\n" if $do_debug;

#chdir $conv_temp_dir || die "can't cd to $conv_temp_dir: $!\n";

# cleanup if directory exists

#if (-d $conv_sub_dir){ # directory exists 
#    $status = system("rm -rf $conv_sub_dir/*; rmdir $conv_sub_dir");
#    if ($status) {die "can't remove subdirectory $conv_sub_dir: $!\n";}
#}

# make the new sub dir

#mkdir($conv_sub_dir,0755) || die "can't create subdirectory $conv_sub_dir: $!\n";

#$status = system("cp -r $conv_source_dir/* $conv_sub_dir") ;
#if ($status) { die "can't copy files from CONV_SOURCE_DIR to CONV_SUB_DIR: $!\n";}

#chdir $conv_sub_dir || die "can't cd to $conv_sub_dir: $!\n";
 chdir $conv_source_dir || die "can't cd to $conv_source_dir: $!\n";

print "\nconfiguring sources\n" if $do_debug;

########################
# configure conv-defs.h
# 

$filename = "conv-defs.h";

print "\nconfiguring $filename\n" if $do_debug;

open(INFILE ,$filename) || die "can't open $filename in CONV_SOURCE_DIR: $!\n";
print "opened $filename for reading\n" if $do_ddebug;
open(OUTFILE,">tmp.txt") || die "can't open temporary file tmp.txt: $!\n";
print "opened tmp.txt for writing\n" if $do_ddebug;

$found = &replicate_until('^\s*\/\*\s*BEGIN\s*gen-isa2late(x)','BEGIN gen-isa2latex');
if ($found eq "") {
    die "\ncan't find BEGIN gen-isa2latex\n";}

## replace
printf(OUTFILE "%s\n", "/* BEGIN gen-isa2latex */");
printf(OUTFILE "#define START_LOW_TABLE %s\n", $start_low_table);
printf(OUTFILE "#define END_LOW_TABLE   %s\n", $end_low_table);
printf(OUTFILE "#define START_HI_TABLE  %s\n", $start_hi_table);
printf(OUTFILE "#define END_HI_TABLE    %s\n", $end_hi_table);
printf(OUTFILE "#define SEQ_TABLE       %s\n", $seq_table);
printf(OUTFILE "%s\n", "/* END gen-isa2latex */");

$found = &skip_until('^\s*\/\*\s*END\s*gen-isa2late(x)','END gen-isa2latex');
if ($found eq "") {
    die "\ncan't find END gen-isa2latex\n";}

## the rest
while (<INFILE> ){printf(OUTFILE "%s",$_);}

close(INFILE);
close(OUTFILE);
print "closed $filename and tmp.txt\n" if $do_ddebug;

$status = system("cp tmp.txt $filename") ;
if ($status) { die "can't copy tmp.txt to $filename: $!\n";}

########################
# configure conv-tables.h
# 

$filename = "conv-tables.h";

print "\nconfiguring $filename\n" if $do_debug;

open(INFILE ,$filename) || die "can't open $filename in CONV_SOURCE_DIR: $!\n";
print "opened $filename for reading\n" if $do_ddebug;
open(OUTFILE,">tmp.txt") || die "can't open temporary file tmp.txt: $!\n";
print "opened tmp.txt for writing\n" if $do_ddebug;

### LOW TABLE
$found = &replicate_until('^\s*\/\*\s*BEGIN_OF_LOW_TABL(E)','BEGIN_OF_LOW_TABLE');
if ($found eq "") {
    die "\ncan't find BEGIN_OF_LOW_TABLE\n";}

## replace
printf(OUTFILE "%s\n", "/* BEGIN_OF_LOW_TABLE */");
printf(OUTFILE "%s\n",
       "char *translationTableLow[END_LOW_TABLE - START_LOW_TABLE + 1] = {");
$index = $start_low_table;
$sep = ",\n";
while ($index <= $end_low_table) {
    $sep = "\n" if $index == $end_low_table;   
    printf(OUTFILE "   \"%s\"".$sep, $low_table[$index - $start_low_table]);
    $index++;
}
printf(OUTFILE "%s\n","};");
printf(OUTFILE "%s\n", "/* END_OF_LOW_TABLE */");

$found = &skip_until('^\s*\/\*\s*END_OF_LOW_TABL(E)','END_OF_LOW_TABLE');
if ($found eq "") {
    die "\ncan't find END_OF_LOW_TABLE\n";}

### HI TABLE
$found = &replicate_until('^\s*\/\*\s*BEGIN_OF_HI_TABL(E)','BEGIN_OF_HI_TABLE');
if ($found eq "") {
    die "\ncan't find BEGIN_OF_HI_TABLE\n";}

## replace
printf(OUTFILE "%s\n", "/* BEGIN_OF_HI_TABLE */");
printf(OUTFILE "%s\n",
       "char *translationTableHi[END_HI_TABLE - START_HI_TABLE + 1][2] = {");

$index = $start_hi_table;
$sep = ",\n";
while ($index <= $end_hi_table) {
    $sep = "\n" if $index == $end_hi_table;   
    ($temp1,$temp2,$temp3) = split(/\"/,$hi_table[$index - $start_hi_table]); 
    printf(OUTFILE "   {%-".($max_hi_len2+3)."s,%s}".$sep,
	   "\"".$temp2."\"","\"".$temp3."\"");
    $index++;
}
printf(OUTFILE "%s\n","};");
printf(OUTFILE "%s\n", "/* END_OF_HI_TABLE */");

$found = &skip_until('^\s*\/\*\s*END_OF_HI_TABL(E)','END_OF_HI_TABLE');
if ($found eq "") {
    die "\ncan't find END_OF_HI_TABLE\n";}

### SEQ TABLE
$found = &replicate_until('^\s*\/\*\s*BEGIN_OF_SEQ_TABL(E)','BEGIN_OF_SEQ_TABLE');
if ($found eq "") {
    die "\ncan't find BEGIN_OF_SEQ_TABLE\n";}

## replace
printf(OUTFILE "%s\n", "/* BEGIN_OF_SEQ_TABLE */");
printf(OUTFILE "%s\n",
       "char *translationTableSeq[SEQ_TABLE][2] = {");

$index = 0;
$sep = ",\n";
while ($index <= $seq_table - 1) {
    $sep = "\n" if $index == $seq_table - 1;   
    ($temp1,$temp2,$temp3,$temp4) = split(/\"/,$seq_table[$index]); 
    printf(OUTFILE "   {%-".($max_seq_len3+3)."s,%s}".$sep,
	   "\"".$temp3."\"","\"".$temp4."\"");
    $index++;
}
printf(OUTFILE "%s\n","};");
printf(OUTFILE "%s\n", "/* END_OF_SEQ_TABLE */");

$found = &skip_until('^\s*\/\*\s*END_OF_SEQ_TABL(E)','END_OF_SEQ_TABLE');
if ($found eq "") {
    die "\ncan't find END_OF_SEQ_TABLE\n";}
## the rest
while (<INFILE> ){printf(OUTFILE "%s",$_);}

close(INFILE);
close(OUTFILE);
print "closed $filename and tmp.txt\n" if $do_ddebug;

$status = system("cp tmp.txt $filename") ;
if ($status) { die "can't copy tmp.txt to $filename: $!\n";}

########################
# configure conv-lex.x
# 

$filename = "conv-lex.x";

print "\nconfiguring $filename\n" if $do_debug;

open(INFILE ,$filename) || die "can't open $filename in CONV_SOURCE_DIR: $!\n";
print "opened $filename for reading\n" if $do_ddebug;
open(OUTFILE,">tmp.txt") || die "can't open temporary file tmp.txt: $!\n";
print "opened tmp.txt for writing\n" if $do_ddebug;


### HI TABLE
$found = &replicate_until('^\s*\/\*\s*BEGIN_OF_HI_TABL(E)','BEGIN_OF_HI_TABLE');
if ($found eq "") {
    die "\ncan't find BEGIN_OF_HI_TABLE\n";}
## replace
printf(OUTFILE "%s\n", "  /* BEGIN_OF_HI_TABLE */");
$index = $start_hi_table;
while ($index <= $end_hi_table) {
    ($temp1,$temp2,$temp3) = split(/\"/,$hi_table[$index-$start_hi_table]); 
    printf(OUTFILE "<ISAA>%-".($max_hi_len1+3)."s\t"."put((char)%d,FALSE,0);\n",
	   $temp1,$index);
    $index++;
}
printf(OUTFILE "%s\n", "  /* END_OF_HI_TABLE */");
$found = &skip_until('^\s*\/\*\s*END_OF_HI_TABL(E)','END_OF_HI_TABLE');
if ($found eq "") {
    die "\ncan't find END_OF_SEQ_TABLE\n";}


### SEQ TABLE
$found = &replicate_until('^\s*\/\*\s*BEGIN_OF_SEQ_TABL(E)','BEGIN_OF_SEQ_TABLE');
if ($found eq "") {
    die "\ncan't find BEGIN_OF_SEQ_TABLE\n";}
## replace
printf(OUTFILE "%s\n", "  /* BEGIN_OF_SEQ_TABLE */");
$index = 0;
while ($index < $seq_table ) {
    ($temp1,$temp2,$temp3,$temp4) = split(/\"/,$seq_table[$index]); 
    printf(OUTFILE "<ISA,ISAA>%-".($max_seq_len1+3)."s\t"."put((char)32,TRUE,%d);\n",
	   $temp1,$index);
    printf(OUTFILE "<ISAA>%-".($max_seq_len2+3)."s    \t"."put((char)32,TRUE,%d);\n",
	   $temp2,$index);
    $index++;
}
printf(OUTFILE "%s\n", "  /* END_OF_SEQ_TABLE */");
$found = &skip_until('^\s*\/\*\s*END_OF_SEQ_TABL(E)','END_OF_SEQ_TABLE');
if ($found eq "") {
    die "\ncan't find END_OF_SEQ_TABLE\n";}


## the rest
while (<INFILE> ){printf(OUTFILE "%s",$_);}

close(INFILE);
close(OUTFILE);
print "closed $filename and tmp.txt\n" if $do_ddebug;

$status = system("cp tmp.txt $filename") ;
if ($status) { die "can't copy tmp.txt to $filename: $!\n";}

########################
# execute  Makefile
# 
print "\nexecuting Makefile\n" if $do_debug;
$status = system($GMAKE) ;
if ($status) { die "\"".$GMAKE."\" executed abnormally: $!\n";}

#$status = system("cp $conv_temp_dir/$conv_sub_dir/isa2latex $conv_source_dir");
#    if ($status) { die "can't copy binary file to CONV_SOURCE_DIR: $!\n";}

#print "\nexecuting Makefile, cleaning up\n" if $do_debug;
#$status = system($GMAKE." clean");
#if ($status) { die "\"".$GMAKE." clean\" executed abnormally: $!\n";}

#######################################################################
# process -s option
#######################################################################

#if ($install_source){
#    print "\ninstall new files in CONV_SOURCE_DIR due to -s option\n" if $do_debug;
#    $status = system("cp -r $conv_temp_dir/$conv_sub_dir/* $conv_source_dir");
#    if ($status) { die "can't copy new files to CONV_SOURCE_DIR: $!\n";}

#    print "copied new files to CONV_SOURCE_DIR\n" if $do_debug;

#    chdir $initial_dir || die "can't cd to initial dir $initial_dir: $!\n";
#    $status = system("cp $config_file $conv_source_dir");
#    if ($status) { die "can't copy configuration file to CONV_SOURCE_DIR: $!\n";}
#
#   print "copied configuration file to CONV_SOURCE_DIR\n" if $do_debug;
   
#}


########################
# END of script
# 

print "\nconfiguration and generation of isa2latex properly terminated\n".
      "have fun with isa2latex!\n\n";
exit(0);

#######################################################################
# subroutines
#######################################################################

sub look_for_value {
    local ($pattern,$label) = @_;
    local ($temp) = "";

    while (<CONFIG> ){
	if (($temp) = /$pattern/){
	    print "line $.: $label is $temp\n" if $do_debug;
	    last;}
    }
    return $temp;
}


sub look_for_label {
    local ($pattern,$label) = @_;
    local ($temp) = "";

    while (<CONFIG> ){
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

###############################################################

    # These next few lines are legal in both Perl and nroff.

.00;                       # finish .ig
 
'di           \" finish diversion--previous line must be blank
.nr nl 0-1    \" fake up transition to first page again
.nr % 0         \" start at page 1
'; __END__ ##### From here on it's a standard manual page #####
