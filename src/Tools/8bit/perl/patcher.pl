#!/usr/local/dist/DIR/perl4/bin/perl
'di';
'ig00';
#
# $Header$
#
# $Log$
# Revision 1.1  1996/06/25 15:44:59  oheimb
# Initial revision
#
# Revision 1.1.1.1  1996/06/25  13:58:24  oheimb
# Graphical 8bit Font Package imported, second attempt
#
#
# patcher
# Franz Regensburger <regensbu@informatik.tu-muenchen.de>
# 10.2.8.95
#
# last changed: 
#
# a universal patcher for text files
#
# don't use character @ in configfile

# I like to see the output as it happens (flushed output)

$| = 1;

# cash current working directory 
require "pwd.pl";
&initpwd;

########################
# comand line processing
# processes all known switches and ingnores others.
# first non-switch which is the name of a text file is 
# interpreted as name of the configuration file
#

# initialize
$config_file="";

$do_debug = 0;
$do_ddebug = 0;

while (@ARGV){
    $cur_arg = shift @ARGV;
    if ($cur_arg eq '-d')  {$do_debug = 1;}
    elsif ($cur_arg eq '-dd') {$do_debug = 1; $do_ddebug = 1;}
    elsif ((-T $cur_arg) && !$config_file) {$config_file = $cur_arg;}
}

# complain if no config file is found

if ($config_file eq "") {
    print "\nno config file suplied or argument is not a text file\n\n";
    print "usage patcher [-d -dd ] config-file \n", 
          "options must be seperated by blanks!";
    die "\n";
}

print "debug mode is on\n" if $do_debug;
print "double debug mode is on\n" if $do_ddebug;
print "name of config file is $config_file\n" if $do_debug;

########################
# open the config file

open(INFILE,$config_file) || die "can't open $config_file: $!\n";
print "opened config file,\nprocessing\n" if $do_ddebug;

########################
# look for stem of filenames
$stem = &look_for_value('^\s*STEM\s*"(.*)"',"STEM");

if ($stem eq "") {
    die "\ncan't find STEM  in configuration file\n";}

if (! (-d $stem)){
    die "\nSTEM is not a directory\n";}

if (! (-r $stem)){
    die "\nno read permission for directory STEM \n";}


########################
# read in the configuration commands
print "\nreading commands\n" if $do_debug;

$index = 0;
$end_config = 0;
$pattern1 = '^\s*(ADD|EXTRACT)\s*([^\s]*)\s*IN\s*([^\s]*)\s*BETWEEN\s*"([^"]*)"\s*"([^"]*)"';
$pattern2 = '^\s*(CLEAN)\s*IN\s*([^\s]*)\s*BETWEEN\s*"([^"]*)"\s*"([^"]*)"';

#$pattern = '^#\s*([^#]*)#\s*([^#]*)#\s*([^#]*)#\s*([^#]*)#\s*([^#]*)';

while (<INFILE> ){
    if (($cmd,$patchfile,$infile,$pragma1,$pragma2) = /$pattern1/){
	$config_table[$index]= join('@',$cmd,$patchfile,$infile,$pragma1,$pragma2);
	# the @ is used as seperator
	printf "line $.: %s %s %s %s %s\n", 
	     $cmd,$patchfile,$infile,$pragma1,$pragma2 if $do_ddebug;
	$index +=1;
    }
  elsif (($cmd,$infile,$pragma1,$pragma2) = /$pattern2/){
	$config_table[$index]= join('@',$cmd,"",$infile,$pragma1,$pragma2);
	# the @ is used as seperator
	printf "line $.: %s %s %s %s\n", 
	     $cmd,$infile,$pragma1,$pragma2 if $do_ddebug;
	$index +=1;
    }
} #while

if ($index > 0) {
	$end_config = $index - 1;}
   else {$end_config = -1;}	

print "there were  $index commands found\n"  if $do_debug;

########################
# close the handle for the config file
close(INFILE);
print "closed config file\n\n" if $do_debug;


########################
# do all the commands
print "processing all the commands\n" if $do_debug;

$index = 0;
while ($index <= $end_config) {
    ($cmd,$patchfile,$infile,$pragma1,$pragma2) =
    split(/@/,$config_table[$index]); 
    print "current command is:\n" if $do_debug;
    printf " %s %s %s %s %s\n", 
	     $cmd,$patchfile,$infile,$pragma1,$pragma2 if $do_debug;

$filename = $stem.$infile;
$tempfile = $stem."patcher.tmp";
$thepatchfile = $stem.$patchfile;

open(INFILE ,$filename) || die "can't open $filename: $!\n";
print "opened $filename for reading\n" if $do_ddebug;

if ( $cmd eq "ADD" ){
open(PATCHFILE,$thepatchfile) || die "can't open $thepatchfile: $!\n";
print "opened $thepatchfile for reading\n" if $do_ddebug;
}

if ( $cmd eq "EXTRACT" ){
open(PATCHFILE,">".$thepatchfile) || die "can't open $thepatchfile: $!\n";
print "opened $thepatchfile for writing\n" if $do_ddebug;
}

open(OUTFILE,">".$tempfile) || die "can't open temporary file $tempfile: $!\n";
print "opened $tempfile for writing\n" if $do_ddebug;

$found = &replicate_until($pragma1);
if ($found eq "") {die "\ncan't find $pragma1\n";}

if ( $cmd eq "ADD" ){
    while (<PATCHFILE> ){
	printf(OUTFILE "%s",$_);
    }
}
if ( $cmd eq "EXTRACT" ){
    while (<INFILE> ){
	printf(OUTFILE "%s",$_);
	if (/$pragma2/){
	    last;}
	printf(PATCHFILE "%s",$_);
    }
}
else {
    $found = &skip_until($pragma2);
    if ($found eq "") {die "\ncan't find $pragma2\n";}
}

# print the rest
while (<INFILE> ){
	printf(OUTFILE "%s",$_);
    }

close(INFILE);
close(PATCHFILE) if $cmd eq "ADD" | $cmd eq "EXTRACT";
close(OUTFILE);
print "closed the files\n" if $do_ddebug;

$status = system("cp $tempfile $filename") ;
if ($status) { die "can't copy $tempfile to $filename: $!\n";}


    $index += 1;
}

# erase the patcher.tmp file

$status = system("rm $tempfile") ;
if ($status) { die "can't erase $tempfile: $!\n";}


########################
# END of script
# 

print "\nprogram patcher properly terminated\n\n";
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
	if (/$pattern/){
	    $temp=true;
	    last;}
    }
    return $temp;
}

sub replicate_until {
    local ($pattern) = @_;
    local ($temp) = "";

    while (<INFILE> ){
	printf(OUTFILE "%s",$_);
	if (/$pattern/){
	    $temp = "true";
	    last;}
    }
    return $temp;
}

sub skip_until {
    local ($pattern) = @_;
    local ($temp) = "";

    while (<INFILE> ){
	if (/$pattern/){
	    printf(OUTFILE "%s",$_);  #restore last line
	    $temp = "true";
	    last;}
    }
    return $temp;
}
###############################################################

    # These next few lines are legal in both Perl and nroff.

.00;                       # finish .ig
 
'di           \" finish diversion--previous line must be blank
.nr nl 0-1    \" fake up transition to first page again
.nr % 0         \" start at page 1
'; __END__ ##### From here on it's a standard manual page #####
