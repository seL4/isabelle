#!/usr/local/dist/bin/perl
#
# gen-isaaxe
# Franz Regensburger <regensbu@informatik.tu-muenchen.de>
# 21.3.95
#
# last changed: 
#
# configures the script `isaaxe'
#
# 

# I like to see the output as it happens (flushed output)

$| = 1;

# cash current working directory 
require "pwd.pl";
&initpwd;

$initial_dir = $ENV{'PWD'};

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

while (@ARGV){
    $cur_arg = shift @ARGV;
    if ($cur_arg eq '-d')  {$do_debug = 1;}
    elsif ($cur_arg eq '-dd') {$do_debug = 1; $do_ddebug = 1;}
    elsif ((-T $cur_arg) && !$config_file) {$config_file = $cur_arg;}
}


# complain if no configuration file is found

if ($config_file eq "") {
    print "\nno configuration file suplied or argument is not a text file\n\n";
    print "usage gen-isaaxe [-d -dd] configfile\n", 
          "options must be seperated by blanks!";
    die "\n";
}

print "debug mode is on\n" if $do_debug;
print "double debug mode is on\n" if $do_ddebug;
print "name of configuration file is $config_file\n" if $do_debug;

########################
# open the configuration file

open(INFILE,$config_file) || die "can't open $config_file: $!\n";
print "opened configuration file,\nprocessing\n" if $do_debug;

########################
# search for general setup variables

print "\ngeneral setup\n" if $do_debug;

########################
# search for PACK

$pack = $ENV{'ISABELLE8BIT'};

if ($pack eq "") {
    die "\ncan't find label PACK in configuration file\n";}

if (! (-d $pack)){
    die "\nPACK is not a directory\n";}

########################
# search for AXE_DIR

#$axe_dir = &look_for_value('^\s*AXE_DIR\s*"(.*)"',"AXE_DIR");

#if ($axe_dir eq "") {
#    die "\ncan't find AXE_DIR  in configuration file\n";}


#if (!(-r $pack."/".$axe_dir && -w $pack."/".$axe_dir && -x $pack."/".$axe_dir)){
#    die "\nneed read, write and execute permission for directory AXE_DIR\n";}

$axe_dir = "axe";

########################
# configuration of KEY_MAP
print "\nsetup for KEY_MAP\n" if $do_debug;

########################
# search for BEGIN_KEY_MAP

$found = &look_for_label('^\s*BEGIN_KEY_MA(P)',"BEGIN_KEY_MAP");

if ($found eq "") {
    die "\ncan't find BEGIN_KEY_MAP in configuration file\n";}

########################
# read the KEY_MAP

$index = 0;
$found = 0;
$end_key_map = 0;
$pattern = 
'^\s*MOD\s*(None|Mod1|Mod2|Mod4|Shift|Ctrl)\s*KEY\s*([a-zA-Z]|F\d{1,2})\s*CODE\s*([0-9a-fA-F][0-9a-fA-F](\s*,\s*[0-9a-fA-F][0-9a-fA-F])*)\s*$';

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
	die "\ncan't find END_KEY_MAP in configuration file\n";}

if ($end_low_table < $start_low_table){
	die "\nNo entries in KEY_MAP\n";}
    else {print 
	"computed index for END_KEY_MAP is $end_key_map\n" if $do_debug;}

########################
# we reached the end of the configuration file

print "\nprocessing of configuration file completed\n" if $do_debug;

########################
# close the handle for config file
close(INFILE);
print "closed configuration file\n" if $do_debug;


#######################################################################
# modify the sources 
#######################################################################

########################
# change to directory AXE_DIR and open the file `isaaxe' 

chdir $pack."/".$axe_dir || die "can't cd to $axe_dir: $!\n";

########################
# configure isaaxe
# 

$filename = "isaaxe";
print "\nconfiguring $filename\n" if $do_debug;

open(INFILE ,$filename) || die "can't open $filename: $!\n";
print "opened $filename for reading\n" if $do_ddebug;
open(OUTFILE,">tmp.txt") || die "can't open temporary file tmp.txt: $!\n";
print "opened tmp.txt for writing\n" if $do_ddebug;

$found = &replicate_until('^\s*\x2aAxe\x2aed\x2e(translations)',
             '*Axe*ed.translations');

if ( $found eq "") {
    die "\ncan't find `*Axe*ed.translations'\n";}

# print header of table
printf(OUTFILE "*Axe*ed.translations: #override\\\n");

#print the table
$index = 0;
while ($index < $end_key_map) {
    $entry = &translate_entry(split(/:/,$key_map[$index]));
    printf(OUTFILE "\t%s \\n\\\n", $entry);
    $index += 1;
}
# print the last item
$entry = &translate_entry(split(/:/,$key_map[$index]));
printf(OUTFILE "\t%s \\\n", $entry);

# print footer of table
printf(OUTFILE "\" \$*\n");

close(INFILE);
close(OUTFILE);
print "closed $filename and tmp.txt\n" if $do_ddebug;

$status = system("cp tmp.txt $filename") ;
if ($status) { die "can't copy tmp.txt to $filename: $!\n";}

print "copied tmp.txt to $filename\n" if $do_ddebug;

$status = system("rm -f tmp.txt");
    if ($status) {die "can't remove file tmp.txt: $!\n";}

print "removed tmp.txt to $filename\n" if $do_ddebug;

########################
# END of script
# 
print "\nconfiguration of isaaxe  properly terminated\n\n";
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

# strip leading and trailing blanks
sub strip_blanks{
    local ($string) = @_;
    $string =~ s/^\s*((\S+)|(\S.*\S))\s*$/$1/g;
    return $string;
}

# translate an entry for `isaaxe' script
sub translate_entry{
    local ($mod,$key,$code) = @_;
    local (@codelist);
    local ($string);
    # if mod is None, delete it
    if ($mod eq "None"){$mod = "";}

    # if key is an uppercase letter, add Shift to modifier
    # although conversion to lowercase is not necessary, we do it

    if ($key =~ /^[A-Z]$/){
	$mod = $mod." Shift" if !($mod eq "Shift");
	$key =~ tr/A-Z/a-z/;}
 
    # split the sequence of key codes
    @codelist = split(/\s*,\s*/,$code);

    # generate key codes
    $code="";
    foreach $string (@codelist){
   	$code .= "insert-string(0x". $string .") ";}

    # assemble the whole line
    $string = "!". #exclusive binding
	$mod." <Key>".$key.":\t\t".$code;

    return $string;
}




