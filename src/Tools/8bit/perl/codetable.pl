#!/usr/local/dist/bin/perl
#
# codetable.pl
# Franz Regensburger <regensbu@informatik.tu-muenchen.de>
# 21.3.95
#
# last changed: 
#
# print the extended ascii-code table
# leave out unprintable characters.
#
# needs an 8bit terminal for output

$index = 0;
while ($index <= 255) {
     if ( $index < 32 || (126 < $index && $index < 161)){# unprintable
#    if ( $index < 32){# unprintable
	$ascii_code = 32;}
	else { 	$ascii_code = $index;} 	

    printf( "%-3o  %-3d  %-2x  %c \n", 
                 $index,
                 $index,
                 $index,
		 $ascii_code);

    $index += 1;
}
