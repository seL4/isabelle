<!-- _GP_
# undef all the functions we're defining. This stops lots of
# complaining about re-defining the sub for each content file that's
# processed.

       if (defined(&me)) { undef &me; }
       if (defined(&distname)) { undef &distname; }
       if (defined(&href)) { undef &href; }
       if (defined(&twodig)) { undef &twodig; }
       if (defined(&when)) { undef &when; }
       if (defined(&size)) { undef &size; }
       if (defined(&page)) { undef &page; }
       if (defined(&empty_line)) { undef &empty_line; }
       if (defined(&setnavcolor)) { undef &setnavcolor; }
       if (defined(&twodig)) { undef &twodig; }
       if (defined(&setdowncolor)) { undef &setdowncolor; }
       if (defined(&downloadhead)) { undef &downloadhead; }
       if (defined(&download)) { undef &download; }

 -->

<!--  _GP_ 

    sub distname {
      return $ENV{"DISTNAME"};
    }

    sub href {
	return "<a href=\"" . $_[0] . "\">" . $_[1] . "</a>";
    }

    sub twodig {
      if ($_[0] < 10) {
        return "0$_[0]";
      }
      return "$_[0]";
    }

# ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = gmtime(time);     
    sub when { 
      my @s = stat $inputfile;
      my @t = gmtime($s[9]);      
      my $year  = $t[5]+1900;      
      my $month = twodig($t[4]+1);
      my $day   = twodig($t[3]);
      return "$month/$day/$year";
#      my $hour  = twodig($t[2]);
#      my $min   = twodig($t[1]);
#      return "$month/$day/$year $hour:$min UTC";
    }  

    sub setnavcolor {
      $navcolor = $_[0];
      return "";
    }
    
    # page(name, file)
    sub page {    
      my $retval = "";      

      if ("$_[1].html" eq substr($outputfile,rindex($outputfile,"/")+1)) {
        $retval = <<EOF;
        <table width="100%" border="0" cellspacing="0" cellpadding="5">
        <tr> 
          <td align=center bgcolor="$navcolor">
            <b><font face="Arial,Helvetica"><A HREF="$_[1].html" target="_top">$_[0]</A></font></b>
          </td>
        </tr>
        </table>
EOF
      }
      else {
        $retval = <<EOF;
        <table width="100%" border="0" cellspacing="0" cellpadding="5">
        <tr> 
          <td width="8">&nbsp;</td>
          <td width="150" align=center bgcolor="$navcolor">
            <b><font face="Arial,Helvetica"><A HREF="$_[1].html" target="_top">$_[0]</A></font></b>
          </td>
          <td width="8">&nbsp;</td>
        </tr>
        </table>
EOF
      }
      return $retval;
    }

    # empty_line(numcols)
    sub empty_line {
      my $retval = <<EOF;
      <p>
EOF
      return $retval;
    }

    sub size {
      my $filename = $_[0];

      my @s = stat $filename;
      my $size = defined $s[7] ? $s[7]/1024 : 0;

      return sprintf("%d", $size);
    }

    sub setdowncolor {
      $downcolor = $_[0];
      return "";
    }

    sub downloadhead {
      my $text = $_[0];

      return <<EOF;
      <tr><td colspan=3><strong>$text</strong></td></tr>
EOF
    }

    sub download {
      my $rowspan = $_[0];
      my $descr = $_[1];
      my $url   = $_[2];
      my $prefix  = $_[3];

      my $size = size("$prefix/$url");
      $size = "$size K";

      my $filename = $path;

      if ($url =~ /([^\/]*\/)*([^\/]+)/) {
	$filename = $2;
      }

      my $td   = "nowrap bgcolor=$downcolor";
      
      my $descr_text = "";
      if ($descr ne "") {
        $descr_text = <<EOF;
	<td rowspan=$rowspan align="left" $td>
          &nbsp; $descr
        </td>
EOF
      }

      my $retval = <<EOF;
      <tr>$descr_text
        <td align="left" $td>
          &nbsp; <A HREF="$url">$filename</A>
        </td>
        <td align="right" $td>
          &nbsp; $size &nbsp;
        </td>
      </tr>
EOF

      return $retval;
    }

 -->
