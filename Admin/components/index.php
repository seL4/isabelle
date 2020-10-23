<html>
<body>
<h2>Components:</h2>
<table>
<tr>
<th> Name </th>
<th> &nbsp;&nbsp;&nbsp; </th>
<th> Size</th>
</tr>
<?php
 $component_pattern="/^.+\.tar\.gz$/";

 foreach (scandir(getcwd()) as $file){
   if (preg_match($component_pattern, $file)
       && is_file($file)
       && is_readable($file)) {
     print "<tr><td><a href=\"$file\">$file</a></td><td></td><td>".filesize($file)."</td></tr>\n";
  }
 }
?>
</table>
</body>
</html>
