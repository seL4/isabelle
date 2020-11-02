<html>
<body>
<h2>Isabelle Components</h2>
<table>
<tr>
<td><b>Name</b></td>
<td>&nbsp;&nbsp;&nbsp;</td>
<td><b>Size</b></td>
</tr>
<?php
 $component_pattern="/^.+\.tar\.gz$/";

 foreach (scandir(getcwd()) as $file){
   if (preg_match($component_pattern, $file)
       && is_file($file)
       && is_readable($file)) {
     print "<tr><td><a href=\"$file\"><code>$file</code></a></td><td></td><td>".filesize($file)."</td></tr>\n";
  }
 }
?>
</table>
</body>
</html>
