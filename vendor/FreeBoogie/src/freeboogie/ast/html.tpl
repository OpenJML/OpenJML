This is a list of all classes in the FreeBoogie
abstract grammar.

\file{ag.html}
<html>
<head><title>The FreeBoogie abstract grammar</title></head>

<body>

<h1>The FreeBoogie AST</h1>

<p>
The base class for the whole hierarchy is <tt>Ast</tt>.
The abstract classes (\abstract_classes[, ]{<tt>\ClassName</tt>})
are used to group related normal classes
(\normal_classes[, ]{<tt>\ClassName</tt>}). The normal
classes may have members which can be children or primitives,
and if they are primitives they can be enums. A list with
details about normal classes follows.
</p>

<table border="1" align="center">
<tr>
  <th>Class</th>
  <th>Base</th>
  <th>Children</th>
  <th>Primitives</th>
  <th>Enum members</th>
</tr>

\normal_classes{
<a name="\ClassName" />
<tr>
  <td>\ClassName</td>
  <td>\BaseName</td>
  <td>\children[, ]{\memberName}</td>
  <td>\primitives[, ]{\if_enum{}{\memberName}}</td>
  <td>\primitives[, ]{\if_enum{\memberName}{}}</td>
</tr>
}
</table>

<p>
Here is a graphical representation of the hierarchy:
</p>

<img src="hierarchy.gif" />


</body>
</html>

\file{/dev/null}
We also generate the dot file from which the hierarchy is generated.

\file{hierarchy.dot}
digraph hierarchy {
  rankdir=RL;
  node [shape=box];
\classes{"\ClassName" -> "\BaseName";
}
  "Ast" [style=bold];
\abstract_classes{"\ClassName" [style=bold];
}
}

