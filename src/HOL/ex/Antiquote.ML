
Goal "P (EXPR (a + b + c))";
Goal "P (EXPR (a + b + c + VAR x + VAR y + 1))";
Goal "P (EXPR (VAR (f w) + VAR x))";

Goal "P (Expr (%env. env))";				(*improper*)
Goal "P (Expr (%env. f env))";
Goal "P (Expr (%env. f env + env))";			(*improper*)
Goal "P (Expr (%env. f env y z))";
Goal "P (Expr (%env. f env + g y env))";
Goal "P (Expr (%env. f env + g env y + h a env z))";
