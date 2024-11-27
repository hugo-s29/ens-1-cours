open Expr_conv

let expr_test = "g(x,f(x,y))"

let _ = Printf.printf "Test de l'expression %s : %s\n" expr_test (string_of_expr (expr_of_string expr_test))

let prob_test = "g(x,f(x,y)) = h()"

let _ = Printf.printf "Test du problème %s : %s\n" prob_test (string_of_problem (problem_of_string prob_test))
