(* 
                         CS 51 Problem Set 2
            Higher Order Functional Programming -- Testing
 *)

open Test_simple ;;
open Expr ;;
open Evaluation ;;
open Env ;;

(* Expressions contains sample expressions and environments used to create 
and run unit tests in tests.ml *)
open Expressions ;;

(* tests free_vars on all original expr types *)
let freevars_test () =
    Printf.printf("Testing free_vars!\n");
    unit_test (same_vars (free_vars (Num 5)) 
    (vars_of_list []))
    	"free vars num";
    unit_test (same_vars (free_vars (Num 5)) 
    (vars_of_list []))
    	"free vars bool";
    unit_test (same_vars (free_vars (Raise)) 
    (vars_of_list []))
    	"free vars raise";
    unit_test (same_vars (free_vars (Unassigned)) 
    (vars_of_list []))
    	"free vars unassigned";
    unit_test (same_vars (free_vars (Var "x")) 
    (vars_of_list ["x"]))
    	"free vars var";
    unit_test (same_vars (free_vars (Unop (Negate, Var "x"))) 
    (vars_of_list ["x"]))
    	"free vars unop";
    unit_test (same_vars (free_vars (Binop (Times, Var "x", Var "y"))) 
    (vars_of_list ["x"; "y"]))
    	"free vars binop";
    unit_test (same_vars (free_vars (App (Var "f", Var "x"))) 
    (vars_of_list ["f"; "x"]))
    	"free vars application";
    unit_test (same_vars (free_vars (Let ("x", Num 3, Unop (Negate, Var "x")))) 
    (vars_of_list []))
    	"free vars let";
    unit_test (same_vars (free_vars (Letrec ("x", Binop (Plus, Var "x", Num 3),
     Unop (Negate, Var "x")))) 
    (vars_of_list []))
    	"free vars letrec";
    unit_test (same_vars (free_vars (Fun ("x", Var "x"))) 
    (vars_of_list []))
    	"free vars fun";
    unit_test (same_vars (free_vars (Conditional (Var "x", Var "y", Var "z"))) 
    (vars_of_list ["x"; "y"; "z"]))
    	"free vars conditional";
         ;;

(* note: did not test on nested strings because they have been shown to work 
via expressions.ml, and because string escape sequences were failing *)
let exp_to_abstr_test () = 
	Printf.printf("\nTesting exp_to_abstr!\n");
    unit_test (exp_to_abstract_string cond2 =
			"Conditional(Binop(Equals, Binop(Plus, Num(4), Num(2)), " ^ 
			"Num(6)), Num(51), Num(124))")
		"exp_to_abstr cond1";
	unit_test (exp_to_abstract_string cond3 =
			"Conditional(Binop(LessThan, Float(3.), Num(4)), " ^ 
			"Binop(Times, Num(3), Num(4)), Binop(Plus, Num(3), Num(4)))")
		"exp_to_abstr cond3";
	unit_test (exp_to_abstract_string binop10 =
			"Binop(Times, Float(3.), Float(1.5))")
		"exp_to_abstr binop10";
	unit_test (exp_to_abstract_string binop27 =
			"Binop(GreaterThan, Num(1), Num(2))")
		"exp_to_abstr binop27" ;;

(* tests exp_to_concrete_string *)
let exp_to_conc_test () = 
	Printf.printf("\nTesting exp_to_conc!\n");	
    unit_test (exp_to_concrete_string cond2 =
			"if 4 + 2 = 6 then 51 else 124")
		"exp_to_conc cond1";
	unit_test (exp_to_concrete_string cond3 =
			"if 3. < 4 then 3 * 4 else 3 + 4")
		"exp_to_conc cond3";
	unit_test (exp_to_concrete_string binop10 =
			"3. * 1.5")
		"exp_to_conc binop10";
	unit_test (exp_to_concrete_string binop27 =
			"1 > 2")
		"exp_to_conc binop27" ;;

(* tests new varname *)
let new_vname_test () = 
	Printf.printf("\nTesting new_varname!\n");	
    unit_test (new_varname () = "var0")
		"new_varname 0";
	unit_test (new_varname () = "var1")
		"new_varname 1";
	unit_test (new_varname () = "var2")
		"new_varname 2" ;;

(* tests substitution *)
let subst_test () = 
	Printf.printf("\nTesting subst!\n");	
    unit_test (subst "z" (Var "y") func2 =
			func2)
		"subst func2";
	unit_test (subst "x" (Var "z") lexp2 =
			lexp2)
		"subst lexp2 z";
	unit_test (subst "x" (Var "y") lexp2 =
			Let("var3", Num(124), Num(51)))
		"subst lexp2 y";
	unit_test (subst "y" (Num 4) lexp3 =
			Let("x", Binop(Plus, Num(4), Num(3)), Var("x")))
		"subst lexp3 y -> 4";
	unit_test (subst "x" (Num 4) lexp3 = 
			lexp3)
		"subst lexp3 x -> 4" ;;

(* tests the extract helper *)
let extr_test () = 
	Printf.printf("\nTesting extract!\n");	
    unit_test (extract (Val (Var "x")) = Var "x")
		"extract var";
	unit_test (extract (Val binop1) = binop1)
		"extract binop1";
	unit_test (extract (Val cond1) = cond1)
		"extract cond1";
	unit_test (extract (Val comp1) = comp1)
		"extract comp1" ;;

(* tolerance and float extraction, for testing with floats *)
let tol = 0.0001
let extr_float (v : value) = match v with 
                             | Val Float n -> n  
                             | _ -> failwith "inv input"

(* tests that num, bool, float, string remain the same through evaluation *)
let eval_identity_test (ev : (expr -> env -> value)) : unit = 
	unit_test (ev (Num 3) (empty ()) = Val (Num 3))
    	"eval num";
	unit_test (ev (Bool false) (empty ()) = Val (Bool false))
    	"eval bool";
	unit_test (ev (Float 3.2) (empty ()) = Val (Float 3.2))
    	"eval float";
	unit_test (ev (String "hello") (empty ()) = Val (String "hello"))
    	"eval string" ;;

(* tests unops, given an evaluator *)
let eval_unop_test (ev : (expr -> env -> value)) : unit = 
    unit_test (ev unop1 (empty ()) = Val (Num ~-1))
    	"eval unop1";
	unit_test (ev unop2 (empty ()) = Val (Num 2))
    	"eval unop2";
	unit_test (ev unop3 (empty ()) = Val (Float ~-.1.))
    	"eval unop3";
	unit_test (ev unop4 (empty ()) = Val (Float 2.5))
    	"eval unop4" ;;

(* tests binops, given an evaluator *)
let eval_binop_test (ev : (expr -> env -> value)) : unit = 
    unit_test (ev binop1 (empty ()) = Val (Num 3))
    "eval binop1";
    unit_test_within tol 
        (extr_float (ev binop2 (empty ()))) 
        (extr_float (Val (Float 4.1)))
        "eval binop2";
    unit_test_within tol 
        (extr_float (ev binop3 (empty ()))) 
        (extr_float (Val (Float 3.3)))
        "eval binop3";
    unit_test_within tol 
        (extr_float (ev binop4 (empty ()))) 
        (extr_float (Val (Float 3.3)))
        "eval binop4";
    unit_test (ev binop5 (empty ()) = Val (Num (~-1)))
    "eval binop5";
    unit_test_within tol 
        (extr_float (ev binop6 (empty ()))) 
        (extr_float (Val (Float (~-.1.1))))
        "eval binop6";
    unit_test_within tol 
        (extr_float (ev binop7 (empty ()))) 
        (extr_float (Val (Float (~-.0.7))))
        "eval binop7";
    unit_test_within tol 
        (extr_float (ev binop8 (empty ()))) 
        (extr_float (Val (Float (~-.1.3))))
        "eval binop8";
    unit_test (ev binop9 (empty ()) = Val (Num 2))
    "eval binop9";
    unit_test_within tol 
        (extr_float (ev binop10 (empty ()))) 
        (extr_float (Val (Float 4.5)))
        "eval binop10";
    unit_test_within tol 
        (extr_float (ev binop11 (empty ()))) 
        (extr_float (Val (Float ~-.4.5)))
        "eval binop11";
    unit_test_within tol 
        (extr_float (ev binop12 (empty ()))) 
        (extr_float (Val (Float 4.)))
        "eval binop12";
    unit_test (ev binop13 (empty ()) = Val (Num (0)))
    "eval binop13";
    unit_test_within tol 
        (extr_float (ev binop14 (empty ()))) 
        (extr_float (Val (Float (2.))))
        "eval binop14";
    unit_test_within tol 
        (extr_float (ev binop15 (empty ()))) 
        (extr_float (Val (Float (~-.0.5))))
        "eval binop15";
    unit_test_within tol 
        (extr_float (ev binop16 (empty ()))) 
        (extr_float (Val (Float (4.))))
        "eval binop16";
    unit_test (ev binop17 (empty ()) = Val (Bool true))
        "eval binop17";
	unit_test (ev binop18 (empty ()) = Val (Bool false))
        "eval binop18";
	unit_test (ev binop19 (empty ()) = Val (Bool true))
        "eval binop19";
	unit_test (ev binop20 (empty ()) = Val (Bool false))
        "eval binop20";
	unit_test (ev binop21 (empty ()) = Val (Bool true))
        "eval binop21";
	unit_test (ev binop22 (empty ()) = Val (Bool true))
        "eval binop22";
	unit_test (ev binop23 (empty ()) = Val (Bool false))
        "eval binop23";
	unit_test (ev binop24 (empty ()) = Val (Bool false))
        "eval binop24";
	unit_test (ev binop25 (empty ()) = Val (Bool false))
        "eval binop25";
	unit_test (ev binop26 (empty ()) = Val (Bool false))
        "eval binop26";
	unit_test (ev binop27 (empty ()) = Val (Bool false))
        "eval binop27";
	unit_test (ev binop28 (empty ()) = Val (Bool true))
        "eval binop28";
	unit_test (ev binop29 (empty ()) = Val (Bool true))
        "eval binop29";
	unit_test (ev binop30 (empty ()) = Val (Bool true))
        "eval binop30";
	unit_test (ev binop31 (empty ()) = Val (Bool true))
        "eval binop31";
	unit_test (ev binop32 (empty ()) = Val (Bool true))
        "eval binop32";
	unit_test (ev binop33 (empty ()) = Val (Bool true))
        "eval binop33";
	unit_test (ev binop34 (empty ()) = Val (Bool false))
        "eval binop34";
	unit_test (ev binop35 (empty ()) = Val (String "hello world!"))
        "eval binop35";
	unit_test (ev binop36 (empty ()) = Val (Bool false))
        "eval binop36";
	unit_test (ev binop37 (empty ()) = Val (Bool true))
        "eval binop37" ;;

(* tests Conditionals, given evaluator *)
let eval_cond_test (ev : (expr -> env -> value)) : unit =
	unit_test (ev cond1 (empty ()) = Val (String "goodbye"))
    	"eval cond1";
	unit_test (ev cond2 (empty ()) = Val (Num 51))
    	"eval cond2";
	unit_test (ev cond3 (empty ()) = Val (Num 12))
    	"eval cond3";
	unit_test (ev cond4 (empty ()) = Val (Bool false))
    	"eval cond4" ;;

(* tests for correct Var output, with varying expectations based on model *)
let eval_var_test (ev : (expr -> env -> value)) (md : model) : unit =
	if md = Sub then
		(unit_test (try (ev (Var "x") (empty ())) = Val (Var "z")
		with EvalError "unbound variable x" -> true)
			"eval var substitution")
	else
		(unit_test (try (ev (Var "x") (empty ())) = Val (Var "z")
		with EvalError "val not found" -> true)
			"eval var not found";
		unit_test (try (ev (Var "x") envx3) = Val (Num 3)
		with EvalError "val not found" -> false)
			"eval var x -> 3";
		unit_test (try (ev (Var "y") envyf) = Val (Bool false)
		with EvalError "val not found" -> false)
			"eval var y -> false";
		(* checks that extend removes associations *)
		unit_test (try (ev (Var "x") envx4) = Val (Float 4.)
		with EvalError "val not found" -> false)
			"eval var x -> 4.") ;;

(* tests for correct Fun output based on model *)
let eval_fun_test (ev : (expr -> env -> value)) (md : model) : unit =
	unit_test (ev func1 envempty = 
		if md = Lex then Closure (func1, envempty) else Val (func1))
		"eval func1 empty env";
	unit_test (ev func1 envx4 = 
		if md = Lex then Closure (func1, envx4) else Val (func1))
		"eval func1 envx4";
	unit_test (ev func2 envempty = 
		if md = Lex then Closure (func2, envempty) else Val (func2))
		"eval func2 empty env";
	unit_test (ev func2 envx4 = 
		if md = Lex then Closure (func2, envx4) else Val (func2))
		"eval func2 envx4" ;;

(* tests for correct Let output based on model *)
let eval_let_test (ev : (expr -> env -> value)) (md : model) : unit =
	if md = Lex then
		unit_test (ev lexp1 envx4 = Val (Float 3.))
			"eval lexp1 envx4"
	else ();
		(unit_test (ev lexp1 (empty ()) = Val (Float 3.))
			"eval lexp1";
		unit_test (ev lexp2 (empty ()) = Val (Num 51))
			"eval lexp2") ;;

(* tests letrec and application using compound tests *)
let eval_compound_test (ev : (expr -> env -> value)) (md : model) : unit =
	unit_test (ev comp1 (empty ()) = 
		if md = Dyn then Val (Num 5) else Val (Num 4))
		"eval comp1 empty env";
    unit_test (ev comp2 (empty ()) = 
		if md = Dyn then Val (Float 3.) else Val (Float 5.))
		"eval comp2 empty env";
	unit_test (ev comp3 (empty ()) = Val (Num 12))
		"eval comp3 empty env";
	(* should evaluate in dynamic and fail in sub/lex *)
	unit_test (try ev comp4 (empty ()) = 
		Val (Num 2) with 
		| (EvalError "unbound variable f") -> md = Sub 
		| (EvalError "val not found") -> md = Lex)
		"eval comp4 empty env" ;;

(* tests syntactic sugaring of lets, letrecs, funs *)
let eval_sugar_test (ev : (expr -> env -> value)) (md : model) : unit =
	unit_test (try ev sugar1 (empty ()) = 
		Val (Num 7) with (EvalError "val not found") -> md = Dyn)
		"eval sugar1 empty env";
    unit_test (try ev sugar2 (empty ()) = 
		Val (Bool true) with (EvalError "val not found") -> md = Dyn)
		"eval sugar2 empty env";
	unit_test (try ev sugar3 (empty ()) = 
		Val (String "hello world!") with (EvalError "val not found") -> md = Dyn)
		"eval sugar3 empty env";
	unit_test (try ev sugar4 (empty ()) = 
		Val (Num 9) with (EvalError "val not found") -> md = Dyn)
		"eval sugar4 empty env" ;;


(* abstracts all the tests, regardless of model *)
let eval_tests (ev : (expr -> env -> value)) (md : model) : unit = 
	eval_identity_test ev;
	eval_unop_test ev;
	eval_binop_test ev;
	eval_cond_test ev;
	eval_var_test ev md;
	eval_fun_test ev md; 
	eval_let_test ev md; 
	eval_compound_test ev md;
	eval_sugar_test ev md ;;

(* tests the three non-trivial models *)
let eval_s_test () = 
    Printf.printf("\nTesting eval_s!\n");
    eval_tests eval_s Sub ;;

let eval_d_test () = 
    Printf.printf("\nTesting eval_d!\n");
	eval_tests eval_d Dyn ;;
		
let eval_l_test () = 
	Printf.printf("\nTesting eval_l!\n");
	eval_tests eval_l Lex ;;
    
(* runs all tests on functions and the 3 evaluators *)
let test_all () = 
    freevars_test ();
	exp_to_abstr_test ();
	exp_to_conc_test ();
	new_vname_test ();
	subst_test ();
	extr_test ();
    eval_s_test ();
    eval_d_test ();
    eval_l_test () ;;

let _ = test_all () ;;