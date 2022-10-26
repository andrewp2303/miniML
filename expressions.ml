open Expr ;;
open Evaluation ;;
open Env ;;


(* stores unops and binops that test all cases *)
let unop1 = Unop (Negate, Num 1)
let unop2 = Unop (Negate, Num (~-2))
let unop3 = Unop (Negate, Float 1.)
let unop4 = Unop (Negate, Float (~-.2.5))

let binop1 = Binop (Plus, Num 1, Num 2)
let binop2 = Binop (Plus, Float 1.5, Float 2.6)
let binop3 = Binop (Plus, Float 1.3, Num 2)
let binop4 = Binop (Plus, Num 1, Float 2.3)

let binop5 = Binop (Minus, Num 1, Num 2)
let binop6 = Binop (Minus, Float 1.5, Float 2.6)
let binop7 = Binop (Minus, Float 1.3, Num 2)
let binop8 = Binop (Minus, Num 1, Float 2.3)

let binop9 = Binop (Times, Num 1, Num 2)
let binop10 = Binop (Times, Float 3., Float 1.5)
let binop11 = Binop (Times, Float ~-.1.5, Num 3)
let binop12 = Binop (Times, Num 4, Float 1.)

let binop13 = Binop (Divide, Num 1, Num 2)
let binop14 = Binop (Divide, Float 3., Float 1.5)
let binop15 = Binop (Divide, Float ~-.1.5, Num 3)
let binop16 = Binop (Divide, Num 4, Float 1.)

let binop17 = Binop (Equals, Num 2, Num 2)
let binop18 = Binop (Equals, Float 3., Float 1.5)
let binop19 = Binop (Equals, Float 3., Num 3)
let binop20 = Binop (Equals, Num 4, Float 1.)
let binop21 = Binop (Equals, Bool true, Bool true)

let binop22 = Binop (LessThan, Num 1, Num 2)
let binop23 = Binop (LessThan, Float 3., Float 1.5)
let binop24 = Binop (LessThan, Float 1.5, Num ~-3)
let binop25 = Binop (LessThan, Num 4, Float 1.)
let binop26 = Binop (LessThan, Bool true, Bool false)

let binop27 = Binop (GreaterThan, Num 1, Num 2)
let binop28 = Binop (GreaterThan, Float 3., Float 1.5)
let binop29 = Binop (GreaterThan, Float 1.5, Num ~-3)
let binop30 = Binop (GreaterThan, Num 4, Float 1.)
let binop31 = Binop (GreaterThan, Bool true, Bool false)

let binop32 = Binop (Equals, String "hello", String "hello")
let binop33 = Binop (LessThan, String "cat", String "dog")
let binop34 = Binop (GreaterThan, String "cat", String "dog")
let binop35 = Binop (Plus, String "hello", String " world!")

let binop36 = Binop (And, Bool true, Bool false)
let binop37 = Binop (Or, Bool true, Bool false)

(* Note: starting here, test expressions were made using 
exp_to_abstract_string and the trivial evaluator in miniML *)

(* creates conditionals to be evaluated *)

(* if 2 > 3 then "hello" else "goodbye" ;; *)
(* evaluates to Val String "goodbye" *)
let cond1 = Conditional(Binop(GreaterThan, Num(2), Num(3)), 
			String("hello"), String("goodbye"))

(* if 4 + 2 = 6 then 51 else 124 ;; *)
(* evaluates to Val Num 51 *)
let cond2 = Conditional(Binop(Equals, Binop(Plus, Num(4), Num(2)), 
			Num(6)), Num(51), Num(124))

(* if 3.0 < 4 then 3 * 4 else 3 + 4 ;; *)
(* evaluates to Val Num 12 *)
let cond3 = Conditional(Binop(LessThan, Float(3.), Num(4)), 
			Binop(Times, Num(3), Num(4)), Binop(Plus, Num(3), Num(4)))

(* if 3 * 17 = 51. then 51 > 124 else 51 < 124 ;; *)
(* evaluates to Val Bool False *)
let cond4 = Conditional(Binop(Equals, Binop(Times, Num(3), Num(17)), 
			Float(51.)), Binop(GreaterThan, Num(51), Num(124)), 
			Binop(LessThan, Num(51), Num(124)))


(* creates environments *)
let envx3 = extend (empty ()) "x" (ref (Val (Num 3)))
let envyf = extend envx3 "y" (ref (Val (Bool false)))
let envx4 = extend envyf "x" (ref (Val (Float 4.)))
let envempty = empty ()


(* creates function expressions *)
(* fun x -> y *)
let func1 = Fun("x", Var("y"))

(* fun z -> 3 *)
let func2 = Fun("z", Num(3))


(* creates let expressions *)
(* let x = 3. in x ;; *)
let lexp1 = Let("x", Float(3.), Var("x"))

(* let y = 124 in 51 ;; *)
let lexp2 = Let("y", Num(124), Num(51))

(* let x = y + 3 in x ;; *)
let lexp3 = Let("x", Binop(Plus, Var("y"), Num(3)), Var("x"))



(* creates compound expressions *)
(* from the writeup: 
let x = 1 in let f = fun y -> x + y in let x = 2 in f 3 ;; *)
(* should evaluate to 4 with eval_s/eval_l and 5 with eval_d *)
let comp1 = Let("x", Num(1), Let("f", Fun("y", Binop(Plus, Var("x"), Var("y"))), 
            Let("x", Num(2), App(Var("f"), Num(3)))))

(* let x = 5. in let f = fun y -> x in let x = 3. in f 6 ;; *)
(* slightly confusing, but should evaluate to 5. in lex/sub and 3. in dyn *)
let comp2 = Let("x", Float(5.), Let("f", Fun("y", Var("x")), 
            Let("x", Float(3.), App(Var("f"), Num(6)))))

(* let double = fun x -> 2 * x in double (double 3) ;; *)
(* another one from book, evaluates to Val Num 12 *)
let comp3 = Let("double", Fun("x", Binop(Times, Num(2), Var("x"))), 
			App(Var("double"), App(Var("double"), Num(3))))

(* let f = fun n -> if n = 0 then 1 else n * f (n - 1) in f 2 ;; *)
(* another one from the book *)
let comp4 = Let("f", Fun("n", Conditional(Binop(Equals, Var("n"), Num(0)), 
			Num(1), Binop(Times, Var("n"), App(Var("f"), Binop(Minus, Var("n"), 
			Num(1)))))), App(Var("f"), Num(2)))


(* creates syntactically sugared expressions for testing *)
(* let f x y = x + y in f 3 4 ;; *)
(* f sums the two input values, should evaluate to Val Num 7 *)
let sugar1 = Let("f", Fun("x", Fun("y", Binop(Plus, Var("x"), Var("y")))), 
			App(App(Var("f"), Num(3)), Num(4)))

(* let ord a b c = (a < b) && (b < c) in ord 1 2 3 ;; *)
(* should evaluate to Val Bool True (ord checks if a < b < c) *)
let sugar2 = Let("ord", Fun("a", Fun("b", Fun("c", Binop(And, Binop(LessThan, 
			Var("a"), Var("b")), Binop(LessThan, Var("b"), Var("c")))))), 
			App(App(App(Var("ord"), Num(1)), Num(2)), Num(3)))

(* let conc x y = x + y in conc "hello " "world!" ;; *)
(* should evaluate to Val String "hello world!" (conc is a concatenator) *)
let sugar3 = Let("conc", Fun("x", Fun("y", Binop(Plus, Var("x"), Var("y")))), 
			App(App(Var("conc"), String("hello ")), String("world!")))

(* let x = 3 in let f y z = x + y + z in let x = 4 in f 3 3 ;; *)
(* one final test - theoretically evaluates to 10 in dynamic and 9 in lex/sub, 
but in actuality should return an error in dynamic and 9 in lex/sub *)
let sugar4 = Let("x", Num(3), Let("f", Fun("y", Fun("z", Binop(Plus, 
			Binop(Plus, Var("x"), Var("y")), Var("z")))), Let("x", Num(4), 
			App(App(Var("f"), Num(3)), Num(3)))))