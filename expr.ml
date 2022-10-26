(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Divide
  | Equals
  | LessThan
  | GreaterThan
  | And
  | Or
;;

type varid = string ;;

  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Float of float                       (* floats *)
  | String of string                     (* strings *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var v -> SS.singleton v
  | Unop (_, e) -> free_vars e
  | Binop (_, e1, e2)
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Let (x, e1, e2) -> SS.union (SS.remove x (free_vars e2)) (free_vars e1)
  | Letrec (x, e1, e2) -> SS.union (SS.remove x (free_vars e2)) 
                          (SS.remove x (free_vars e1))
  | Fun (x, e) -> SS.remove x (free_vars e)
  | Conditional (e1, e2, e3) -> SS.union (free_vars e1) 
                              (SS.union (free_vars e2) (free_vars e3))
  | _ -> SS.empty
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)
let new_varname : unit -> varid =
  let ctr = ref ~-1 in fun () -> 
    ctr := !ctr + 1;
    "var" ^ string_of_int !ctr ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let rec sub_this (exp : expr) : expr =
    match exp with
    | Var v -> if v = var_name then repl else exp
    | Unop (unop, e) -> Unop(unop, sub_this e)
    | Binop (binop, e1, e2) -> Binop(binop, sub_this e1, sub_this e2)
    | Let (v, e1, e2) -> 
          if v = var_name 
            then Let (v, sub_this e1, e2)
          else if SS.mem v (free_vars repl) 
            then let temp = new_varname () 
                  in Let (temp, sub_this e1, sub_this (subst v (Var(temp)) e2)) 
          else Let (v, sub_this e1, sub_this e2)
    | Letrec (v, e1, e2) -> 
          if v = var_name 
            then exp
          else if SS.mem v (free_vars repl) 
            then let temp = new_varname () 
                  in Letrec (temp, sub_this (subst v (Var(temp)) e1), 
                            sub_this (subst v (Var(temp)) e2)) 
          else Letrec (v, sub_this e1, sub_this e2)
    | Fun (v, e) -> 
          if v = var_name 
            then exp 
          else if SS.mem v (free_vars repl) 
            then let temp = new_varname () 
                  in Fun (temp, sub_this (subst v (Var(temp)) e)) 
          else Fun (v, sub_this e)
    | App (e1, e2) -> 
                    App (sub_this e1, sub_this e2)
    | Conditional (e1, e2, e3) -> 
                    Conditional (sub_this e1, sub_this e2, sub_this e3)
    | _ -> exp
  in sub_this exp ;;
     
(*......................................................................
  String representations of expressions
 *)
   
(* creates concrete unop/binop strings used in exp_to_concrete_string *)
let string_of_unop (unop : unop) : string =
  match unop with
  | Negate -> "-" ;;

let string_of_binop (binop : binop) : string =
  match binop with
  | Plus -> " + "
  | Minus -> " - "
  | Times -> " * "
  | Divide -> " / "
  | Equals -> " = "
  | LessThan -> " < "
  | GreaterThan -> " > "
  | And -> " && "
  | Or -> " || "
   ;;

(* creates abstract unop/binop strings used in exp_to_abstract_string *)
let string_of_unop_abs (unop : unop) : string =
  match unop with
  | Negate -> "Negate" ;;

let string_of_binop_abs (binop : binop) : string =
  match binop with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Divide -> "Divide"
  | Equals -> "Equals"
  | LessThan -> "LessThan"
  | GreaterThan -> "GreaterThan"
  | And -> "And"
  | Or -> "Or" ;;

(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
(* not done: dealing with spacing *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var v -> v
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Float f -> string_of_float f
  | String s -> s
  | Unop (u, e) -> string_of_unop u ^ exp_to_concrete_string e
  | Binop (b, e1, e2) -> exp_to_concrete_string e1 ^ string_of_binop b
                         ^ exp_to_concrete_string e2
  | Conditional (e1, e2, e3) -> "if " ^ exp_to_concrete_string e1 ^ " then "
                                ^ exp_to_concrete_string e2 ^ " else "
                                ^ exp_to_concrete_string e3
  | Fun (v, e) -> "fun " ^ v ^ " -> " ^ exp_to_concrete_string e
  | Let (v, e1, e2) -> "let " ^ v ^ " = " ^ exp_to_concrete_string e1 
                        ^ " in " ^ exp_to_concrete_string e2
  | Letrec (v, e1, e2) -> "let rec " ^ v ^ " = " ^ exp_to_concrete_string e1 
                        ^ " in " ^ exp_to_concrete_string e2   
  | Raise         
  | Unassigned -> ""        
  | App (e1, e2)  -> exp_to_concrete_string e1 ^ exp_to_concrete_string e2 ;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var(\"" ^ v ^ "\")"
  | Num n -> "Num(" ^ string_of_int n ^ ")"
  | Bool b -> "Bool(" ^ string_of_bool b ^ ")"
  | Float f -> "Float(" ^ string_of_float f ^ ")"
  | String s -> "String(\"" ^ s ^ "\")"
  | Unop (u, e) -> "Unop(" ^ string_of_unop_abs u ^ ", " ^ 
                    exp_to_abstract_string e ^ ")"
  | Binop (b, e1, e2) -> "Binop(" ^ string_of_binop_abs b ^ ", " ^ 
                    exp_to_abstract_string e1 ^ ", " ^ 
                    exp_to_abstract_string e2 ^ ")"
  | Conditional (e1, e2, e3) -> "Conditional(" ^ exp_to_abstract_string e1 ^ 
                                ", " ^ exp_to_abstract_string e2 
                                ^ ", " ^ exp_to_abstract_string e3 ^ ")"
  | Fun (v, e) -> "Fun(\"" ^ v ^ "\", " ^ exp_to_abstract_string e ^ ")"
  | Let (v, e1, e2) -> "Let(\"" ^ v ^ "\", " ^ exp_to_abstract_string e1 
                        ^ ", " ^ exp_to_abstract_string e2 ^ ")"
  | Letrec (v, e1, e2) -> "Letrec(\"" ^ v ^ "\", " ^ exp_to_abstract_string e1 
                        ^ ", " ^ exp_to_abstract_string e2 ^ ")"
  | Raise           
  | Unassigned -> ""        
  | App (e1, e2)  -> "App(" ^ exp_to_abstract_string e1
                      ^ ", " ^ exp_to_abstract_string e2 ^ ")" ;;
