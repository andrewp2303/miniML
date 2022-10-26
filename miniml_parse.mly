(*
                         CS 51 Final Project
                           MiniML -- Parser
*)
                  
%{
  open Expr ;;
  (* lst_to_fun takes a list of strings and a terminal expression, then 
  converts it to a nested Fun *)
  let rec lst_to_fun (lst : string list) (exp : expr) : expr = 
  match lst with
  | [] -> exp
  | hd :: tl -> Fun(hd, lst_to_fun tl exp) ;;
%}

%token EOF
%token OPEN CLOSE
%token LET DOT IN REC
%token NEG
%token AND OR 
%token PLUS MINUS 
%token TIMES DIVIDE
%token LESSTHAN EQUALS GREATERTHAN
%token IF THEN ELSE 
%token FUNCTION
%token RAISE
%token <string> ID
%token <int> INT 
%token <float> FLOAT
%token <string> STRING 
%token TRUE FALSE

%nonassoc IF
%left LESSTHAN EQUALS GREATERTHAN
%left PLUS MINUS
%left TIMES DIVIDE
%nonassoc AND OR
%nonassoc NEG

%start input
%type <Expr.expr> input


(* Grammar follows *)
%%
input:  exp EOF                 { $1 }


exp:    exp expnoapp            { App($1, $2) }
        | expnoapp              { $1 }

idlist:  ID idlist              { $1 :: $2 }
        | ID                    { [$1] }

expnoapp: INT                   { Num $1 }
        | FLOAT                 { Float $1 }
        | STRING                { String $1 }
        | TRUE                  { Bool true }
        | FALSE                 { Bool false }
        | ID                    { Var $1 }
        | exp PLUS exp          { Binop(Plus, $1, $3) }
        | exp MINUS exp         { Binop(Minus, $1, $3) }
        | exp TIMES exp         { Binop(Times, $1, $3) }
        | exp DIVIDE exp        { Binop(Divide, $1, $3) }
        | exp EQUALS exp        { Binop(Equals, $1, $3) }
        | exp LESSTHAN exp      { Binop(LessThan, $1, $3) }
        | exp GREATERTHAN exp   { Binop(GreaterThan, $1, $3) }
        | exp AND exp           { Binop(And, $1, $3) }
        | exp OR exp            { Binop(Or, $1, $3) }
        | NEG exp               { Unop(Negate, $2) }
        | IF exp THEN exp ELSE exp      { Conditional($2, $4, $6) }
        | LET ID EQUALS exp IN exp      { Let($2, $4, $6) }
        | LET REC ID EQUALS exp IN exp  { Letrec($3, $5, $7) }
        | LET ID idlist EQUALS exp IN exp   { Let($2, lst_to_fun $3 $5, $7) }
        | LET REC ID idlist EQUALS exp IN exp { Letrec($3, lst_to_fun $4 $6, $8) }
        | FUNCTION ID idlist DOT exp   { Fun($2, lst_to_fun $3 $5) } 
        | FUNCTION ID DOT exp   { Fun($2, $4) } 
        | RAISE                 { Raise }
        | OPEN exp CLOSE        { $2 }
;

%%
