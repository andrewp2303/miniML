(* 
                         CS 51 Final Project
                      MiniML -- Lexical Analyzer

 *)

{
  open Printf ;;
  open Miniml_parse ;; (* need access to parser's token definitions *)

  let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

  let keyword_table = 
    create_hashtable 8 [
                       ("if", IF);
                       ("in", IN);
                       ("then", THEN);
                       ("else", ELSE);
                       ("let", LET);
                       ("raise", RAISE);
                       ("rec", REC);
                       ("true", TRUE);
                       ("false", FALSE);
                       ("fun", FUNCTION);
                       ("function", FUNCTION)
                     ]
                     
  let sym_table = 
    create_hashtable 8 [
                       ("=", EQUALS);
                       ("<", LESSTHAN);
                       (">", GREATERTHAN);
                       (".", DOT);
                       ("->", DOT);
                       (";;", EOF);
                       ("~-", NEG);
                       ("+", PLUS);
                       ("-", MINUS);
                       ("*", TIMES);
                       ("/", DIVIDE);
                       ("(", OPEN);
                       (")", CLOSE);
                       ("&&", AND);
                       ("||", OR)
                     ]
}

let digit = ['0'-'9']
let id = ['a'-'z'] ['a'-'z' '0'-'9']*
let sym = ['(' ')'] | (['$' '&' '*' '+' '-' '/' '=' '<' '>' '^'
                            '.' '~' ';' '!' '?' '%' ':' '#' '|']+)
let string = ['"'] [^ '"']* ['"']

(* creating a regular expression for floats *)
let exp = ['e' 'E'] ['-' '+']? digit*
let frac = '.' digit*
let fl = digit+ frac? exp?

rule token = parse
  | digit+ as inum
        { let num = int_of_string inum in
          INT num
        }
  | fl as ifloat
        { let num = float_of_string ifloat in
          FLOAT num
        }
  | id as word
        { try
            let token = Hashtbl.find keyword_table word in
            token 
          with Not_found ->
            ID word
        }
  | sym as symbol
        { try
            let token = Hashtbl.find sym_table symbol in
            token
          with Not_found ->
            printf "Ignoring unrecognized token: %s\n" symbol;
            token lexbuf
        }
  | string as str 
        { STRING (String.sub str 1 (String.length str - 2)) 
        }
  | '{' [^ '\n']* '}'   { token lexbuf }    (* skip one-line comments *)
  | [' ' '\t' '\n']     { token lexbuf }    (* skip whitespace *)
  | _ as c                                  (* warn and skip unrecognized characters *)
        { printf "Ignoring unrecognized character: %c\n" c;
          token lexbuf
        }
  | eof
        { raise End_of_file }
