{
open Parser        (* The type token is defined in parser.mli *)
exception Eof
}
rule token = parse
(*Séparateurs*)
[' ' '\t']       { token lexbuf }     (* skip blanks *)
| ['\n' ]          { EOL }
(*constantes numériques*)
| ('-'?)['0'-'9']+ as lxm { NUM(int_of_string lxm) }
(*identificateurs*)
| ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9']* as id { IDENT(id) } 
(*mots-clefs*)
| "if"			   { IF }
| "add"            { PLUS }
| "sub"            { MINUS }
| "mul"            { TIMES }
| "div"            { DIV }
| "CONST"		   { CONST }
| "FUN" 		   { FUN }
| "REC" 		   { REC }
| "ECHO"           { ECHO }
| "int"		       { INT }
| "bool" 		   { BOOL }
| "true" 		   { TRUE }
| "false"          { FALSE }
| "not"		       { NOT }
| "and" 		   { AND }
| "or" 		       { OR }
| "eq"             { EQ }
| "lt"		       { LT }

(*Symboles réservés*)
| "["			   { LBRACKET }
| "]" 			   { RBRACKET }
| ":"			   { COLON }
| ";"	           { SEMICOLON }
| "," 			   { COMMA }
| "*" 			   { STAR }
| "->"			   { ARROW }
| "("              { LPAR }
| ")"              { RPAR }
| eof              { raise Eof }
