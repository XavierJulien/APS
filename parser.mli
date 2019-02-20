type token =
  | NUM of (int)
  | IDENT of (string)
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | CONST
  | FUN
  | REC
  | ECHO
  | INT
  | BOOL
  | TRUE
  | FALSE
  | NOT
  | AND
  | OR
  | EQ
  | LT
  | IF
  | LBRACKET
  | RBRACKET
  | LPAR
  | RPAR
  | COLON
  | SEMICOLON
  | COMMA
  | STAR
  | ARROW

val prog :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.prog
