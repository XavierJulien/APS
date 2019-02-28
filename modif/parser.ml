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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Ast
# 37 "parser.ml"
let yytransl_const = [|
  259 (* PLUS *);
  260 (* MINUS *);
  261 (* TIMES *);
  262 (* DIV *);
  263 (* CONST *);
  264 (* FUN *);
  265 (* REC *);
  266 (* ECHO *);
  267 (* INT *);
  268 (* BOOL *);
  269 (* TRUE *);
  270 (* FALSE *);
  271 (* NOT *);
  272 (* AND *);
  273 (* OR *);
  274 (* EQ *);
  275 (* LT *);
  276 (* IF *);
  277 (* LBRACKET *);
  278 (* RBRACKET *);
  279 (* LPAR *);
  280 (* RPAR *);
  281 (* COLON *);
  282 (* SEMICOLON *);
  283 (* COMMA *);
  284 (* STAR *);
  285 (* ARROW *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\003\000\004\000\004\000\004\000\
\005\000\005\000\005\000\006\000\006\000\007\000\008\000\008\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\010\000\010\000\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\002\000\004\000\007\000\008\000\
\001\000\001\000\005\000\001\000\003\000\003\000\001\000\003\000\
\001\000\001\000\001\000\001\000\001\000\004\000\004\000\006\000\
\005\000\005\000\005\000\005\000\004\000\005\000\005\000\005\000\
\005\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\036\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\019\000\020\000\017\000\
\018\000\000\000\000\000\005\000\021\000\001\000\000\000\000\000\
\009\000\010\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\004\000\003\000\000\000\000\000\
\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\014\000\016\000\
\022\000\000\000\000\000\000\000\000\000\029\000\000\000\000\000\
\000\000\000\000\000\000\035\000\023\000\013\000\000\000\000\000\
\000\000\025\000\026\000\027\000\028\000\030\000\031\000\032\000\
\033\000\000\000\011\000\007\000\000\000\024\000\008\000"

let yydgoto = "\002\000\
\004\000\008\000\009\000\010\000\047\000\048\000\032\000\033\000\
\065\000\066\000\021\000"

let yysindex = "\004\000\
\246\254\000\000\030\255\000\000\011\255\008\255\002\255\248\254\
\254\254\013\255\252\254\252\254\016\255\000\000\000\000\000\000\
\000\000\020\255\069\255\000\000\000\000\000\000\030\255\030\255\
\000\000\000\000\252\254\002\255\024\255\252\254\021\255\014\255\
\037\255\002\255\002\255\002\255\002\255\002\255\002\255\002\255\
\002\255\002\255\002\255\002\255\000\000\000\000\032\255\023\255\
\000\000\020\255\040\255\252\254\020\255\002\255\002\255\002\255\
\002\255\002\255\038\255\002\255\002\255\002\255\002\255\002\255\
\002\255\039\255\252\254\252\254\042\255\020\255\000\000\000\000\
\000\000\041\255\043\255\044\255\045\255\000\000\053\255\054\255\
\055\255\056\255\002\255\000\000\000\000\000\000\067\255\002\255\
\071\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\072\255\000\000\000\000\002\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\073\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\070\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\074\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\020\000\000\000\000\000\246\255\255\255\000\000\212\255\
\249\255\035\000\000\000"

let yytablesize = 100
let yytable = "\020\000\
\028\000\029\000\014\000\015\000\001\000\069\000\025\000\026\000\
\072\000\012\000\003\000\044\000\011\000\022\000\016\000\017\000\
\013\000\030\000\027\000\051\000\049\000\031\000\018\000\023\000\
\019\000\089\000\055\000\056\000\057\000\058\000\059\000\060\000\
\061\000\062\000\063\000\064\000\005\000\006\000\024\000\007\000\
\053\000\071\000\045\000\046\000\050\000\052\000\073\000\074\000\
\075\000\076\000\077\000\068\000\079\000\080\000\081\000\082\000\
\083\000\087\000\054\000\067\000\070\000\078\000\085\000\088\000\
\090\000\086\000\091\000\092\000\093\000\014\000\015\000\034\000\
\035\000\036\000\037\000\098\000\094\000\095\000\096\000\097\000\
\100\000\016\000\017\000\038\000\039\000\040\000\041\000\042\000\
\043\000\018\000\099\000\019\000\101\000\103\000\002\000\102\000\
\015\000\034\000\012\000\084\000"

let yycheck = "\007\000\
\011\000\012\000\001\001\002\001\001\000\050\000\011\001\012\001\
\053\000\002\001\021\001\019\000\002\001\022\001\013\001\014\001\
\009\001\002\001\023\001\030\000\028\000\002\001\021\001\026\001\
\023\001\070\000\034\000\035\000\036\000\037\000\038\000\039\000\
\040\000\041\000\042\000\043\000\007\001\008\001\026\001\010\001\
\027\001\052\000\023\000\024\000\021\001\025\001\054\000\055\000\
\056\000\057\000\058\000\029\001\060\000\061\000\062\000\063\000\
\064\000\068\000\022\001\028\001\021\001\024\001\024\001\022\001\
\024\001\067\000\024\001\024\001\024\001\001\001\002\001\003\001\
\004\001\005\001\006\001\083\000\024\001\024\001\024\001\024\001\
\088\000\013\001\014\001\015\001\016\001\017\001\018\001\019\001\
\020\001\021\001\024\001\023\001\022\001\101\000\022\001\024\001\
\022\001\024\001\029\001\065\000"

let yynames_const = "\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  CONST\000\
  FUN\000\
  REC\000\
  ECHO\000\
  INT\000\
  BOOL\000\
  TRUE\000\
  FALSE\000\
  NOT\000\
  AND\000\
  OR\000\
  EQ\000\
  LT\000\
  IF\000\
  LBRACKET\000\
  RBRACKET\000\
  LPAR\000\
  RPAR\000\
  COLON\000\
  SEMICOLON\000\
  COMMA\000\
  STAR\000\
  ARROW\000\
  "

let yynames_block = "\
  NUM\000\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmds) in
    Obj.repr(
# 28 "parser.mly"
                        ( ASTProg(_2) )
# 213 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 32 "parser.mly"
      (ASTStat(_1))
# 220 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 33 "parser.mly"
                      (ASTDec(_1,_3))
# 228 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 34 "parser.mly"
                       (ASTStats(_1,_3))
# 236 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 38 "parser.mly"
           (ASTEcho(_2))
# 243 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 42 "parser.mly"
                        (ASTConst(_2,_3,_4))
# 252 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 43 "parser.mly"
                                                (ASTFun(_2,_3,_5,_7))
# 262 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 44 "parser.mly"
                                                    (ASTFunRec(_3,_4,_6,_8))
# 272 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 48 "parser.mly"
      ( ASTIntType )
# 278 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "parser.mly"
         ( ASTBoolType )
# 284 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 50 "parser.mly"
                                ( ASTArrowType(_2,_4) )
# 292 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 54 "parser.mly"
        (ASTType(_1))
# 299 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast._type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.types) in
    Obj.repr(
# 55 "parser.mly"
                     (ASTTypes(_1,_3))
# 307 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 59 "parser.mly"
                     ( ASTArgFin(_1,_3) )
# 315 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 63 "parser.mly"
      (ASTArg(_1))
# 322 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.args) in
    Obj.repr(
# 64 "parser.mly"
                   ( ASTArgs(_1,_3))
# 330 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    Obj.repr(
# 68 "parser.mly"
      ( ASTTrue )
# 336 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "parser.mly"
         ( ASTFalse )
# 342 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 70 "parser.mly"
       ( ASTNum(_1) )
# 349 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 71 "parser.mly"
         ( ASTId(_1) )
# 356 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.oprim) in
    Obj.repr(
# 72 "parser.mly"
         ( ASTOprim(_1) )
# 363 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 73 "parser.mly"
                               (ASTLambda(_2,_4))
# 371 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprs) in
    Obj.repr(
# 74 "parser.mly"
                         (ASTApply(_2,_3))
# 379 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 75 "parser.mly"
                               (ASTIf(_3,_4,_5))
# 388 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 79 "parser.mly"
                           ( ASTBinary(Ast.Add, _3, _4) )
# 396 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 80 "parser.mly"
                              ( ASTBinary(Ast.Sub, _3, _4) )
# 404 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 81 "parser.mly"
                              ( ASTBinary(Ast.Mul, _3, _4) )
# 412 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 82 "parser.mly"
                            ( ASTBinary(Ast.Div, _3, _4) )
# 420 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 83 "parser.mly"
                       ( ASTUnary(Ast.Not, _3) )
# 427 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 84 "parser.mly"
                            ( ASTBinaryBool(Ast.And, _3, _4) )
# 435 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 85 "parser.mly"
                           ( ASTBinaryBool(Ast.Or, _3, _4) )
# 443 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 86 "parser.mly"
                           ( ASTBinaryBool(Ast.Eq, _3, _4) )
# 451 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 87 "parser.mly"
                           ( ASTBinaryBool(Ast.Lt, _3, _4) )
# 459 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 91 "parser.mly"
      (ASTExpr(_1))
# 466 "parser.ml"
               : Ast.exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 92 "parser.mly"
              (ASTExprs(_1,_2))
# 474 "parser.ml"
               : Ast.exprs))
(* Entry prog *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.prog)
