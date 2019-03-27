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
  | VAR
  | PROC
  | SET
  | BIF
  | WHILE
  | CALL
  | VOID

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Ast
# 44 "parser.ml"
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
  286 (* VAR *);
  287 (* PROC *);
  288 (* SET *);
  289 (* BIF *);
  290 (* WHILE *);
  291 (* CALL *);
  292 (* VOID *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\012\000\003\000\003\000\003\000\
\003\000\003\000\004\000\004\000\004\000\004\000\004\000\004\000\
\005\000\005\000\005\000\005\000\006\000\006\000\007\000\008\000\
\008\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\010\000\010\000\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\003\000\002\000\003\000\004\000\
\003\000\003\000\004\000\007\000\008\000\003\000\006\000\007\000\
\001\000\001\000\005\000\001\000\001\000\003\000\003\000\001\000\
\003\000\001\000\001\000\001\000\001\000\001\000\004\000\004\000\
\006\000\005\000\005\000\005\000\005\000\004\000\005\000\005\000\
\005\000\005\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\045\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\028\000\029\000\026\000\027\000\000\000\
\000\000\006\000\030\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\001\000\000\000\000\000\017\000\018\000\000\000\
\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\014\000\000\000\000\000\007\000\000\000\000\000\
\009\000\000\000\010\000\004\000\003\000\000\000\000\000\011\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\008\000\044\000\000\000\000\000\000\000\
\000\000\023\000\025\000\031\000\000\000\000\000\000\000\000\000\
\038\000\000\000\000\000\000\000\000\000\000\000\032\000\000\000\
\000\000\005\000\022\000\000\000\000\000\000\000\034\000\035\000\
\036\000\037\000\039\000\040\000\041\000\042\000\000\000\015\000\
\000\000\019\000\012\000\000\000\033\000\016\000\013\000"

let yydgoto = "\002\000\
\004\000\014\000\015\000\016\000\070\000\071\000\046\000\047\000\
\066\000\067\000\027\000\064\000"

let yysindex = "\011\000\
\248\254\000\000\022\255\000\000\020\255\019\255\126\255\021\255\
\049\255\126\255\126\255\126\255\126\255\003\255\000\255\011\255\
\004\255\004\255\058\255\000\000\000\000\000\000\000\000\060\255\
\103\255\000\000\000\000\004\255\018\255\062\255\126\255\044\255\
\044\255\126\255\000\000\022\255\022\255\000\000\000\000\004\255\
\000\000\126\255\045\255\004\255\043\255\042\255\053\255\126\255\
\126\255\126\255\126\255\126\255\126\255\126\255\126\255\126\255\
\126\255\126\255\000\000\060\255\061\255\000\000\022\255\044\255\
\000\000\126\255\000\000\000\000\000\000\055\255\056\255\000\000\
\060\255\063\255\004\255\060\255\126\255\126\255\126\255\126\255\
\126\255\064\255\126\255\126\255\126\255\126\255\126\255\065\255\
\068\255\060\255\069\255\000\000\000\000\004\255\004\255\070\255\
\060\255\000\000\000\000\000\000\071\255\072\255\073\255\075\255\
\000\000\076\255\077\255\078\255\087\255\126\255\000\000\044\255\
\090\255\000\000\000\000\089\255\126\255\092\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\091\255\000\000\
\044\255\000\000\000\000\126\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\107\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\108\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\037\255\000\000\000\000\000\000\057\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\227\255\000\000\000\000\248\255\255\255\000\000\197\255\
\249\255\209\255\000\000\225\255"

let yytablesize = 149
let yytable = "\026\000\
\089\000\065\000\031\000\032\000\033\000\034\000\068\000\069\000\
\042\000\043\000\088\000\001\000\003\000\096\000\038\000\039\000\
\099\000\058\000\093\000\059\000\018\000\017\000\028\000\062\000\
\035\000\036\000\040\000\019\000\005\000\006\000\113\000\007\000\
\092\000\091\000\072\000\074\000\037\000\118\000\060\000\041\000\
\078\000\079\000\080\000\081\000\082\000\083\000\084\000\085\000\
\086\000\087\000\029\000\008\000\009\000\010\000\011\000\012\000\
\013\000\030\000\043\000\044\000\043\000\045\000\043\000\061\000\
\063\000\073\000\098\000\075\000\076\000\100\000\101\000\102\000\
\103\000\104\000\077\000\106\000\107\000\108\000\109\000\110\000\
\128\000\090\000\094\000\097\000\095\000\021\000\116\000\105\000\
\111\000\112\000\114\000\117\000\115\000\000\000\119\000\120\000\
\121\000\134\000\122\000\123\000\124\000\125\000\127\000\020\000\
\021\000\048\000\049\000\050\000\051\000\131\000\126\000\129\000\
\130\000\132\000\133\000\022\000\023\000\052\000\053\000\054\000\
\055\000\056\000\057\000\024\000\135\000\025\000\020\000\021\000\
\002\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\022\000\023\000\000\000\000\000\000\000\000\000\
\000\000\000\000\024\000\000\000\025\000"

let yycheck = "\007\000\
\060\000\033\000\010\000\011\000\012\000\013\000\036\000\037\000\
\017\000\018\000\058\000\001\000\021\001\073\000\011\001\012\001\
\076\000\025\000\066\000\028\000\002\001\002\001\002\001\031\000\
\022\001\026\001\023\001\009\001\007\001\008\001\090\000\010\001\
\064\000\063\000\042\000\044\000\026\001\097\000\021\001\036\001\
\048\000\049\000\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\002\001\030\001\031\001\032\001\033\001\034\001\
\035\001\009\001\022\001\002\001\024\001\002\001\026\001\002\001\
\021\001\021\001\075\000\025\001\027\001\077\000\078\000\079\000\
\080\000\081\000\022\001\083\000\084\000\085\000\086\000\087\000\
\112\000\021\001\028\001\021\001\029\001\029\001\095\000\024\001\
\024\001\022\001\022\001\022\001\094\000\255\255\024\001\024\001\
\024\001\129\000\024\001\024\001\024\001\024\001\110\000\001\001\
\002\001\003\001\004\001\005\001\006\001\117\000\024\001\022\001\
\024\001\022\001\024\001\013\001\014\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\132\000\023\001\001\001\002\001\
\022\001\022\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\013\001\014\001\255\255\255\255\255\255\255\255\
\255\255\255\255\021\001\255\255\023\001"

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
  VAR\000\
  PROC\000\
  SET\000\
  BIF\000\
  WHILE\000\
  CALL\000\
  VOID\000\
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
# 33 "parser.mly"
                        ( ASTProg(_2) )
# 260 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 37 "parser.mly"
      (ASTStat(_1))
# 267 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 38 "parser.mly"
                      (ASTDec(_1,_3))
# 275 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 39 "parser.mly"
                       (ASTStats(_1,_3))
# 283 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmds) in
    Obj.repr(
# 44 "parser.mly"
                        ( ASTBlock(_2) )
# 290 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 49 "parser.mly"
           (ASTEcho(_2))
# 297 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 51 "parser.mly"
                 (ASTSet(_2,_3))
# 305 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 52 "parser.mly"
                        (ASTBIf(_2,_3,_4))
# 314 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 53 "parser.mly"
                    (ASTWhile(_2,_3))
# 322 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 54 "parser.mly"
                   (ASTCall(_2,_3))
# 330 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 59 "parser.mly"
                        (ASTConst(_2,_3,_4))
# 339 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 60 "parser.mly"
                                                (ASTFun(_2,_3,_5,_7))
# 349 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 61 "parser.mly"
                                                    (ASTFunRec(_3,_4,_6,_8))
# 359 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 63 "parser.mly"
                   (ASTVar(_2,_3))
# 367 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 64 "parser.mly"
                                           (ASTProc(_2,_4,_6))
# 376 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 65 "parser.mly"
                                               (ASTProcRec(_3,_5,_7))
# 385 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
      ( ASTIntType )
# 391 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "parser.mly"
         ( ASTBoolType )
# 397 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 72 "parser.mly"
                                ( ASTArrowType(_2,_4) )
# 405 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
         ( ASTVoidType )
# 411 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 79 "parser.mly"
        (ASTType(_1))
# 418 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast._type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.types) in
    Obj.repr(
# 80 "parser.mly"
                     (ASTTypes(_1,_3))
# 426 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 84 "parser.mly"
                     ( ASTArgFin(_1,_3) )
# 434 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 88 "parser.mly"
      (ASTArg(_1))
# 441 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.args) in
    Obj.repr(
# 89 "parser.mly"
                   ( ASTArgs(_1,_3))
# 449 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    Obj.repr(
# 93 "parser.mly"
      ( ASTTrue )
# 455 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 94 "parser.mly"
         ( ASTFalse )
# 461 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 95 "parser.mly"
       ( ASTNum(_1) )
# 468 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 96 "parser.mly"
         ( ASTId(_1) )
# 475 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.oprim) in
    Obj.repr(
# 97 "parser.mly"
         ( ASTOprim(_1) )
# 482 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 98 "parser.mly"
                               (ASTLambda(_2,_4))
# 490 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprs) in
    Obj.repr(
# 99 "parser.mly"
                         (ASTApply(_2,_3))
# 498 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 100 "parser.mly"
                               (ASTIf(_3,_4,_5))
# 507 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 104 "parser.mly"
                           ( ASTBinary(Ast.Add, _3, _4) )
# 515 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 105 "parser.mly"
                              ( ASTBinary(Ast.Sub, _3, _4) )
# 523 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 106 "parser.mly"
                              ( ASTBinary(Ast.Mul, _3, _4) )
# 531 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 107 "parser.mly"
                            ( ASTBinary(Ast.Div, _3, _4) )
# 539 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 108 "parser.mly"
                       ( ASTUnary(Ast.Not, _3) )
# 546 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 109 "parser.mly"
                            ( ASTBinary(Ast.And, _3, _4) )
# 554 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 110 "parser.mly"
                           ( ASTBinary(Ast.Or, _3, _4) )
# 562 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 111 "parser.mly"
                           ( ASTBinary(Ast.Eq, _3, _4) )
# 570 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 112 "parser.mly"
                           ( ASTBinary(Ast.Lt, _3, _4) )
# 578 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 116 "parser.mly"
      (ASTExpr(_1))
# 585 "parser.ml"
               : Ast.exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 117 "parser.mly"
              (ASTExprs(_1,_2))
# 593 "parser.ml"
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
