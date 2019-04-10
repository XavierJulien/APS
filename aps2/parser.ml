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
  | LEN
  | NTH
  | ALLOC
  | VEC

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Ast
# 48 "parser.ml"
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
  293 (* LEN *);
  294 (* NTH *);
  295 (* ALLOC *);
  296 (* VEC *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\012\000\013\000\013\000\003\000\
\003\000\003\000\003\000\003\000\004\000\004\000\004\000\004\000\
\004\000\004\000\005\000\005\000\005\000\005\000\005\000\006\000\
\006\000\007\000\008\000\008\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\010\000\010\000\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\003\000\001\000\005\000\002\000\
\003\000\004\000\003\000\003\000\004\000\007\000\008\000\003\000\
\006\000\007\000\001\000\001\000\005\000\001\000\004\000\001\000\
\003\000\003\000\001\000\003\000\001\000\001\000\001\000\001\000\
\001\000\004\000\004\000\006\000\005\000\004\000\004\000\005\000\
\005\000\005\000\005\000\004\000\005\000\005\000\005\000\005\000\
\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\051\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\031\000\032\000\029\000\030\000\000\000\
\000\000\008\000\033\000\000\000\000\000\000\000\000\000\006\000\
\000\000\000\000\000\000\000\000\001\000\000\000\000\000\019\000\
\020\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\016\000\
\000\000\000\000\000\000\009\000\000\000\000\000\011\000\000\000\
\012\000\004\000\003\000\000\000\000\000\000\000\013\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\
\050\000\000\000\000\000\000\000\000\000\000\000\026\000\028\000\
\034\000\000\000\000\000\000\000\000\000\044\000\000\000\000\000\
\000\000\000\000\000\000\039\000\000\000\038\000\035\000\000\000\
\000\000\000\000\005\000\023\000\025\000\000\000\000\000\000\000\
\040\000\041\000\042\000\043\000\045\000\046\000\047\000\048\000\
\000\000\037\000\017\000\000\000\007\000\021\000\014\000\000\000\
\036\000\018\000\015\000"

let yydgoto = "\002\000\
\004\000\014\000\015\000\016\000\077\000\078\000\048\000\049\000\
\072\000\073\000\027\000\070\000\033\000"

let yysindex = "\013\000\
\004\255\000\000\164\255\000\000\026\255\014\255\096\255\027\255\
\025\255\179\255\096\255\096\255\096\255\008\255\005\255\009\255\
\253\254\253\254\036\255\000\000\000\000\000\000\000\000\039\255\
\120\255\000\000\000\000\253\254\037\255\055\255\147\255\000\000\
\096\255\038\255\038\255\096\255\000\000\164\255\164\255\000\000\
\000\000\052\255\000\000\096\255\040\255\253\254\042\255\035\255\
\043\255\096\255\096\255\096\255\096\255\096\255\096\255\096\255\
\096\255\096\255\096\255\096\255\096\255\096\255\096\255\000\000\
\039\255\047\255\179\255\000\000\164\255\038\255\000\000\096\255\
\000\000\000\000\000\000\253\254\041\255\044\255\000\000\039\255\
\050\255\253\254\039\255\096\255\096\255\096\255\096\255\096\255\
\048\255\096\255\096\255\096\255\096\255\096\255\058\255\096\255\
\066\255\067\255\071\255\039\255\096\255\096\255\074\255\000\000\
\000\000\075\255\253\254\253\254\079\255\039\255\000\000\000\000\
\000\000\080\255\081\255\082\255\083\255\000\000\084\255\087\255\
\088\255\089\255\096\255\000\000\090\255\000\000\000\000\038\255\
\093\255\094\255\000\000\000\000\000\000\103\255\096\255\107\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\106\255\000\000\000\000\038\255\000\000\000\000\000\000\096\255\
\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\109\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\110\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\247\254\
\000\000\000\000\000\000\000\000\045\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\219\255\000\000\000\000\250\255\252\255\000\000\212\255\
\249\255\203\255\000\000\228\255\075\000"

let yytablesize = 202
let yytable = "\026\000\
\074\000\075\000\032\000\034\000\035\000\036\000\071\000\040\000\
\041\000\098\000\044\000\045\000\049\000\001\000\049\000\018\000\
\049\000\063\000\105\000\042\000\099\000\064\000\019\000\063\000\
\003\000\068\000\029\000\017\000\028\000\037\000\038\000\103\000\
\043\000\030\000\039\000\109\000\079\000\046\000\112\000\081\000\
\047\000\104\000\085\000\086\000\087\000\088\000\089\000\090\000\
\091\000\092\000\093\000\094\000\095\000\096\000\097\000\129\000\
\066\000\065\000\069\000\101\000\080\000\083\000\040\000\041\000\
\084\000\136\000\082\000\100\000\107\000\106\000\110\000\118\000\
\108\000\024\000\042\000\111\000\113\000\114\000\115\000\116\000\
\117\000\124\000\119\000\120\000\121\000\122\000\123\000\043\000\
\125\000\126\000\127\000\076\000\128\000\125\000\130\000\131\000\
\020\000\021\000\132\000\147\000\135\000\134\000\133\000\137\000\
\138\000\139\000\140\000\141\000\022\000\023\000\142\000\143\000\
\144\000\146\000\148\000\145\000\024\000\149\000\025\000\154\000\
\020\000\021\000\050\000\051\000\052\000\053\000\150\000\151\000\
\152\000\153\000\002\000\027\000\022\000\023\000\054\000\055\000\
\056\000\057\000\058\000\059\000\024\000\102\000\025\000\000\000\
\155\000\000\000\000\000\020\000\021\000\050\000\051\000\052\000\
\053\000\000\000\000\000\000\000\060\000\061\000\062\000\022\000\
\023\000\054\000\055\000\056\000\057\000\058\000\059\000\024\000\
\000\000\025\000\005\000\006\000\000\000\007\000\000\000\000\000\
\000\000\000\000\000\000\020\000\021\000\000\000\000\000\060\000\
\067\000\062\000\000\000\000\000\000\000\000\000\000\000\022\000\
\023\000\008\000\009\000\010\000\011\000\012\000\013\000\024\000\
\000\000\031\000"

let yycheck = "\007\000\
\038\000\039\000\010\000\011\000\012\000\013\000\035\000\011\001\
\012\001\063\000\017\000\018\000\022\001\001\000\024\001\002\001\
\026\001\025\000\072\000\023\001\065\000\028\000\009\001\031\000\
\021\001\033\000\002\001\002\001\002\001\022\001\026\001\069\000\
\036\001\009\001\026\001\080\000\044\000\002\001\083\000\046\000\
\002\001\070\000\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\060\000\061\000\062\000\100\000\
\002\001\021\001\021\001\067\000\021\001\027\001\011\001\012\001\
\022\001\110\000\025\001\021\001\028\001\076\000\021\001\024\001\
\029\001\029\001\023\001\082\000\084\000\085\000\086\000\087\000\
\088\000\024\001\090\000\091\000\092\000\093\000\094\000\036\001\
\096\000\024\001\024\001\040\001\022\001\101\000\102\000\022\001\
\001\001\002\001\024\001\128\000\022\001\108\000\107\000\024\001\
\024\001\024\001\024\001\024\001\013\001\014\001\024\001\024\001\
\024\001\024\001\022\001\123\000\021\001\024\001\023\001\148\000\
\001\001\002\001\003\001\004\001\005\001\006\001\024\001\135\000\
\022\001\024\001\022\001\022\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\067\000\023\001\255\255\
\152\000\255\255\255\255\001\001\002\001\003\001\004\001\005\001\
\006\001\255\255\255\255\255\255\037\001\038\001\039\001\013\001\
\014\001\015\001\016\001\017\001\018\001\019\001\020\001\021\001\
\255\255\023\001\007\001\008\001\255\255\010\001\255\255\255\255\
\255\255\255\255\255\255\001\001\002\001\255\255\255\255\037\001\
\038\001\039\001\255\255\255\255\255\255\255\255\255\255\013\001\
\014\001\030\001\031\001\032\001\033\001\034\001\035\001\021\001\
\255\255\023\001"

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
  LEN\000\
  NTH\000\
  ALLOC\000\
  VEC\000\
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
# 37 "parser.mly"
                        ( ASTProg(_2) )
# 297 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 41 "parser.mly"
      (ASTStat(_1))
# 304 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 42 "parser.mly"
                      (ASTDec(_1,_3))
# 312 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 43 "parser.mly"
                       (ASTStats(_1,_3))
# 320 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmds) in
    Obj.repr(
# 48 "parser.mly"
                        ( ASTBlock(_2) )
# 327 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 54 "parser.mly"
      ( ASTLId(_1))
# 334 "parser.ml"
               : Ast.lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 55 "parser.mly"
                           ( ASTLNth(_3,_4) )
# 342 "parser.ml"
               : Ast.lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 60 "parser.mly"
           (ASTEcho(_2))
# 349 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 62 "parser.mly"
                 (ASTSet(_2,_3))
# 357 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 63 "parser.mly"
                        (ASTBIf(_2,_3,_4))
# 366 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 64 "parser.mly"
                    (ASTWhile(_2,_3))
# 374 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 65 "parser.mly"
                   (ASTCall(_2,_3))
# 382 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 71 "parser.mly"
                        (ASTConst(_2,_3,_4))
# 391 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 72 "parser.mly"
                                                (ASTFun(_2,_3,_5,_7))
# 401 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 73 "parser.mly"
                                                    (ASTFunRec(_3,_4,_6,_8))
# 411 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 75 "parser.mly"
                   (ASTVar(_2,_3))
# 419 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 76 "parser.mly"
                                           (ASTProc(_2,_4,_6))
# 428 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 77 "parser.mly"
                                               (ASTProcRec(_3,_5,_7))
# 437 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "parser.mly"
      ( ASTIntType )
# 443 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 83 "parser.mly"
         ( ASTBoolType )
# 449 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 84 "parser.mly"
                                ( ASTArrowType(_2,_4) )
# 457 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 86 "parser.mly"
         ( ASTVoidType )
# 463 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 88 "parser.mly"
                       ( ASTVecType(_3))
# 470 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 93 "parser.mly"
        (ASTType(_1))
# 477 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast._type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.types) in
    Obj.repr(
# 94 "parser.mly"
                     (ASTTypes(_1,_3))
# 485 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 98 "parser.mly"
                     ( ASTArgFin(_1,_3) )
# 493 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 102 "parser.mly"
      (ASTArg(_1))
# 500 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.args) in
    Obj.repr(
# 103 "parser.mly"
                   ( ASTArgs(_1,_3))
# 508 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    Obj.repr(
# 107 "parser.mly"
      ( ASTTrue )
# 514 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "parser.mly"
         ( ASTFalse )
# 520 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 109 "parser.mly"
       ( ASTNum(_1) )
# 527 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 110 "parser.mly"
         ( ASTId(_1) )
# 534 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.oprim) in
    Obj.repr(
# 111 "parser.mly"
         ( ASTOprim(_1) )
# 541 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 112 "parser.mly"
                               (ASTLambda(_2,_4))
# 549 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprs) in
    Obj.repr(
# 113 "parser.mly"
                         (ASTApply(_2,_3))
# 557 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 114 "parser.mly"
                               (ASTIf(_3,_4,_5))
# 566 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 116 "parser.mly"
                           ( ASTENth(_3,_4) )
# 574 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 117 "parser.mly"
                        (ASTAlloc(_3))
# 581 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 118 "parser.mly"
                      (ASTLen(_3))
# 588 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 122 "parser.mly"
                           ( ASTBinary(Ast.Add, _3, _4) )
# 596 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 123 "parser.mly"
                              ( ASTBinary(Ast.Sub, _3, _4) )
# 604 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 124 "parser.mly"
                              ( ASTBinary(Ast.Mul, _3, _4) )
# 612 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 125 "parser.mly"
                            ( ASTBinary(Ast.Div, _3, _4) )
# 620 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 126 "parser.mly"
                       ( ASTUnary(Ast.Not, _3) )
# 627 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 127 "parser.mly"
                            ( ASTBinary(Ast.And, _3, _4) )
# 635 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 128 "parser.mly"
                           ( ASTBinary(Ast.Or, _3, _4) )
# 643 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 129 "parser.mly"
                           ( ASTBinary(Ast.Eq, _3, _4) )
# 651 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 130 "parser.mly"
                           ( ASTBinary(Ast.Lt, _3, _4) )
# 659 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 134 "parser.mly"
      (ASTExpr(_1))
# 666 "parser.ml"
               : Ast.exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 135 "parser.mly"
              (ASTExprs(_1,_2))
# 674 "parser.ml"
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
