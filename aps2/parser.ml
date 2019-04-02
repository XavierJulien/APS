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
\003\000\003\000\003\000\003\000\003\000\004\000\004\000\004\000\
\004\000\004\000\004\000\005\000\005\000\005\000\005\000\005\000\
\006\000\006\000\007\000\008\000\008\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\010\000\010\000\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\003\000\001\000\005\000\002\000\
\003\000\004\000\003\000\003\000\003\000\004\000\007\000\008\000\
\003\000\006\000\007\000\001\000\001\000\005\000\001\000\004\000\
\001\000\003\000\003\000\001\000\003\000\001\000\001\000\001\000\
\001\000\001\000\004\000\004\000\006\000\005\000\004\000\004\000\
\005\000\005\000\005\000\005\000\004\000\005\000\005\000\005\000\
\005\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\052\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\032\000\033\000\030\000\031\000\000\000\
\000\000\008\000\034\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\001\000\000\000\000\000\020\000\
\021\000\000\000\023\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\017\000\
\000\000\000\000\009\000\000\000\013\000\000\000\000\000\011\000\
\000\000\012\000\004\000\003\000\000\000\000\000\000\000\014\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\
\010\000\051\000\000\000\000\000\000\000\000\000\000\000\027\000\
\029\000\035\000\000\000\000\000\000\000\000\000\045\000\000\000\
\000\000\000\000\000\000\000\000\040\000\000\000\039\000\036\000\
\000\000\000\000\000\000\005\000\024\000\026\000\000\000\000\000\
\000\000\041\000\042\000\043\000\044\000\046\000\047\000\048\000\
\049\000\000\000\038\000\018\000\000\000\007\000\022\000\015\000\
\000\000\037\000\019\000\016\000"

let yydgoto = "\002\000\
\004\000\014\000\015\000\016\000\078\000\079\000\048\000\049\000\
\073\000\074\000\027\000\071\000\033\000"

let yysindex = "\024\000\
\006\255\000\000\067\255\000\000\026\255\014\255\136\255\029\255\
\027\255\009\255\136\255\136\255\136\255\011\255\016\255\031\255\
\254\254\254\254\038\255\000\000\000\000\000\000\000\000\057\255\
\105\255\000\000\000\000\254\254\039\255\060\255\136\255\025\255\
\136\255\043\255\043\255\136\255\000\000\067\255\067\255\000\000\
\000\000\124\255\000\000\136\255\044\255\254\254\041\255\042\255\
\048\255\136\255\136\255\136\255\136\255\136\255\136\255\136\255\
\136\255\136\255\136\255\136\255\136\255\136\255\136\255\000\000\
\057\255\050\255\000\000\012\255\000\000\067\255\043\255\000\000\
\136\255\000\000\000\000\000\000\254\254\045\255\047\255\000\000\
\057\255\051\255\254\254\057\255\136\255\136\255\136\255\136\255\
\136\255\059\255\136\255\136\255\136\255\136\255\136\255\065\255\
\136\255\068\255\070\255\069\255\057\255\000\000\136\255\073\255\
\000\000\000\000\079\255\254\254\254\254\082\255\057\255\000\000\
\000\000\000\000\081\255\088\255\089\255\091\255\000\000\092\255\
\103\255\106\255\107\255\136\255\000\000\108\255\000\000\000\000\
\043\255\111\255\115\255\000\000\000\000\000\000\116\255\136\255\
\119\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\121\255\000\000\000\000\043\255\000\000\000\000\000\000\
\136\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\126\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\129\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\249\254\000\000\000\000\000\000\000\000\123\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\225\255\000\000\000\000\240\255\045\000\000\000\213\255\
\249\255\196\255\000\000\241\255\086\000"

let yytablesize = 164
let yytable = "\026\000\
\044\000\045\000\099\000\034\000\035\000\036\000\075\000\076\000\
\040\000\041\000\031\000\064\000\106\000\102\000\050\000\018\000\
\050\000\063\000\050\000\072\000\042\000\100\000\019\000\067\000\
\001\000\069\000\003\000\017\000\029\000\082\000\028\000\032\000\
\037\000\043\000\032\000\030\000\080\000\110\000\104\000\046\000\
\113\000\038\000\086\000\087\000\088\000\089\000\090\000\091\000\
\092\000\093\000\094\000\095\000\096\000\097\000\098\000\105\000\
\039\000\130\000\047\000\065\000\107\000\066\000\068\000\070\000\
\081\000\083\000\112\000\137\000\084\000\085\000\101\000\111\000\
\108\000\005\000\006\000\109\000\007\000\114\000\115\000\116\000\
\117\000\118\000\119\000\120\000\121\000\122\000\123\000\124\000\
\125\000\126\000\129\000\127\000\135\000\128\000\132\000\131\000\
\008\000\009\000\010\000\011\000\012\000\013\000\133\000\136\000\
\138\000\020\000\021\000\050\000\051\000\052\000\053\000\139\000\
\140\000\148\000\141\000\142\000\146\000\022\000\023\000\054\000\
\055\000\056\000\057\000\058\000\059\000\024\000\143\000\025\000\
\152\000\144\000\145\000\147\000\149\000\155\000\040\000\041\000\
\020\000\021\000\150\000\151\000\153\000\060\000\061\000\062\000\
\154\000\156\000\042\000\002\000\022\000\023\000\028\000\025\000\
\134\000\103\000\000\000\000\000\024\000\000\000\025\000\043\000\
\000\000\000\000\000\000\077\000"

let yycheck = "\007\000\
\017\000\018\000\063\000\011\000\012\000\013\000\038\000\039\000\
\011\001\012\001\002\001\028\000\073\000\002\001\022\001\002\001\
\024\001\025\000\026\001\035\000\023\001\065\000\009\001\031\000\
\001\000\033\000\021\001\002\001\002\001\046\000\002\001\023\001\
\022\001\036\001\023\001\009\001\044\000\081\000\070\000\002\001\
\084\000\026\001\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\060\000\061\000\062\000\071\000\
\026\001\101\000\002\001\021\001\077\000\002\001\038\001\021\001\
\021\001\025\001\083\000\111\000\027\001\022\001\021\001\021\001\
\028\001\007\001\008\001\029\001\010\001\085\000\086\000\087\000\
\088\000\089\000\024\001\091\000\092\000\093\000\094\000\095\000\
\024\001\097\000\022\001\024\001\109\000\024\001\022\001\103\000\
\030\001\031\001\032\001\033\001\034\001\035\001\024\001\022\001\
\024\001\001\001\002\001\003\001\004\001\005\001\006\001\024\001\
\024\001\129\000\024\001\024\001\124\000\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\024\001\023\001\
\136\000\024\001\024\001\024\001\022\001\149\000\011\001\012\001\
\001\001\002\001\024\001\024\001\022\001\037\001\038\001\039\001\
\024\001\153\000\023\001\022\001\013\001\014\001\022\001\029\001\
\108\000\068\000\255\255\255\255\021\001\255\255\023\001\036\001\
\255\255\255\255\255\255\040\001"

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
# 287 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 41 "parser.mly"
      (ASTStat(_1))
# 294 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 42 "parser.mly"
                      (ASTDec(_1,_3))
# 302 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 43 "parser.mly"
                       (ASTStats(_1,_3))
# 310 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmds) in
    Obj.repr(
# 48 "parser.mly"
                        ( ASTBlock(_2) )
# 317 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
       ( ASTLId(_1))
# 324 "parser.ml"
               : Ast.lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 55 "parser.mly"
                           ( ASTLNth(_3,_4) )
# 332 "parser.ml"
               : Ast.lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 60 "parser.mly"
           (ASTEcho(_2))
# 339 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 62 "parser.mly"
                  (ASTSet(_2,_3))
# 347 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 63 "parser.mly"
                        (ASTBIf(_2,_3,_4))
# 356 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 64 "parser.mly"
                    (ASTWhile(_2,_3))
# 364 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 65 "parser.mly"
                   (ASTCall(_2,_3))
# 372 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 67 "parser.mly"
                 (ASTLval(_2,_3))
# 380 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 72 "parser.mly"
                        (ASTConst(_2,_3,_4))
# 389 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 73 "parser.mly"
                                                (ASTFun(_2,_3,_5,_7))
# 399 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 74 "parser.mly"
                                                    (ASTFunRec(_3,_4,_6,_8))
# 409 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 76 "parser.mly"
                   (ASTVar(_2,_3))
# 417 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 77 "parser.mly"
                                           (ASTProc(_2,_4,_6))
# 426 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 78 "parser.mly"
                                               (ASTProcRec(_3,_5,_7))
# 435 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 83 "parser.mly"
      ( ASTIntType )
# 441 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "parser.mly"
         ( ASTBoolType )
# 447 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 85 "parser.mly"
                                ( ASTArrowType(_2,_4) )
# 455 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 87 "parser.mly"
         ( ASTVoidType )
# 461 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 89 "parser.mly"
                       ( ASTVecType(_3))
# 468 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 94 "parser.mly"
        (ASTType(_1))
# 475 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast._type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.types) in
    Obj.repr(
# 95 "parser.mly"
                     (ASTTypes(_1,_3))
# 483 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 99 "parser.mly"
                     ( ASTArgFin(_1,_3) )
# 491 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 103 "parser.mly"
      (ASTArg(_1))
# 498 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.args) in
    Obj.repr(
# 104 "parser.mly"
                   ( ASTArgs(_1,_3))
# 506 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "parser.mly"
      ( ASTTrue )
# 512 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 109 "parser.mly"
         ( ASTFalse )
# 518 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 110 "parser.mly"
       ( ASTNum(_1) )
# 525 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 111 "parser.mly"
         ( ASTId(_1) )
# 532 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.oprim) in
    Obj.repr(
# 112 "parser.mly"
         ( ASTOprim(_1) )
# 539 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 113 "parser.mly"
                               (ASTLambda(_2,_4))
# 547 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprs) in
    Obj.repr(
# 114 "parser.mly"
                         (ASTApply(_2,_3))
# 555 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 115 "parser.mly"
                               (ASTIf(_3,_4,_5))
# 564 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 117 "parser.mly"
                           ( ASTENth(_3,_4) )
# 572 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 118 "parser.mly"
                        (ASTAlloc(_3))
# 579 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 119 "parser.mly"
                      (ASTLen(_3))
# 586 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 123 "parser.mly"
                           ( ASTBinary(Ast.Add, _3, _4) )
# 594 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 124 "parser.mly"
                              ( ASTBinary(Ast.Sub, _3, _4) )
# 602 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 125 "parser.mly"
                              ( ASTBinary(Ast.Mul, _3, _4) )
# 610 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 126 "parser.mly"
                            ( ASTBinary(Ast.Div, _3, _4) )
# 618 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 127 "parser.mly"
                       ( ASTUnary(Ast.Not, _3) )
# 625 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 128 "parser.mly"
                            ( ASTBinary(Ast.And, _3, _4) )
# 633 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 129 "parser.mly"
                           ( ASTBinary(Ast.Or, _3, _4) )
# 641 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 130 "parser.mly"
                           ( ASTBinary(Ast.Eq, _3, _4) )
# 649 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 131 "parser.mly"
                           ( ASTBinary(Ast.Lt, _3, _4) )
# 657 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 135 "parser.mly"
      (ASTExpr(_1))
# 664 "parser.ml"
               : Ast.exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 136 "parser.mly"
              (ASTExprs(_1,_2))
# 672 "parser.ml"
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
