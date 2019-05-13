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
\000\000\008\000\033\000\000\000\000\000\000\000\006\000\000\000\
\000\000\000\000\000\000\000\000\001\000\000\000\000\000\019\000\
\020\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\016\000\
\000\000\000\000\000\000\009\000\000\000\000\000\011\000\000\000\
\012\000\004\000\003\000\000\000\000\000\000\000\013\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\010\000\050\000\
\000\000\000\000\000\000\000\000\000\000\026\000\028\000\034\000\
\000\000\000\000\000\000\000\000\044\000\000\000\000\000\000\000\
\000\000\000\000\039\000\000\000\038\000\035\000\000\000\000\000\
\000\000\005\000\023\000\025\000\000\000\000\000\000\000\040\000\
\041\000\042\000\043\000\045\000\046\000\047\000\048\000\000\000\
\037\000\017\000\000\000\007\000\021\000\014\000\000\000\036\000\
\018\000\015\000"

let yydgoto = "\002\000\
\004\000\014\000\015\000\016\000\077\000\078\000\048\000\049\000\
\072\000\073\000\027\000\070\000\033\000"

let yysindex = "\015\000\
\252\254\000\000\104\255\000\000\018\255\010\255\144\255\026\255\
\013\255\009\255\144\255\144\255\144\255\008\255\007\255\014\255\
\254\254\254\254\033\255\000\000\000\000\000\000\000\000\039\255\
\103\255\000\000\000\000\254\254\035\255\055\255\000\000\020\255\
\144\255\041\255\041\255\144\255\000\000\104\255\104\255\000\000\
\000\000\059\255\000\000\144\255\042\255\254\254\040\255\037\255\
\038\255\144\255\144\255\144\255\144\255\144\255\144\255\144\255\
\144\255\144\255\144\255\144\255\144\255\144\255\144\255\000\000\
\039\255\045\255\009\255\000\000\104\255\041\255\000\000\144\255\
\000\000\000\000\000\000\254\254\044\255\046\255\000\000\039\255\
\048\255\254\254\039\255\144\255\144\255\144\255\144\255\144\255\
\049\255\144\255\144\255\144\255\144\255\144\255\050\255\144\255\
\052\255\064\255\068\255\039\255\144\255\069\255\000\000\000\000\
\072\255\254\254\254\254\075\255\039\255\000\000\000\000\000\000\
\074\255\076\255\077\255\078\255\000\000\079\255\086\255\101\255\
\105\255\144\255\000\000\106\255\000\000\000\000\041\255\109\255\
\108\255\000\000\000\000\000\000\119\255\144\255\111\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\123\255\
\000\000\000\000\041\255\000\000\000\000\000\000\144\255\000\000\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\126\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\127\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\255\
\000\000\000\000\000\000\000\000\099\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\225\255\000\000\000\000\241\255\044\000\000\000\215\255\
\249\255\207\255\000\000\222\255\084\000"

let yytablesize = 167
let yytable = "\026\000\
\071\000\044\000\045\000\034\000\035\000\036\000\074\000\075\000\
\040\000\041\000\031\000\018\000\064\000\098\000\029\000\001\000\
\003\000\063\000\019\000\017\000\042\000\030\000\104\000\099\000\
\049\000\068\000\049\000\028\000\049\000\037\000\081\000\032\000\
\038\000\043\000\046\000\103\000\079\000\102\000\108\000\039\000\
\047\000\111\000\085\000\086\000\087\000\088\000\089\000\090\000\
\091\000\092\000\093\000\094\000\095\000\096\000\097\000\065\000\
\066\000\067\000\128\000\084\000\105\000\069\000\080\000\083\000\
\082\000\100\000\110\000\135\000\109\000\040\000\041\000\106\000\
\117\000\123\000\107\000\125\000\112\000\113\000\114\000\115\000\
\116\000\042\000\118\000\119\000\120\000\121\000\122\000\126\000\
\124\000\127\000\130\000\133\000\146\000\129\000\043\000\131\000\
\134\000\136\000\076\000\137\000\138\000\139\000\140\000\020\000\
\021\000\050\000\051\000\052\000\053\000\141\000\005\000\006\000\
\153\000\007\000\144\000\022\000\023\000\054\000\055\000\056\000\
\057\000\058\000\059\000\024\000\142\000\025\000\150\000\024\000\
\143\000\145\000\147\000\148\000\151\000\008\000\009\000\010\000\
\011\000\012\000\013\000\060\000\061\000\062\000\149\000\154\000\
\020\000\021\000\152\000\002\000\027\000\132\000\101\000\000\000\
\000\000\000\000\000\000\000\000\022\000\023\000\000\000\000\000\
\000\000\000\000\000\000\000\000\024\000\000\000\025\000"

let yycheck = "\007\000\
\035\000\017\000\018\000\011\000\012\000\013\000\038\000\039\000\
\011\001\012\001\002\001\002\001\028\000\063\000\002\001\001\000\
\021\001\025\000\009\001\002\001\023\001\009\001\072\000\065\000\
\022\001\033\000\024\001\002\001\026\001\022\001\046\000\023\001\
\026\001\036\001\002\001\070\000\044\000\069\000\080\000\026\001\
\002\001\083\000\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\060\000\061\000\062\000\021\001\
\002\001\038\001\100\000\022\001\076\000\021\001\021\001\027\001\
\025\001\021\001\082\000\109\000\021\001\011\001\012\001\028\001\
\024\001\024\001\029\001\024\001\084\000\085\000\086\000\087\000\
\088\000\023\001\090\000\091\000\092\000\093\000\094\000\024\001\
\096\000\022\001\022\001\107\000\127\000\101\000\036\001\024\001\
\022\001\024\001\040\001\024\001\024\001\024\001\024\001\001\001\
\002\001\003\001\004\001\005\001\006\001\024\001\007\001\008\001\
\147\000\010\001\122\000\013\001\014\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\024\001\023\001\134\000\029\001\
\024\001\024\001\022\001\024\001\022\001\030\001\031\001\032\001\
\033\001\034\001\035\001\037\001\038\001\039\001\024\001\151\000\
\001\001\002\001\024\001\022\001\022\001\106\000\067\000\255\255\
\255\255\255\255\255\255\255\255\013\001\014\001\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001"

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
       ( ASTLId(ASTId(_1)))
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
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.lval) in
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
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 71 "parser.mly"
                        (ASTConst(_2,_3,_4))
# 381 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 72 "parser.mly"
                                                (ASTFun(_2,_3,_5,_7))
# 391 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 73 "parser.mly"
                                                    (ASTFunRec(_3,_4,_6,_8))
# 401 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 75 "parser.mly"
                   (ASTVar(_2,_3))
# 409 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 76 "parser.mly"
                                           (ASTProc(_2,_4,_6))
# 418 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 77 "parser.mly"
                                               (ASTProcRec(_3,_5,_7))
# 427 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "parser.mly"
      ( ASTIntType )
# 433 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 83 "parser.mly"
         ( ASTBoolType )
# 439 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 84 "parser.mly"
                                ( ASTArrowType(_2,_4) )
# 447 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 86 "parser.mly"
         ( ASTVoidType )
# 453 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 88 "parser.mly"
                       ( ASTVecType(_3))
# 460 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 93 "parser.mly"
        (ASTType(_1))
# 467 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast._type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.types) in
    Obj.repr(
# 94 "parser.mly"
                     (ASTTypes(_1,_3))
# 475 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 98 "parser.mly"
                     ( ASTArgFin(_1,_3) )
# 483 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 102 "parser.mly"
      (ASTArg(_1))
# 490 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.args) in
    Obj.repr(
# 103 "parser.mly"
                   ( ASTArgs(_1,_3))
# 498 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    Obj.repr(
# 107 "parser.mly"
      ( ASTTrue )
# 504 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "parser.mly"
         ( ASTFalse )
# 510 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 109 "parser.mly"
       ( ASTNum(_1) )
# 517 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 110 "parser.mly"
         ( ASTId(_1) )
# 524 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.oprim) in
    Obj.repr(
# 111 "parser.mly"
         ( ASTOprim(_1) )
# 531 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 112 "parser.mly"
                               (ASTLambda(_2,_4))
# 539 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprs) in
    Obj.repr(
# 113 "parser.mly"
                         (ASTApply(_2,_3))
# 547 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 114 "parser.mly"
                               (ASTIf(_3,_4,_5))
# 556 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 116 "parser.mly"
                           ( ASTENth(_3,_4) )
# 564 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 117 "parser.mly"
                        (ASTAlloc(_3))
# 571 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 118 "parser.mly"
                      (ASTLen(_3))
# 578 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 122 "parser.mly"
                           ( ASTBinary(Ast.Add, _3, _4) )
# 586 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 123 "parser.mly"
                              ( ASTBinary(Ast.Sub, _3, _4) )
# 594 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 124 "parser.mly"
                              ( ASTBinary(Ast.Mul, _3, _4) )
# 602 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 125 "parser.mly"
                            ( ASTBinary(Ast.Div, _3, _4) )
# 610 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 126 "parser.mly"
                       ( ASTUnary(Ast.Not, _3) )
# 617 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 127 "parser.mly"
                            ( ASTBinary(Ast.And, _3, _4) )
# 625 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 128 "parser.mly"
                           ( ASTBinary(Ast.Or, _3, _4) )
# 633 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 129 "parser.mly"
                           ( ASTBinary(Ast.Eq, _3, _4) )
# 641 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 130 "parser.mly"
                           ( ASTBinary(Ast.Lt, _3, _4) )
# 649 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 134 "parser.mly"
      (ASTExpr(_1))
# 656 "parser.ml"
               : Ast.exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 135 "parser.mly"
              (ASTExprs(_1,_2))
# 664 "parser.ml"
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
