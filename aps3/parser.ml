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
  | RETURN

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Ast
# 49 "parser.ml"
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
  297 (* RETURN *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\012\000\013\000\013\000\
\014\000\003\000\003\000\003\000\003\000\003\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\004\000\005\000\005\000\
\005\000\005\000\005\000\006\000\006\000\007\000\008\000\008\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\010\000\010\000\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\001\000\003\000\001\000\005\000\
\002\000\002\000\003\000\004\000\003\000\003\000\004\000\007\000\
\008\000\003\000\006\000\007\000\007\000\008\000\001\000\001\000\
\005\000\001\000\004\000\001\000\003\000\003\000\001\000\003\000\
\001\000\001\000\001\000\001\000\001\000\004\000\004\000\006\000\
\005\000\004\000\004\000\005\000\005\000\005\000\005\000\004\000\
\005\000\005\000\005\000\005\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\055\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\005\000\000\000\000\000\000\000\035\000\036\000\033\000\
\034\000\000\000\000\000\010\000\037\000\000\000\000\000\000\000\
\007\000\000\000\000\000\000\000\000\000\000\000\009\000\001\000\
\000\000\000\000\023\000\024\000\000\000\026\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\018\000\000\000\000\000\000\000\011\000\000\000\
\000\000\013\000\000\000\014\000\004\000\003\000\000\000\000\000\
\000\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\012\000\054\000\000\000\000\000\000\000\000\000\000\000\
\030\000\032\000\038\000\000\000\000\000\000\000\000\000\048\000\
\000\000\000\000\000\000\000\000\000\000\043\000\000\000\042\000\
\039\000\000\000\000\000\000\000\006\000\027\000\029\000\000\000\
\000\000\000\000\044\000\045\000\046\000\047\000\049\000\050\000\
\051\000\052\000\000\000\041\000\019\000\000\000\008\000\025\000\
\000\000\016\000\021\000\000\000\040\000\020\000\017\000\022\000"

let yydgoto = "\002\000\
\004\000\105\000\016\000\017\000\080\000\081\000\051\000\052\000\
\075\000\076\000\029\000\073\000\035\000\018\000"

let yysindex = "\007\000\
\250\254\000\000\143\255\000\000\014\255\010\255\103\255\023\255\
\022\255\007\255\103\255\103\255\103\255\103\255\005\255\017\255\
\019\255\000\000\006\255\006\255\031\255\000\000\000\000\000\000\
\000\000\061\255\142\255\000\000\000\000\006\255\043\255\063\255\
\000\000\028\255\103\255\046\255\046\255\103\255\000\000\000\000\
\143\255\143\255\000\000\000\000\255\254\000\000\103\255\048\255\
\006\255\047\255\044\255\051\255\103\255\103\255\103\255\103\255\
\103\255\103\255\103\255\103\255\103\255\103\255\103\255\103\255\
\103\255\103\255\000\000\061\255\053\255\007\255\000\000\143\255\
\046\255\000\000\103\255\000\000\000\000\000\000\006\255\049\255\
\050\255\000\000\061\255\054\255\006\255\061\255\103\255\103\255\
\103\255\103\255\103\255\052\255\103\255\103\255\103\255\103\255\
\103\255\067\255\103\255\071\255\072\255\056\255\061\255\103\255\
\076\255\000\000\000\000\075\255\006\255\006\255\078\255\061\255\
\000\000\000\000\000\000\082\255\083\255\086\255\088\255\000\000\
\089\255\091\255\095\255\097\255\103\255\000\000\098\255\000\000\
\000\000\046\255\080\255\099\255\000\000\000\000\000\000\104\255\
\169\255\105\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\113\255\000\000\000\000\046\255\000\000\000\000\
\101\255\000\000\000\000\169\255\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\107\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\116\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\012\255\000\000\000\000\000\000\000\000\096\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\018\000\000\000\000\000\239\255\232\255\000\000\214\255\
\249\255\204\255\000\000\220\255\069\000\000\000"

let yytablesize = 192
let yytable = "\028\000\
\074\000\047\000\048\000\036\000\037\000\038\000\039\000\001\000\
\033\000\043\000\044\000\020\000\067\000\101\000\003\000\019\000\
\043\000\044\000\021\000\066\000\015\000\045\000\107\000\031\000\
\030\000\102\000\040\000\071\000\045\000\034\000\032\000\084\000\
\049\000\053\000\046\000\053\000\106\000\053\000\079\000\082\000\
\111\000\046\000\041\000\114\000\042\000\088\000\089\000\090\000\
\091\000\092\000\093\000\094\000\095\000\096\000\097\000\098\000\
\099\000\100\000\077\000\078\000\131\000\108\000\050\000\068\000\
\069\000\070\000\072\000\113\000\083\000\138\000\086\000\085\000\
\087\000\103\000\112\000\120\000\109\000\130\000\110\000\115\000\
\116\000\117\000\118\000\119\000\135\000\121\000\122\000\123\000\
\124\000\125\000\126\000\127\000\136\000\149\000\128\000\129\000\
\132\000\133\000\134\000\137\000\155\000\150\000\050\000\022\000\
\023\000\139\000\140\000\005\000\006\000\141\000\007\000\142\000\
\143\000\158\000\144\000\024\000\025\000\147\000\145\000\160\000\
\146\000\148\000\151\000\026\000\028\000\027\000\156\000\152\000\
\002\000\154\000\008\000\009\000\010\000\011\000\012\000\013\000\
\157\000\031\000\104\000\000\000\000\000\014\000\022\000\023\000\
\053\000\054\000\055\000\056\000\159\000\005\000\006\000\000\000\
\007\000\000\000\024\000\025\000\057\000\058\000\059\000\060\000\
\061\000\062\000\026\000\000\000\027\000\000\000\000\000\000\000\
\000\000\022\000\023\000\000\000\008\000\009\000\010\000\011\000\
\012\000\013\000\063\000\064\000\065\000\024\000\025\000\014\000\
\000\000\000\000\000\000\000\000\000\000\153\000\000\000\027\000"

let yycheck = "\007\000\
\037\000\019\000\020\000\011\000\012\000\013\000\014\000\001\000\
\002\001\011\001\012\001\002\001\030\000\066\000\021\001\002\001\
\011\001\012\001\009\001\027\000\003\000\023\001\075\000\002\001\
\002\001\068\000\022\001\035\000\023\001\023\001\009\001\049\000\
\002\001\022\001\036\001\024\001\073\000\026\001\040\001\047\000\
\083\000\036\001\026\001\086\000\026\001\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\060\000\061\000\062\000\063\000\
\064\000\065\000\041\000\042\000\103\000\079\000\002\001\021\001\
\002\001\038\001\021\001\085\000\021\001\112\000\027\001\025\001\
\022\001\021\001\021\001\024\001\028\001\022\001\029\001\087\000\
\088\000\089\000\090\000\091\000\109\000\093\000\094\000\095\000\
\096\000\097\000\024\001\099\000\110\000\130\000\024\001\024\001\
\104\000\022\001\024\001\022\001\137\000\022\001\002\001\001\001\
\002\001\024\001\024\001\007\001\008\001\024\001\010\001\024\001\
\024\001\150\000\024\001\013\001\014\001\125\000\024\001\156\000\
\024\001\024\001\024\001\021\001\029\001\023\001\022\001\024\001\
\022\001\137\000\030\001\031\001\032\001\033\001\034\001\035\001\
\024\001\022\001\070\000\255\255\255\255\041\001\001\001\002\001\
\003\001\004\001\005\001\006\001\156\000\007\001\008\001\255\255\
\010\001\255\255\013\001\014\001\015\001\016\001\017\001\018\001\
\019\001\020\001\021\001\255\255\023\001\255\255\255\255\255\255\
\255\255\001\001\002\001\255\255\030\001\031\001\032\001\033\001\
\034\001\035\001\037\001\038\001\039\001\013\001\014\001\041\001\
\255\255\255\255\255\255\255\255\255\255\021\001\255\255\023\001"

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
  RETURN\000\
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
# 41 "parser.mly"
                        ( ASTProg(_2) )
# 296 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 45 "parser.mly"
      (ASTStat(_1))
# 303 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 46 "parser.mly"
                      (ASTDec(_1,_3))
# 311 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmds) in
    Obj.repr(
# 47 "parser.mly"
                       (ASTStats(_1,_3))
# 319 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.ret) in
    Obj.repr(
# 48 "parser.mly"
       (ASTCmdReturn(_1))
# 326 "parser.ml"
               : Ast.cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmds) in
    Obj.repr(
# 53 "parser.mly"
                        ( ASTBlock(_2) )
# 333 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 59 "parser.mly"
       ( ASTLId(ASTId(_1)))
# 340 "parser.ml"
               : Ast.lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 60 "parser.mly"
                           ( ASTLNth(_3,_4) )
# 348 "parser.ml"
               : Ast.lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 66 "parser.mly"
                (ASTReturn(_2))
# 355 "parser.ml"
               : Ast.ret))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 72 "parser.mly"
           (ASTEcho(_2))
# 362 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 74 "parser.mly"
                 (ASTSet(_2,_3))
# 370 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 75 "parser.mly"
                        (ASTBIf(_2,_3,_4))
# 379 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 76 "parser.mly"
                    (ASTWhile(_2,_3))
# 387 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 77 "parser.mly"
                   (ASTCall(_2,_3))
# 395 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 83 "parser.mly"
                        (ASTConst(_2,_3,_4))
# 404 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 84 "parser.mly"
                                                (ASTFun(_2,_3,_5,_7))
# 414 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 85 "parser.mly"
                                                    (ASTFunRec(_3,_4,_6,_8))
# 424 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 87 "parser.mly"
                   (ASTVar(_2,_3))
# 432 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 88 "parser.mly"
                                           (ASTProc(_2,_4,_6))
# 441 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 89 "parser.mly"
                                               (ASTProcRec(_3,_5,_7))
# 450 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 91 "parser.mly"
                                                  (ASTFunRet(_2,_3,_5,_7))
# 460 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : Ast._type) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 92 "parser.mly"
                                                     (ASTFunRecRet(_3,_4,_6,_8))
# 470 "parser.ml"
               : Ast.dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 97 "parser.mly"
      ( ASTIntType )
# 476 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 98 "parser.mly"
         ( ASTBoolType )
# 482 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 99 "parser.mly"
                                ( ASTArrowType(_2,_4) )
# 490 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    Obj.repr(
# 101 "parser.mly"
         ( ASTVoidType )
# 496 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast._type) in
    Obj.repr(
# 103 "parser.mly"
                       ( ASTVecType(_3))
# 503 "parser.ml"
               : Ast._type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 108 "parser.mly"
        (ASTType(_1))
# 510 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast._type) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.types) in
    Obj.repr(
# 109 "parser.mly"
                     (ASTTypes(_1,_3))
# 518 "parser.ml"
               : Ast.types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast._type) in
    Obj.repr(
# 113 "parser.mly"
                     ( ASTArgFin(_1,_3) )
# 526 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 117 "parser.mly"
      (ASTArg(_1))
# 533 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.args) in
    Obj.repr(
# 118 "parser.mly"
                   ( ASTArgs(_1,_3))
# 541 "parser.ml"
               : Ast.args))
; (fun __caml_parser_env ->
    Obj.repr(
# 122 "parser.mly"
      ( ASTTrue )
# 547 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 123 "parser.mly"
         ( ASTFalse )
# 553 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 124 "parser.mly"
       ( ASTNum(_1) )
# 560 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 125 "parser.mly"
         ( ASTId(_1) )
# 567 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.oprim) in
    Obj.repr(
# 126 "parser.mly"
         ( ASTOprim(_1) )
# 574 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 127 "parser.mly"
                               (ASTLambda(_2,_4))
# 582 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprs) in
    Obj.repr(
# 128 "parser.mly"
                         (ASTApply(_2,_3))
# 590 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 129 "parser.mly"
                               (ASTIf(_3,_4,_5))
# 599 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 131 "parser.mly"
                           ( ASTENth(_3,_4) )
# 607 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 132 "parser.mly"
                        (ASTAlloc(_3))
# 614 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 133 "parser.mly"
                      (ASTLen(_3))
# 621 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 137 "parser.mly"
                           ( ASTBinary(Ast.Add, _3, _4) )
# 629 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 138 "parser.mly"
                              ( ASTBinary(Ast.Sub, _3, _4) )
# 637 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 139 "parser.mly"
                              ( ASTBinary(Ast.Mul, _3, _4) )
# 645 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 140 "parser.mly"
                            ( ASTBinary(Ast.Div, _3, _4) )
# 653 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 141 "parser.mly"
                       ( ASTUnary(Ast.Not, _3) )
# 660 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 142 "parser.mly"
                            ( ASTBinary(Ast.And, _3, _4) )
# 668 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 143 "parser.mly"
                           ( ASTBinary(Ast.Or, _3, _4) )
# 676 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 144 "parser.mly"
                           ( ASTBinary(Ast.Eq, _3, _4) )
# 684 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 145 "parser.mly"
                           ( ASTBinary(Ast.Lt, _3, _4) )
# 692 "parser.ml"
               : Ast.oprim))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 149 "parser.mly"
      (ASTExpr(_1))
# 699 "parser.ml"
               : Ast.exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprs) in
    Obj.repr(
# 150 "parser.mly"
              (ASTExprs(_1,_2))
# 707 "parser.ml"
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
