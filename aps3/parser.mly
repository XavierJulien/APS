%{
open Ast
%}
%token <int> NUM
%token <string> IDENT
%token PLUS MINUS TIMES DIV
%token CONST FUN REC ECHO
%token INT BOOL TRUE FALSE
%token NOT AND OR EQ LT IF
%token LBRACKET RBRACKET LPAR RPAR
%token COLON SEMICOLON COMMA STAR ARROW
/*aps1*/
%token VAR PROC SET BIF WHILE CALL VOID
/*aps2*/
%token LEN NTH ALLOC VEC
%start prog             /* the entry point */

%type <Ast.prog> prog
%type <Ast.cmds> cmds
%type <Ast.stat> stat
%type <Ast.dec> dec
%type <Ast._type> _type
%type <Ast.types> types
%type <Ast.arg> arg
%type <Ast.args> args
%type <Ast.expr> expr
%type <Ast.exprs> exprs
%type <Ast.oprim> oprim
/*aps1*/
%type <Ast.block> block
/*aps2*/
%type <Ast.lval> lval
/******/
%%

prog:
	LBRACKET cmds RBRACKET	{ ASTProg($2) }
;

cmds:
	stat {ASTStat($1)}
	| dec SEMICOLON cmds {ASTDec($1,$3)}
	| stat SEMICOLON cmds {ASTStats($1,$3)}
	| ret {ASTCmdReturn($1)}
;

/*aps1*/
block:
	LBRACKET cmds RBRACKET	{ ASTBlock($2) }
;
/******/

/*aps2*/
lval:
	IDENT { ASTLId(ASTId($1))}
	| LPAR NTH lval expr RPAR { ASTLNth($3,$4) }
;
/******/

/*aps3*/
ret:
    RETURN expr {ASTReturn($2)}
;
/******/


stat:
	ECHO expr {ASTEcho($2)}
	/*aps1*/ 	/*aps2 set*/
	| SET lval expr {ASTSet($2,$3)}
	| BIF expr block block {ASTBIf($2,$3,$4)}
	| WHILE expr block {ASTWhile($2,$3)}
	| CALL expr exprs {ASTCall($2,$3)}

	/******/
;

dec:
	CONST IDENT _type expr {ASTConst($2,$3,$4)}
	| FUN IDENT _type LBRACKET args RBRACKET expr  {ASTFun($2,$3,$5,$7)}
	| FUN REC IDENT _type LBRACKET args RBRACKET expr  {ASTFunRec($3,$4,$6,$8)}
	/*aps1*/
	| VAR IDENT _type {ASTVar($2,$3)}
	| PROC IDENT LBRACKET args RBRACKET block {ASTProc($2,$4,$6)}
	| PROC REC IDENT LBRACKET args RBRACKET block {ASTProcRec($3,$5,$7)}
	/******/
;

_type:
	INT  { ASTIntType }
	| BOOL  { ASTBoolType }
	| LPAR types ARROW _type RPAR  { ASTArrowType($2,$4) }
	/*aps1*/
	| VOID  { ASTVoidType }
	/*aps2*/
	| LPAR VEC _type RPAR { ASTVecType($3)}
	/******/
;

types:
	_type  {ASTType($1)}
	| _type STAR types  {ASTTypes($1,$3)}
;

arg:
	IDENT COLON _type   { ASTArgFin($1,$3) }
;

args:
	arg  {ASTArg($1)}
	| arg COMMA args  { ASTArgs($1,$3)}
;

expr:
	TRUE { ASTTrue }
	| FALSE { ASTFalse }
	| NUM { ASTNum($1) }
	| IDENT { ASTId($1) }
	| oprim { ASTOprim($1) }
	| LBRACKET args RBRACKET expr {ASTLambda($2,$4)}
	| LPAR  expr exprs RPAR {ASTApply($2,$3)}
	| LPAR IF expr expr expr RPAR {ASTIf($3,$4,$5)}
	/*aps2*/
	| LPAR NTH expr expr RPAR { ASTENth($3,$4) }
	| LPAR ALLOC expr RPAR {ASTAlloc($3)}
	| LPAR LEN expr RPAR {ASTLen($3)}
;

oprim :
	LPAR PLUS expr expr RPAR  { ASTBinary(Ast.Add, $3, $4) }
	| LPAR MINUS expr expr RPAR  { ASTBinary(Ast.Sub, $3, $4) }
	| LPAR TIMES expr expr RPAR  { ASTBinary(Ast.Mul, $3, $4) }
	| LPAR DIV expr expr RPAR  { ASTBinary(Ast.Div, $3, $4) }
	| LPAR NOT expr RPAR  { ASTUnary(Ast.Not, $3) }
	| LPAR AND expr expr RPAR  { ASTBinary(Ast.And, $3, $4) }
	| LPAR OR expr expr RPAR  { ASTBinary(Ast.Or, $3, $4) }
	| LPAR EQ expr expr RPAR  { ASTBinary(Ast.Eq, $3, $4) }
	| LPAR LT expr expr RPAR  { ASTBinary(Ast.Lt, $3, $4) }
;

exprs:
	expr {ASTExpr($1)}
	| expr exprs {ASTExprs($1,$2)}
;
