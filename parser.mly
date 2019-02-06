%{
open Ast
%}
%token <int> NUM
%token <string> IDENT
%token PLUS MINUS TIMES DIV 
%token CONST FUN REC ECHO 
%token INT BOOL TRUE FALSE 
%token NOT AND OR EQ LT
%token LBRACKET RBRACKET LPAR RPAR 
%token COLON SEMICOLON COMMA STAR ARROW
%token EOL
%start prog             /* the entry point */
%type <Ast.prog> prog
%type <Ast.cmds> cmds
%type <Ast.stat> stat
%type <Ast.dec> dec
%type <Ast.type> type
%type <Ast.types> types
%type <Ast.arg> arg
%type <Ast.args> args
%type <Ast.expr> expr
%type <Ast.exprs> exprs
%type <Ast.oprim> oprim
%%

prog:
	LBRACKET cmds RBRACKET	{ ASTProg($2) }
;

cmds:
	stat {ASTStat($1)}
	| dec SEMICOLON cmds {ASTDec($1) $3}
	| stat SEMICOLON cmds {ASTStat($1) $3}
;

stat:
	ECHO expr {ASTEcho($2)}
;

dec:
	CONST IDENT _type expr {ASTConst(ASTId($2) $3 $4)}
	| FUN IDENT _type LBRACKET args RBRACKET expr  {ASTFun(ASTId($2),$3,$5,$7)}
	| FUN REC IDENT _type LBRACKET args RBRACKET expr  {ASTFunRec(ASTId($3),$4,$6,$8)}
;

_type:
	INT  { ASTIntType } 
	| BOOL  { ASTBoolType }
	| LPAR types ARROW _type RPAR  { ASTArrowType($2,$4) }
;

types:
	_type  {$1::[]}
	| _type STAR types  {$1::$3::[]}
;

arg:
	IDENT COLON _type   { ASTArg(ASTId($1),$3) }
;

args: 
	arg  {$1}
	| arg COMMA args  { ASTArgs($1,$3)}
;

expr:
	TRUE { ASTTrue }
	| FALSE { ASTFalse }
	| NUM { ASTNum($1) }
	| IDENT { ASTId($1) }
	| oprim { $1 }
	| LBRACKET args RBRACKET expr {$2 $4}
	| LPAR  expr exprs RPAR {$2 $3}
	| LPAR IF expr expr expr {ASTIf($1,$2,$3)}
;

oprim :
	PLUS  { ASTOpBin(Ast.Add, }
	| LPAR PLUS expr expr RPAR  { ASTBinary(Ast.Sub, $3, $4) }
	| LPAR MINUS expr expr RPAR  { ASTBinary(Ast.Sub, $3, $4) }
	| LPAR TIMES expr expr RPAR  { ASTBinary(Ast.Mul, $3, $4) }
	| LPAR DIV expr expr RPAR  { ASTBinary(Ast.Div, $3, $4) }
	| LPAR NOT expr RPAR  { ASTUnary(Ast.Sub, $3) }
	| LPAR AND expr expr RPAR  { ASTBinary(Ast.Mul, $3, $4) }
	| LPAR OR expr expr RPAR  { ASTBinary(Ast.Sub, $3, $4) }
	| LPAR EQ expr expr RPAR  { ASTBinary(Ast.Mul, $3, $4) }
	| LPAR LT expr expr RPAR  { ASTBinary(Ast.Sub, $3, $4) }

;

exprs:
	expr {$1}
	| expr exprs {$1 $2}
;
