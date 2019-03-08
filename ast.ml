type opun = Not
type opbin = Add | Mul | Sub | Div | And | Or | Eq | Lt
type _type =
	ASTIntType
	| ASTBoolType
	| ASTArrowType of types  * _type

and types =
	ASTType of _type
	| ASTTypes of _type * types

type arg =
	ASTArgFin of string * _type

type args =
	ASTArg of arg
	| ASTArgs of arg * args

type oprim =
	ASTUnary of opun * expr
	| ASTBinary of opbin * expr * expr

and expr =
	ASTTrue
	| ASTFalse
	| ASTNum of int
	| ASTOprim of oprim
	| ASTId of string
	| ASTLambda of args * expr
	| ASTIf of expr * expr * expr
	| ASTApply of expr * exprs

and exprs =
	ASTExpr of expr
	| ASTExprs of expr * exprs

type stat =
	ASTEcho of expr

type dec =
	ASTConst of string * _type * expr
	| ASTFun of string * _type * args * expr
	| ASTFunRec of string * _type * args * expr

type cmds =
	ASTStat of stat
	| ASTDec of dec * cmds
	| ASTStats of stat * cmds

type prog =
	ASTProg of cmds
