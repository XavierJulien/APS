type opun = Not
and opbin = Add | Mul | Sub | Div | And | Or | Eq | Lt
and _type =
	ASTIntType
	| ASTBoolType
	| ASTArrowType of types  * _type
	(*aps1*)
	| ASTVoidType
	(*aps2*)
	| ASTVecType of _type

and types =
	ASTType of _type
	| ASTTypes of _type * types

and arg =
	ASTArgFin of string * _type

and args =
	ASTArg of arg
	| ASTArgs of arg * args

and oprim =
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
	(*aps2*)
	| ASTENth of expr * expr
	| ASTLen of expr
	| ASTAlloc of expr

and exprs =
	ASTExpr of expr
	| ASTExprs of expr * exprs

and stat =
	ASTEcho of expr
	(*aps1*) (*aps2 pour set*)
	| ASTSet of lval * expr
	| ASTBIf of expr * block * block
	| ASTWhile of expr * block
	| ASTCall of expr * exprs


and dec =
	ASTConst of string * _type * expr
	| ASTFun of string * _type * args * expr
	| ASTFunRec of string * _type * args * expr
	(*aps1*)
	| ASTVar of string * _type
	| ASTProc of string * args * block
	| ASTProcRec of string * args * block
	(*aps3*)
	| ASTFunRet of string * _type * args * block
	| ASTFunRecRet of string * _type * args * block

and cmds =
	ASTStat of stat
	| ASTDec of dec * cmds
	| ASTStats of stat * cmds
	(*aps3*)
	| ASTCmdReturn of ret

(*aps3*)
and ret =
    ASTReturn of expr

(*aps2*)
and lval =
	ASTLId of expr
	| ASTLNth of lval * expr

(*aps1*)
and block =
	ASTBlock of cmds

and prog =
	ASTProg of cmds
