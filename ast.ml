type opun = Not 
type opbin = Add | Mul | Sub | Div | And | Or | Eq | Lt 

type prog = 
	ASTProg of cmds list
type cmds = 
	ASTStat of stat
	| ASTDec of dec * cmds list
	| ASTStat of stat * cmds list 
type stat =
	ASTEcho of expr
type dec = 
	ASTConst of ASTId * _type * expr 
type _type = 
	ASTIntType 
	| ASTBoolType 
	| ASTArrowType of _type list * _type 
type types = 
	_type list
type arg = 
	ASTArg of ASTId * _type
type args = 
	arg 
	| ASTArgs of arg * args
type expr = 
	| ASTTrue
	| ASTFalse
	| ASTNum of int
	| ASTId of string
	| ASTUnary of opun * expr
	| ASTBinaryBin of opbin * expr * expr
	| args
	
type




let string_of_op op =
match op with
Add -> "add"
| Mul -> "mul"
| Sub -> "sub"
| Div -> "div"

let op_of_string op =
match op with
"add" -> Add
| "mul" -> Mul
| "sub" -> Sub
| "div" -> Div


