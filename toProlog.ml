open Ast
let rec print_prolog_prog e =
	match e with
	ASTProg(cmds) -> (Printf.printf "cmds(";
					 print_prolog_cmds cmds;
					 Printf.printf ")"
					)

let rec print_prolog_cmds cmds = 
	match cmds with
	 ASTStat(stat) -> (Printf.printf "stat(";
	 				  print_prolog_stat stat;
	 				  Printf.printf ")"
	 				 )
	|ASTDec(dec,cmds) -> (Printf.printf "dec(";
						  print_prolog_dec dec;
						  Printf.printf ",";
						  print_prolog_cmds cmds;
						  Printf.printf ")"
						 )
	|ASTStats(stat,cmds) -> (Printf.printf "stats(";
					         print_prolog_stat stat;
					         Printf.printf ",";
					         print_prolog_cmds cmds;
					         Printf.printf ")"
					        )

let rec print_prolog_stat stat = 
	match stat with 
	ASTEcho(e) -> (Printf.printf "echo(";
	              print_prolog e;
	              Printf.printf ")"
	             )

let rec print_prolog_dec dec = 
	match dec with 
	|ASTConst(id,t,e) -> (Printf.printf "const(%s" id;print_prolog t;print_prolog e;Printf.print")")
	|ASTFun(id,t,args,e)
	|ASTFunRec(id,t,args,e)

let rec print_prolog_exprs e =
	match e with 
	ASTExpr(e) -> (Printf.printf "expr(";
				   print_prolog_expr e;
				   Printf.printf ")"
				   )
	|ASTExprs(e,exprs) -> (Printf.printf "exprs(";
						   print_prolog_expr e;
						   Printf.printf ",";
						   print_prolog_exprs exprs;
						   Printf.printf ")"
						   )

let rec print_prolog_expr e =
	match e with
	ASTTrue -> Printf.printf "true"
	|ASTFalse -> Printf.printf "false"
	|ASTNum(n) ->  Printf.printf "%d" n
	|ASTOprim(oprim) -> print_prolog_oprim oprim
	|ASTId(id) -> Printf.printf "%s" id 
	|ASTLambda(args,e) -> (Printf.printf "lambda(";
						   print_prolog_args args;
						   Printf.printf ",";
						   print_prolog_expr e;
						   Printf.printf ")";
						   )
	|ASTIf(e1,e2,e3) -> (Printf.printf "if(";
						 print_prolog_expr e1;
						 Printf.printf ",";
						 print_prolog_expr e2;
						 Printf.printf ",";
						 print_prolog_expr e3;
						 Printf.printf ")";
						 )
	|ASTApply(e,exprs) -> (Print

let rec print_prolog_oprim op =
	match op with 
	ASTUnary(opun,e) -> (Printf.printf "opun(";
						print_prolog_opun opun;
						Printf.printf ",";
						print_prolog_expr e;
						Printf.printf ")"
						)
	|ASTBinary(opbin,e1,e2) -> (Printf.printf "opbin(";
								print_prolog_opbin opbin;
								Printf.printf ",";
								print_prolog_expr e1;
								Printf.printf ",";
								print_prolog_expr e2;
								Printf.printf ")"
								)
	
let rec print_prolog_opun o =
	match o with 
	Not -> Printf.printf "not"
	
let rec print_prolog_opbin o =
	match o with 
	Add -> Printf.printf "add"
	|Mul -> Printf.printf "mul"
	|Sub -> Printf.printf "sub"
	|Div -> Printf.printf "div"
	|And -> Printf.printf "and"
	|Or -> Printf.printf "or"
	|Eq -> Printf.printf "eq"
	|Lt -> Printf.printf "lt"
	
	
let rec print_prolog_args args =
	match args with
	ASTArg(a) ->
	|ASTArgs(a,args) -> 


let rec print_prolog_arg a
	match a with 
	ASTArg(id,t) -> 
	

let rec print_prolog_types types =
	match types with 
	ASTType(t) ->
	|ASTTypes(t,types) -> 

let rec print_prolog_type t =
	match t with 
	ASTIntType -> 
	|ASTBoolType ->
	|ASTArrowType ->
	
	
	
	
ASTPrim(op, e1, e2) -> (
Printf.printf"%s" (string_of_op op);
Printf.printf"(";
print_prolog e1;
Printf.printf",";
print_prolog e2;
Printf.printf")"
)


let _ =
	try
	let lexbuf = Lexing.from_channel stdin in
	let e = Parser.prog Lexer.token lexbuf in
	print_prolog_prog e;
	print_char '\n'
	with Lexer.Eof -> exit 0
