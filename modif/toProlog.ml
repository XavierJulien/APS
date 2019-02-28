open Ast
let rec print_prolog_prog e =
	match e with
	ASTProg(cmds) -> (Printf.printf "prog(cmds(";
					 					print_prolog_cmds cmds;
					 					Printf.printf "))"
									 )

and print_prolog_cmds cmds =
	match cmds with
	 ASTStat(stat) -> (Printf.printf "stat(";
	 				  print_prolog_stat stat;
	 				  Printf.printf ")"
	 				 )
	|ASTDec(dec,cmds) -> (Printf.printf "dec(";
						  print_prolog_dec dec;
						  Printf.printf "),";
						  print_prolog_cmds cmds;
						 )
	|ASTStats(stat,cmds) -> (Printf.printf "stat(";
					         print_prolog_stat stat;
					         Printf.printf "),";
					         print_prolog_cmds cmds;
					        )

and print_prolog_stat stat =
	match stat with
	ASTEcho(e) -> (Printf.printf "echo(";
	               print_prolog_expr e;
	               Printf.printf ")"
	              )

and print_prolog_dec dec =
	match dec with
	|ASTConst(id,t,e) -> (Printf.printf "const(%s," id;
												print_prolog_type t;
												Printf.printf ",";
												print_prolog_expr e;
												Printf.printf ")"
											 )
	|ASTFun(id,t,args,e) -> (Printf.printf "fun(%s," id;
													 print_prolog_type t;
													 Printf.printf ",";
													 Printf.printf "[";
													 print_prolog_args args;
													 Printf.printf "]";
													 Printf.printf ",";
													 print_prolog_expr e;
													 Printf.printf ")";
													)
	|ASTFunRec(id,t,args,e) -> (Printf.printf "funrec(%s," id;
													 print_prolog_type t;
													 Printf.printf ",";
													 Printf.printf "[";
													 print_prolog_args args;
													 Printf.printf "]";
	 												 Printf.printf ",";
													 print_prolog_expr e;
													 Printf.printf ")";
													)

and print_prolog_exprs e =
	match e with
	ASTExpr(e) ->  print_prolog_expr e;
	|ASTExprs(e,exprs) -> (Printf.printf "exprs(";
						   print_prolog_expr e;
						   Printf.printf ",";
						   print_prolog_exprs exprs;
						   Printf.printf ")"
						   )

and print_prolog_expr e =
	match e with
	ASTTrue -> Printf.printf "true"
	|ASTFalse -> Printf.printf "false"
	|ASTNum(n) ->  Printf.printf "num(%d)" n
	|ASTOprim(oprim) -> print_prolog_oprim oprim
	|ASTId(id) -> Printf.printf "id(%s)" id
	|ASTLambda(args,e) -> (Printf.printf "lambda(";
												 Printf.printf "[";
												 print_prolog_args args;
												 Printf.printf "]";
							 				 	 Printf.printf ",";
							 				 	 print_prolog_expr e;
							 				 	 Printf.printf ")"
							 )
	|ASTIf(e1,e2,e3) -> (Printf.printf "if(";
						 print_prolog_expr e1;
						 Printf.printf ",";
						 print_prolog_expr e2;
						 Printf.printf ",";
						 print_prolog_expr e3;
						 Printf.printf ")"
						 )
	|ASTApply(e,exprs) -> (Printf.printf "apply(";
												 print_prolog_expr e;
												 Printf.printf ",";
												 print_prolog_exprs exprs;
												 Printf.printf ")"
												)

and print_prolog_oprim op =
	match op with
	ASTUnary(opun,e) -> (print_prolog_opun opun;
						print_prolog_expr e;
						Printf.printf ")"
						)
	|ASTBinary(opbin,e1,e2) -> (print_prolog_opbin opbin;
								print_prolog_expr e1;
								Printf.printf ",";
								print_prolog_expr e2;
								Printf.printf ")"
								)
	|ASTBinaryBool(opbinbool,e1,e2) -> (print_prolog_opbinbool opbinbool;
								print_prolog_expr e1;
								Printf.printf ",";
								print_prolog_expr e2;
								Printf.printf ")"
								)
and print_prolog_opun o =
	match o with
	Not -> Printf.printf "not("

and print_prolog_opbin o =
	match o with
	Add -> Printf.printf "add("
	|Mul -> Printf.printf "mul("
	|Sub -> Printf.printf "sub("
	|Div -> Printf.printf "div("

and print_prolog_opbinbool o =
	match o with
	And -> Printf.printf "and("
	|Or -> Printf.printf "or("
	|Eq -> Printf.printf "eq("
	|Lt -> Printf.printf "lt(";

and print_prolog_args args =
  match args with
	ASTArg(a) -> print_prolog_arg a
	|ASTArgs(a,args) -> ( print_prolog_arg a;
						  Printf.printf ",";
						  print_prolog_args args
						)

and print_prolog_arg arg =
	match arg with
	ASTArgFin(id,t) -> (Printf.printf "(";
						Printf.printf "%s," id;
						print_prolog_type t;
						Printf.printf ")";
									)

and print_prolog_type t =
	match t with
	ASTIntType -> Printf.printf "int"
	|ASTBoolType -> Printf.printf "bool"
	|ASTArrowType(types,t) -> (Printf.printf "arrow_type(";
								 	 					 print_prolog_types types;
								   			 	   Printf.printf ",";
														 print_prolog_type t;
								   			 	   Printf.printf ")"
									)

and print_prolog_types types =
	match types with
	ASTType(t) -> print_prolog_type t;
	|ASTTypes(t,types) -> (Printf.printf "types(";
								 				 print_prolog_type t;
												 Printf.printf ",";
												 print_prolog_types types;
								 			 	 Printf.printf ")"
												)

let _ =
	try
	let fichier = open_in Sys.argv.(1) in
	let lexbuf = Lexing.from_channel fichier in
	let e = Parser.prog Lexer.token lexbuf in
	print_prolog_prog e;
	print_char '\n'
	with Lexer.Eof -> exit 0
