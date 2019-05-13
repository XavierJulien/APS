open Ast
let rec print_prolog_cmds cmds =
	match cmds with
	 ASTStat(stat) -> (Printf.printf "stat(";
	 				  print_prolog_stat stat;
	 				  Printf.printf ")";
	 				  Printf.printf ",epsilon"
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
	(*aps3*)
	|ASTCmdReturn(ret) -> (Printf.printf "return(";
						   print_prolog_ret ret;
						   Printf.printf ")";
						   Printf.printf ",epsilon"
						  )
						   
(*aps1*)
and print_prolog_block block =
	match block with
	ASTBlock(cmds) -> (Printf.printf "block([";
					   print_prolog_cmds cmds;
					   Printf.printf "])"
					  )

and print_prolog_lval lval =
 	match lval with
 	ASTLId(id) -> print_prolog_expr id
 	|ASTLNth(lval,e)->  (Printf.printf "nth(";
                         print_prolog_lval lval;
                         Printf.printf ",";
                         print_prolog_expr e;
                         Printf.printf ")"
                        )

and print_prolog_stat stat =
	match stat with
	ASTEcho(e) -> (Printf.printf "echo(";
	               print_prolog_expr e;
	               Printf.printf ")"
	              )
	(*aps1*) 
	|ASTSet(id,e)-> (Printf.printf "set(";
					 print_prolog_lval id;
					 Printf.printf ",";
					 print_prolog_expr e;
					 Printf.printf ")"
					)
	|ASTBIf(e,b1,b2) ->(Printf.printf "bif(";
						 print_prolog_expr e;
						 Printf.printf ",";
						 print_prolog_block b1;
						 Printf.printf ",";
						 print_prolog_block b2;
						 Printf.printf ")"
						)
	|ASTWhile(e,b) -> (Printf.printf "while(";
						 print_prolog_expr e;
						 Printf.printf ",";
						 print_prolog_block b;
						 Printf.printf ")"
					  )
	|ASTCall(id,params) -> (Printf.printf "call(";
						    print_prolog_expr id;
						    Printf.printf ",[";
							print_prolog_params params;
							Printf.printf "])"
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
	(*aps1*)
	|ASTVar(id,t) -> (Printf.printf "var(%s," id;
					  print_prolog_type t;
					  Printf.printf ")"
				     )
	|ASTProc(id,args,b) -> (Printf.printf "proc(%s," id;
							Printf.printf "[";
							print_prolog_args args;
							Printf.printf "]";
							Printf.printf ",";
							print_prolog_block b;
							Printf.printf ")";
						   )
	|ASTProcRec(id,args,b) -> (Printf.printf "procrec(%s," id;
													 Printf.printf "[";
													 print_prolog_args args;
													 Printf.printf "]";
	 												 Printf.printf ",";
													 print_prolog_block b;
													 Printf.printf ")";
													)
	(*aps3*)
	|ASTFunRet(id,t,args,b) -> (Printf.printf "funret(%s," id;
													 print_prolog_type t;
													 Printf.printf ",";
													 Printf.printf "[";
													 print_prolog_args args;
													 Printf.printf "]";
													 Printf.printf ",";
													 print_prolog_block b;
													 Printf.printf ")";
													)
	|ASTFunRecRet(id,t,args,b) -> (Printf.printf "funrecret(%s," id;
													 print_prolog_type t;
													 Printf.printf ",";
													 Printf.printf "[";
													 print_prolog_args args;
													 Printf.printf "]";
	 												 Printf.printf ",";
													 print_prolog_block b;
													 Printf.printf ")";
													)
(*aps3*)
and print_prolog_ret r = 
	match r with 
	ASTReturn(e) ->  print_prolog_expr e;
	
and print_prolog_exprs e =
	match e with
	ASTExpr(e) ->  print_prolog_expr e;
	|ASTExprs(e,exprs) -> (Printf.printf "exprs(";
						   print_prolog_expr e;
						   Printf.printf ",";
						   print_prolog_exprs exprs;
						   Printf.printf ")"
						   )

and print_prolog_params params =
	match params with
		ASTExpr(e) ->  print_prolog_expr e;
		|ASTExprs(e,params) -> (print_prolog_expr e;
							   Printf.printf ",";
							   print_prolog_params params;
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
	|ASTApply(e,params) -> (Printf.printf "apply(";
												 print_prolog_expr e;
												 Printf.printf ",[";
												 print_prolog_params params;
												 Printf.printf "])"
												)
	(*aps2*)
	|ASTLen(expr) -> (Printf.printf "len(";
												 print_prolog_expr expr;
												 Printf.printf ")"
												)
	|ASTAlloc(expr) -> (Printf.printf "alloc(";
												 print_prolog_expr expr;
												 Printf.printf ")"
												)
	|ASTENth(e1,e2)->  (Printf.printf "nth(";
												 print_prolog_expr e1;
												 Printf.printf ",";
												 print_prolog_expr e2;
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

and print_prolog_opun o =
	match o with
	Not -> Printf.printf "not("

and print_prolog_opbin o =
	match o with
	Add -> Printf.printf "add("
	|Mul -> Printf.printf "mul("
	|Sub -> Printf.printf "sub("
	|Div -> Printf.printf "div("
	|And -> Printf.printf "and("
	|Or -> Printf.printf "or("
	|Eq -> Printf.printf "eq("
	|Lt -> Printf.printf "lt("

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
						Printf.printf ")"
					)

and print_prolog_type t =
	match t with
	ASTIntType -> Printf.printf "int"
	|ASTBoolType -> Printf.printf "bool"
	(*aps1*)
	|ASTVoidType -> Printf.printf "void"
	|ASTArrowType(types,t) -> (Printf.printf "arrow([";
							   print_prolog_types types;
							   Printf.printf "],";
							   print_prolog_type t;
							   Printf.printf ")"
									)
	(*aps2*)
	|ASTVecType(t) -> (Printf.printf "vec(";
							   		print_prolog_type t;
							   		Printf.printf ")"
										)

and print_prolog_types types =
	match types with
	ASTType(t) -> print_prolog_type t;
	|ASTTypes(t,types) -> (print_prolog_type t;
							Printf.printf ",";
							print_prolog_types types;
						  )

let print_prolog_prog e =
	match e with
	ASTProg(cmds) -> (Printf.printf "prog([";
					 					print_prolog_cmds cmds;
					 					Printf.printf "])."
									 )

let _ =
	try
	let fichier = open_in Sys.argv.(1) in
	let lexbuf = Lexing.from_channel fichier in
	let e = Parser.prog Lexer.token lexbuf in
	print_prolog_prog e;
	print_char '\n'
	with Lexer.Eof -> exit 0
