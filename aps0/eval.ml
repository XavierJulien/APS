open Ast;;

type valeur = InN of int
			| InF of expr * string list * (string * valeur) list
			| InFR of string * valeur


(*let env : (string * valeur) list ref = ref []*)

let get_int v =
	match v with
	| InN(e) -> e
	| _ -> failwith "pas encore fait aussi"

let get_string v =
	match v with
	| InN(e) -> string_of_int e
	|_ -> failwith "Pas fait"


let pi_bin op na nb =
	match op with
	| "and" -> if na = 0 then 0 else nb
	| "or" -> if na = 1 then 1 else nb
	| "eq" ->  if na = nb then 1 else 0
	| "lt" ->  if na < nb then 1 else 0
	| "add" -> na+nb
	| "sub" -> na-nb
	| "mul" -> na*nb
	| "div" -> na/nb
	| _ -> failwith " not a binary operator "

let pi_un op arg =
	match op with
	| "not" -> if arg = 0 then 1 else 0
	| _ -> failwith " not an unary operator "


let rec parse_args args =
	match args with
	|ASTArg(a) -> parse_argfin a
	|ASTArgs(a,args) -> (parse_argfin a)@(parse_args args)
and parse_argfin arg =
		match arg with
		|ASTArgFin(id,t) -> id::[]

let rec eval_args env args =
	match args with
		|ASTExpr(a) ->  (eval_expr env a)::[]
		|ASTExprs(a,abis) -> (eval_expr env a)::(eval_args env abis)

and eval_cmds env s ast =
	match ast with
	|ASTStat(stat) -> eval_stat env s stat
	|ASTDec(dec,cmds) -> let new_env = eval_dec env dec in eval_cmds new_env s cmds
	|ASTStats(stat,cmds) -> eval_stat env s stat; eval_cmds env s cmds

and eval_stat env s ast =
	match ast with
	|ASTEcho(e) -> let res = eval_expr env e in s:=!s^(get_string res)^"\n"

and eval_dec env ast =
	match ast with
	|ASTConst(id,t,e) -> let v = eval_expr env e in (id,v)::env
	|ASTFun(id,t,args,e) -> (id,InF(e,parse_args args,env))::env
	|ASTFunRec(id,t,args,e) -> let params = parse_args args in
								 (id,InFR(id,InF(e,params,env)))::env


and eval_expr env ast =
	match ast with
	ASTTrue -> InN(1)
	|ASTFalse -> InN(0)
	|ASTNum(n) -> InN(n)
	|ASTId(id) -> (List.assoc id env)
	|ASTLambda(args,e) -> InF(e,parse_args args,env)
	|ASTIf(e1,e2,e3) -> if (eval_expr env e1) = InN(1) then (eval_expr env e2) else (eval_expr env e3)
	|ASTApply(e,args) -> let eval_e = eval_expr env e  and args_list = eval_args env args in
												(match eval_e with
													|InF(body,params,env1) -> let closure_env = (List.map2 (fun x y -> (x,y)) params args_list)@env1 in
																												eval_expr closure_env body
													|InFR(f,InF(body,params,env1)) -> let closure_env =
																													(f,List.assoc f env)::(List.map2 (fun x y -> (x,y)) params args_list)@env1 in
													 																eval_expr closure_env body
													|_ -> failwith "erreur : impossible d'appliquer une valeur entière")
	|ASTOprim(oprim) -> match oprim with
											|ASTUnary(opun,arg) ->
													(match opun with
													|Not -> InN(pi_un "not" (get_int (eval_expr env arg)))
													)
											|ASTBinary(opbin,arg1,arg2) ->
																	let a1 = get_int (eval_expr env arg1) and a2 = get_int (eval_expr env arg2) in
																		match opbin with
																		| And -> InN(pi_bin "and" a1 a2)
																		| Or -> InN(pi_bin "or" a1 a2)
																		| Eq ->  InN(pi_bin "eq" a1 a2)
																		| Lt ->  InN(pi_bin "lt" a1 a2)
																		| Add -> InN(pi_bin "add" a1 a2)
																		| Sub -> InN(pi_bin "sub" a1 a2)
																		| Mul -> InN(pi_bin "mul" a1 a2)
																		| Div -> InN(pi_bin "div" a1 a2)

let eval_prog ast =
	match ast with
	|ASTProg(cmds) -> let sortie = ref "Retour :\n"
					  and env = [] in
					  	eval_cmds env sortie cmds; !sortie

let _ =
	let fic = open_in Sys.argv.(1) in
	let lexbuf = Lexing.from_channel fic in
	let ast = Parser.prog Lexer.token lexbuf in
	let result  = eval_prog ast in
	print_string result;
	print_newline();;
