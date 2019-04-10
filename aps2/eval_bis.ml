open Ast;;

(*: (string * valeur) list *)

type valeur = InN of int
			| InF of expr * string list * (string * valeur) list
			| InFR of string * valeur
			| InA of int
			| InP of block * string list * (string * valeur) list
			| InPR of string * valeur
			| InB of valeur * int

(* check *)
let cpt = ref 0

let alloc mem =
	let res = (!cpt,(!cpt,ref(InN(-1)))::mem) in
		cpt:=(!cpt+1);
		res
		
(* check *)
let get_int v =
	match v with
	| InN(e) -> e
	| _ -> failwith "pas encore fait aussi"

(* check *)
let get_string v =
	match v with
	| InN(e) -> string_of_int e
	|_ -> failwith "Pas fait"

(* check *)
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

(* check *)
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

(* check *)
let rec eval_args env mem args =
	match args with
		|ASTExpr(a) ->  (eval_expr env mem a)::[]
		|ASTExprs(a,abis) -> (eval_expr env mem a)::(eval_args env mem abis)

(* check *)
and eval_cmds env mem s ast =
	match ast with
	|ASTDec(dec,cmds) -> let (new_env,new_mem) = eval_dec env mem dec in eval_cmds new_env new_mem s cmds
	|ASTStat(stat) -> eval_stat env mem s stat
	|ASTStats(stat,cmds) -> let (new_mem,new_s) = eval_stat env mem s stat in eval_cmds env new_mem new_s cmds

(* check *)
and eval_block env mem s ast =
	match ast with
	|ASTBlock(cmds) -> eval_cmds env mem s cmds

(*and eval_lval env mem ast =
	match ast with 
	|ASTLId(expr_id) -> eval_expr env mem expr_id*)

and eval_stat env mem s ast =
	match ast with
	|ASTEcho(e) ->let res = eval_expr env mem e in s:=!s^(get_string res)^"\n";(mem,s)
	(*|ASTSet(id,e) -> let id_lval = eval_lval env mem  in
						(match List.assoc id env with
										InA(a)-> let v = (List.assoc a mem)
														 and affect = eval_expr env mem e in
														 	 v:= affect;
															 (mem,s)
										|_ -> failwith "Error SET : not a InA")*)
	 |ASTBIf(e,b1,b2) -> if (eval_expr env mem e) = InN(1) then (eval_block env mem s b1) else (eval_block env mem s b2)
	 |ASTWhile(e,b) ->
			if (eval_expr env mem e) = InN(0)
			then (mem,s)
			else let (new_mem,new_s) = (eval_block env mem s b) in
				eval_stat env new_mem new_s ast
	|ASTCall(p,args) -> let eval_p = eval_expr env mem p
											and args_list = eval_args env mem args in
												(match eval_p with
													|InP(block,params,env1) ->
														 let closure_env = (List.map2 (fun x y -> (x,y)) params args_list)@env1 in
															eval_block closure_env mem s block
													|InPR(p,InP(block,params,env1)) ->
														 let closure_env = (p,List.assoc p env)::(List.map2 (fun x y -> (x,y)) params args_list)@env1 in
													 		eval_block closure_env mem s block
													|_ -> failwith "erreur : impossible d'appliquer une valeur entière")

(* check *)
and eval_dec env mem ast =
	match ast with
	|ASTConst(id,t,e) -> let v = eval_expr env mem e in  ((id,v)::env,mem)
	|ASTFun(id,t,args,e) -> ((id,InF(e,parse_args args,env))::env,mem)
	|ASTFunRec(id,t,args,e) -> let params = parse_args args in
								 ((id,InFR(id,InF(e,params,env)))::env,mem)
	(*aps1*)
	|ASTVar(id,t) -> let (a,new_mem) = alloc(mem) in ((id,InA(a))::env,new_mem)
	|ASTProc(id,args,b) -> ((id,InP(b,parse_args args,env))::env,mem)
	|ASTProcRec(id,args,b) -> ((id,InPR(id,InP(b,parse_args args,env)))::env,mem)



and eval_expr env mem ast =
	match ast with
	ASTTrue -> InN(1)
	|ASTFalse -> InN(0)
	|ASTNum(n) -> InN(n)
	|ASTId(id) -> (match (List.assoc id env) with
				  |InA(a) -> !(List.assoc a mem)
				  |v -> v)
	|ASTLambda(args,e) -> InF(e,parse_args args,env)
	|ASTIf(e1,e2,e3) -> if (eval_expr env mem e1) = InN(1) then (eval_expr env mem e2) else (eval_expr env mem e3)
	|ASTApply(e,args) -> let eval_e = eval_expr env mem e  and args_list = eval_args env mem args in
												(match eval_e with
													|InF(body,params,env1) -> let closure_env = (List.map2 (fun x y -> (x,y)) params args_list)@env1 in
																												eval_expr closure_env mem body
													|InFR(f,InF(body,params,env1)) -> let closure_env =
																								(f,List.assoc f env)::(List.map2 (fun x y -> (x,y)) params args_list)@env1 in
													 															eval_expr closure_env mem body
													|_ -> failwith "erreur : impossible d'appliquer une valeur entière")
	|ASTOprim(oprim) ->
				(match oprim with
						|ASTUnary(opun,arg) ->
								(match opun with
								|Not -> InN(pi_un "not" (get_int (eval_expr env mem arg)))
								)
						|ASTBinary(opbin,arg1,arg2) ->
												let a1 = get_int (eval_expr env mem arg1) and a2 = get_int (eval_expr env mem arg2) in
													match opbin with
													| And -> InN(pi_bin "and" a1 a2)
													| Or -> InN(pi_bin "or" a1 a2)
													| Eq ->  InN(pi_bin "eq" a1 a2)
													| Lt ->  InN(pi_bin "lt" a1 a2)
													| Add -> InN(pi_bin "add" a1 a2)
													| Sub -> InN(pi_bin "sub" a1 a2)
													| Mul -> InN(pi_bin "mul" a1 a2)
													| Div -> InN(pi_bin "div" a1 a2))

(* check *)
let eval_prog ast =
	match ast with
	|ASTProg(cmds) -> let sortie = ref "Retour :\n"
					  			  and env = []
										and mem = [] in
					  				let (memory,sortie) = eval_cmds env mem sortie cmds in !sortie

let _ =
	let fic = open_in Sys.argv.(1) in
	let lexbuf = Lexing.from_channel fic in
	let ast = Parser.prog Lexer.token lexbuf in
	let sortie  = eval_prog ast in
	print_string sortie;
	print_newline();;
