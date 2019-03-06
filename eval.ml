open Ast;;

type valeur = InN of int
			| InF of expr * string list * (string * valeur) list
			| InFR of string * valeur


(*let env : (string * valeur) list ref = ref []*)

let pi_bin op (na,nb) = 
	match op with 
	| "and" -> if na = 0 then 0 else nb
	| "or" -> if na = 1 then 1 else nb 
	| "eq" ->  if na = nb then 1 else 0
	| "lt" ->  if na < nb then 1 else 0
	| "add" -> na+nb
	| "sub" -> na-nb
	| "mul" -> na*nb
	| "div" -> na/nb
	| _ -> failwith " not a  binary operator "		

let pi_un op arg =
	match op with 
	| "not" -> if arg == 0 then 1 else 0
	| _ -> failwith " not an unary operator "		

let nu v =
	match v with
	| InN(e) -> string_of_int e
	| _ -> failwith "pas encore fait aussi" 

let rec parse_args args = 
	match args with 
	|ASTArg(a) -> parse_argfin a
	|ASTArgs(a,args) -> (parse_argfin a)@(parse_args args)
and parse_argfin arg = 
		match arg with 
		|ASTArgFin(id,t) -> id::[]

	
let rec eval_cmds env s ast = 
	match ast with
	|ASTStat(stat) -> eval_stat env s stat
	|ASTDec(dec,cmds) -> eval_dec env dec; eval_cmds env s cmds
	|ASTStats(stat,cmds) -> eval_stat env s stat; eval_cmds env s cmds
	
and eval_stat env s ast = 
	match ast with 
	|ASTEcho(e) -> let res = eval_expr env e in s:=!s^(nu res)^"\n"

and eval_dec env ast = 
	match ast with
	|ASTConst(id,t,e) -> let v = eval_expr env e in (id,v)::!env
	|ASTFun(id,t,args,e) -> (id,InF(e,parse_args args,!env))::!env
	|ASTFunRec(id,t,args,e) -> let params = parse_args args in
								 (id,InFR(id,InF(e,params,!env)))::!env


and eval_expr env ast = 
	match ast with
	ASTTrue -> 
	|ASTFalse -> 
	|ASTNum(n) -> 
	|ASTOprim(oprim) ->
	|ASTId(id) ->
	|ASTLambda(args,e) -> 
	|ASTIf(e1,e2,e3) -> 
	|ASTApply(e,params) -> 

let eval_prog ast = 
	match ast with 
	|ASTProg(cmds) -> let sortie = ref "Retour :\n" 
					  and env : (string * valeur) list ref = ref [] in 
					  	eval_cmds env sortie cmds; !sortie

let _ = 
	let fic = open_in Sys.argv.(1) in
	let lexbuf = Lexing.from_channel fic in 
	let ast = Parser.prog Lexer.token lexbuf in 
	let result  = eval_prog ast in 
	print_string result;
	print_newline();;
