open Ast;;

type valeur = InN of int
			| InF of expr * string list * (string * valeur) list
			| InFR of string * valeur


(*let env : (string * valeur) list ref = ref []*)

let nu v =
	match v with
	| InN(e) -> e
	| _ -> failwith "pas encore fait aussi" 

let get_string v = 
	match v with 
	| InN(e) -> string_of_int e 
	|_ -> failwith "Pas fait"


let pi_bin op na nb = 
	match op with 
	| "and" -> if na = InN(0) then InN(0) else InN(nb)
	| "or" -> if na = InN(1) then InN(1) else InN(nb) 
	| "eq" ->  if (nu na) = (nu nb) then InN(1) else InN(0)
	| "lt" ->  if nu na < nu nb then InN(1) else InN(0)
	| "add" -> InN(nu na+nu nb)
	| "sub" -> InN(nu na-nu nb)
	| "mul" -> InN(nu na*nu nb)
	| "div" -> InN(nu na/nu nb)
	| _ -> failwith " not a binary operator "		

let pi_un op arg =
	match op with 
	| "not" -> if arg == InN(0) then InN(1) else InN(0)
	| _ -> failwith " not an unary operator "		


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
	|ASTEcho(e) -> let res = eval_expr env e in s:=!s^(get_string res)^"\n"

and eval_dec env ast = 
	match ast with
	|ASTConst(id,t,e) -> let v = eval_expr env e in (id,v)::!env
	|ASTFun(id,t,args,e) -> (id,InF(e,parse_args args,!env))::!env
	|ASTFunRec(id,t,args,e) -> let params = parse_args args in
								 (id,InFR(id,InF(e,params,!env)))::!env


and eval_expr env ast = 
	match ast with
	ASTTrue -> InN(1)
	|ASTFalse -> InN(0)
	|ASTNum(n) -> InN(n)
	|ASTId(id) -> (List.assoc id !env)
	|ASTLambda(args,e) -> InN(10202022)
	|ASTIf(e1,e2,e3) -> if (eval_expr env e1) = InN(1) then (eval_expr env e2) else (eval_expr env e3)
	|ASTApply(e,params) -> InN(29229)
	|ASTOprim(oprim) -> match oprim with 
						|ASTUnary(opun,arg) -> match opun with
												|Not -> pi_un "not" eval_expr env arg
						|ASTBinary(opbin,arg1,arg2) ->  let a1 = (eval_expr env arg1) and a2 = (eval_expr env arg2) in
														match opbin with
														| And -> pi_bin "and" a1 a2
														| Or -> pi_bin "or" a1 a2
														| Eq ->  pi_bin "eq" a1 a2
														| Lt ->  pi_bin "lt" a1 a2
														| Add -> pi_bin "add" a1 a2
														| Sub -> pi_bin "sub" a1 a2
														| Mul -> pi_bin "mul" a1 a2
														| Div -> pi_bin "div" a1 a2

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
