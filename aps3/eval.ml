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
	let res = (!cpt,(!cpt,ref (InN(-1)))::mem) in
		cpt:=(!cpt+1);
		res

let allocn mem n =
	let capture_cpt = !cpt in
		let rec aux memory n =
			if n>0 then
				let new_mem = (!cpt,ref (InN(-1)))::memory in
				cpt:= !cpt+1;
				aux new_mem (n-1)
			else
			 	(capture_cpt,memory)
			in
	(aux mem n)


(* check *)
let rec get_int v =
	match v with
	| InN(e) -> e
	| InA(a) -> a
	| InB(a,t) -> get_int a
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


(*retourne une val*sigpp list *)
let rec eval_args env mem args =
	match args with
		|ASTExpr(a) ->  (eval_expr env mem a)::[]
		|ASTExprs(a,abis) -> let (v,sigp) = (eval_expr env mem a) in (v,sigp)::(eval_args env sigp abis)


and eval_cmds env mem s ast =
	match ast with
	|ASTDec(dec,cmds) -> let (new_env,new_mem) = eval_dec env mem dec in eval_cmds new_env new_mem s cmds
	|ASTStat(stat) -> eval_stat env mem s stat
	|ASTStats(stat,cmds) -> let (new_mem,new_s) = eval_stat env mem s stat in eval_cmds env new_mem new_s cmds


and eval_block env mem s ast =
	match ast with
	|ASTBlock(cmds) -> eval_cmds env mem s cmds

and eval_stat env mem s ast =
	match ast with
	|ASTEcho(e) ->let (eval_e,sigp) = eval_expr env mem e in 
					s:=!s^(get_string eval_e)^"\n";
					(sigp,s)
	|ASTSet(lval_id,e) -> let (inbloc,sigp) = eval_expr env mem e in
							let (adr,sigpp) = eval_lval env sigp lval_id in
								let value = List.assoc (get_int adr) sigpp in
								Printf.printf "l adresse est %d \n" (get_int adr);
								    (match !value with
                                    |InB(a,b) -> Printf.printf "avant le set la valeur est un bloc de adr debut = %d\n" (get_int !value)
                                    |InN(a) -> Printf.printf "avant le set la valeur est un int =  %d\n" (get_int !value);
                                    |_ -> print_endline "ni bloc ni inn");
									value:=inbloc;
									(match !value with
									|InB(a,b) -> Printf.printf "apres le set la valeur est un bloc de adr debut = %d\n" (get_int !value)
									|InN(a) -> Printf.printf "apres le set la valeur est un int =  %d\n" (get_int !value);
									|_ -> print_endline "ni bloc ni inn";
									print_newline ());
									(sigpp,s)
	|ASTBIf(e,b1,b2) -> let (eval_e,sigp) = (eval_expr env mem e) in 
							if eval_e = InN(1) 
							then (eval_block env sigp s b1)	
							else (eval_block env sigp s b2) 
	|ASTWhile(e,b) ->
			let (eval_e,sigp) = (eval_expr env mem e) in 
			if eval_e = InN(0)
			then (sigp,s)
			else let (sigpp,new_s) = (eval_block env sigp s b) in
				eval_stat env sigpp new_s ast
	|ASTCall(p,args) -> let (eval_p,sigp) = eval_expr env mem p in 
						let args_sig_list = eval_args env sigp args in
						let (valargs_list,sig_list) = List.split args_sig_list in 
						let last_sig = List.nth sig_list ((List.length sig_list)-1) in
												(match eval_p with
													|InP(block,params,env1) ->
														 let closure_env = (List.map2 (fun x y -> (x,y)) params valargs_list)@env1 in
															eval_block closure_env last_sig s block
													|InPR(p,InP(block,params,env1)) ->
														 let closure_env = (p,List.assoc p env)::(List.map2 (fun x y -> (x,y)) params valargs_list)@env1 in
													 		eval_block closure_env last_sig s block
													|_ -> failwith "erreur : impossible d'appliquer une valeur entière")
													
													
(*aps2*)
and eval_lval env mem ast =
	match ast with 
	ASTLId(aid) -> (match aid with
					|ASTId(id) ->  
						(match (List.assoc id env) with
					  	  |InA(a) -> (InA(a),mem)
				  	  	  |InB(a,size) -> (InB(a,size),mem)
				  	  	  |_ -> failwith "id n'est pas une adresse ou un bloc")
					|_ -> failwith "dans eval_lval erreur impossible")
	
	(*|ASTLId(a) -> print_endline "dans ASTLId avant d'appeler eval expr";
	                let (inb,new_mem) = eval_expr env mem a in
					(match inb with 
					|InB(b,n) -> print_string "salut";((get_int b),new_mem)
					|InA(a) -> print_endline "est un inA";(2,new_mem)
					|InN(n) -> print_endline "inN dans eval_lval";(0,new_mem)
					|_ -> (1,new_mem)) *)
	|ASTLNth(lval, expr) -> let (retour_eval_lval,sigm) = eval_lval env mem lval in
                            	let (index,sigprim) = eval_expr env sigm expr in
                                    match retour_eval_lval,index with
                                       |InB(a,n),InN(i) -> (InA((get_int a)+i),sigprim)
                                       |InA(a),InN(i) -> (match !(List.assoc a sigprim) with
                                                           		|InB(adre,size) -> (InA((get_int adre)+i),sigprim)
                                                           		|_ -> failwith "ASTLNth cas matching impossible")
                                       |_ -> failwith "ASTLNth cas matching impossible extérieur"



	                          (* let (adr_debut,sigm) = eval_lval env mem lval in
								let (index,sigprim) = eval_expr env sigm expr in
									let valeur = !(List.assoc (adr_debut+(get_int index)) sigprim) in
									  (match valeur with
									    |InB(adre,size) -> (get_int adre,sigprim)
									    |_ -> (1,sigprim)) *)



(* check *)
and eval_dec env mem ast =
	match ast with
	|ASTConst(id,t,e) -> let (v,sigp) = eval_expr env mem e in  ((id,v)::env,sigp)
	|ASTFun(id,t,args,e) -> ((id,InF(e,parse_args args,env))::env,mem)
	|ASTFunRec(id,t,args,e) -> let params = parse_args args in
								 ((id,InFR(id,InF(e,params,env)))::env,mem)
	(*aps1*)
	|ASTVar(id,t) -> let (a,new_mem) = alloc(mem) in ((id,InA(a))::env,new_mem)
	|ASTProc(id,args,b) -> ((id,InP(b,parse_args args,env))::env,mem)
	|ASTProcRec(id,args,b) -> ((id,InPR(id,InP(b,parse_args args,env)))::env,mem)

and eval_expr env mem ast =
	match ast with
	ASTTrue -> (InN(1),mem)
	|ASTFalse -> (InN(0),mem)
	|ASTNum(n) -> (InN(n),mem)
	|ASTId(id) -> (match (List.assoc id env) with
				  |InA(a) -> (!(List.assoc a mem),mem)
				  |v -> (v,mem))
	|ASTLambda(args,e) -> (InF(e,parse_args args,env),mem)
	|ASTIf(e1,e2,e3) -> let (eval_e1,sigp) = (eval_expr env mem e1) in 
							if eval_e1 = InN(1) 
							then (eval_expr env sigp e2)	
							else (eval_expr env sigp e3)
	|ASTApply(e,args) -> let (fermeture,sigp) = eval_expr env mem e in 
					     let args_sig_list = eval_args env sigp args in
							let (valargs_list,sig_list) = List.split args_sig_list in 
							let last_sig = List.nth sig_list ((List.length sig_list)-1) in
												(match fermeture with
													|InF(body,params,env1) -> let closure_env = (List.map2 (fun x y -> (x,y)) params valargs_list)@env1 in
																												(eval_expr closure_env last_sig body)
													|InFR(f,InF(body,params,env1)) -> 
															let closure_env =(f,List.assoc f env)::(List.map2 (fun x y -> (x,y)) params valargs_list)@env1 in
													 															(eval_expr closure_env last_sig body)
													|_ -> failwith "erreur : impossible d'appliquer une valeur entière")
	|ASTOprim(oprim) -> 
				(match oprim with
						|ASTUnary(opun,arg) ->
							let (v,sigp) = eval_expr env mem arg in
								(match opun with
								|Not -> (InN(pi_un "not" (get_int v)),sigp)
								)
						|ASTBinary(opbin,arg1,arg2) ->
												let (aa1,sigp) = eval_expr env mem arg1 in 													
												let	(aa2,sigpp) = eval_expr env sigp arg2 in
													let a1 = get_int aa1 and a2 = get_int aa2 in 
													match opbin with
													| And -> (InN(pi_bin "and" a1 a2),sigpp)
													| Or -> (InN(pi_bin "or" a1 a2),sigpp)
													| Eq -> (InN(pi_bin "eq" a1 a2),sigpp)
													| Lt -> (InN(pi_bin "lt" a1 a2),sigpp)
													| Add -> (InN(pi_bin "add" a1 a2),sigpp)
													| Sub -> (InN(pi_bin "sub" a1 a2),sigpp)
													| Mul -> (InN(pi_bin "mul" a1 a2),sigpp)
													| Div -> (InN(pi_bin "div" a1 a2),sigpp))
	(*aps2*)
	|ASTAlloc(e) -> let (n,sigp) = eval_expr env mem e in (* n est un InN(int) et allocn retourne un couple de (adr du premier element, nouvelle mémoire) *)
					let (adr,sigpp) = (allocn sigp (get_int n)) in (InB(InA(adr),(get_int n)),sigpp)
	|ASTLen(e) -> let (inbloc,sigp) = eval_expr env mem e in 
					(match inbloc with 
					|InB(adr,n) -> (InN(n),sigp)
					|_ -> failwith "Error ASTLen : not a InB after evaluation")
	|ASTENth(e1,e2) -> let (inbloc,sigp) = eval_expr env mem e1 in
						let (inn_index,sigpp) = eval_expr env sigp e2 in
						let index = get_int inn_index in
						Printf.printf "c'est le cb eme element %d\n" index;
						begin
						match inbloc with
							|InB(a,n) -> Printf.printf "adresse = %d\n" ((get_int a)+index);let v = (List.assoc ((get_int a)+index) sigpp) in (match !v with |InB(a,b) -> Printf.printf "ououououououo adresse = %d taille = %d" (get_int a) b| InN(x) -> print_int x | _ -> print_endline "iiuiuiuiuiuiuiuiu");(!v,sigpp)
							|_ -> failwith "Error ASTENth : not a InB after evaluation"
						end

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
