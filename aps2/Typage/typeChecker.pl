main_stdin :-
	read(user_input,T),
	typeProg([],T,R),
	print(R).
	/*exitCode(R).*/

mem(X, [X|_]).
mem(X, [_|XS]) :- mem(X,XS).

assoc(X, [(X,V)|_], V).
assoc(X, [_|XS], V) :- assoc(X, XS, V).

/*(PROG)*/
typeProg(C,prog(X),void) :-
	typeCmds(C,X,void).

/*(END)*/
typeCmds(_,[epsilon],void).

typeCmds(C,[stat(X)|Y],void) :-
	typeStat(C,X,void),
	typeCmds(C,Y,void).

/*(DEC)*/
typeCmds(C,[dec(X)|Y],void) :-
	typeDec(C,X,CBIS),
	typeCmds(CBIS,Y,void).


/*(ECHO)*/
typeStat(C,echo(X),void) :-
	typeExpr(C,X,int).

/**************APS1*************/

/*(SET)*/
typeStat(C,set(id(ID),EXPR),void) :-
	assoc(ID,C,TYPE),
	typeExpr(C,EXPR,TYPE).

/*(BIF)*/
typeStat(C,bif(COND,B1,B2),void) :-
	typeExpr(C,COND,bool),
	typeBlock(C,B1,void),
	typeBlock(C,B2,void).
	
/*(WHILE)*/
typeStat(C,while(COND,B),void) :-
	typeExpr(C,COND,bool),
	typeBlock(C,B,void).
	
/*(CALL)*/
typeStat(C,call(id(P),ARGS),void) :-
	assoc(P,C,arrow(ARGSTYPE,void)),
	verif(C,ARGS,ARGSTYPE).

/**************APS2*************/
/*(SET)*/
typeStat(C,set(NTH,EXPR),void) :-
	typeExpr(C,NTH,TYPE),
	/*assoc(ID,C,TYPE),*/
	typeExpr(C,EXPR,TYPE).
/*******************************/

get_typeargs([],[]).
get_typeargs([(_,T)|ARGS],[T|RES]) :-
	get_typeargs(ARGS,RES).


/*(CONST)*/
typeDec(C,const(X,TYPE,EXPR),CBIS) :-
	typeExpr(C,EXPR,TYPE),
	CBIS=[(X,TYPE)|C].

/*(FUN)*/
typeDec(C,fun(ID,TYPERETOUR,ARGS,BODY),CBIS):-
	append(ARGS,C,CTER),
	typeExpr(CTER,BODY,TYPERETOUR),
	get_typeargs(ARGS,RES),
	CBIS=[(ID,arrow(RES,TYPERETOUR))|C].
	
/*(FUN REC)*/
typeDec(C,funrec(ID,TYPE,ARGS,BODY),CBIS):-
	get_typeargs(ARGS,RES),
	append(ARGS,C,CTER),
	C4 = [(ID,arrow(RES,TYPE))|CTER],
	typeExpr(C4,BODY,TYPE),
	CBIS=[(ID,arrow(RES,TYPE))|C].

	
	
	
/**************APS1***************/

/*(VAR)*/
typeDec(C,var(X,TYPE),CBIS) :-
	CBIS=[(X,TYPE)|C].

/*(PROC)*/
typeDec(C,proc(ID,ARGS,BODY),CBIS):-
	append(ARGS,C,CTER),
	typeBlock(CTER,BODY,void),
	get_typeargs(ARGS,RES),
	CBIS=[(ID,arrow(RES,void))|C].
	
	
/*(PROCREC)*/
typeDec(C,procrec(ID,ARGS,BODY),CBIS):-
	get_typeargs(ARGS,RES),
	append(ARGS,C,CTER),
	C4 = [(ID,arrow(RES,void))|CTER],
	typeBlock(C4,BODY,void),
	CBIS=[(ID,arrow(RES,void))|C].
	
/**********************************/
verif(_,[],[]).
verif(C,[ARG|ARGS],[ARGTYPE|ARGSTYPE]) :-
	typeExpr(C,ARG,ARGTYPE),
	verif(C,ARGS,ARGSTYPE).

get_type([],[]).
get_type([A|ARGS],[T|TYPES]) :-
	typeExpr([],A,T),
	get_type(ARGS,TYPES).

/*(TRUE)*/
typeExpr(_,true,bool).
/*(FALSE)*/
typeExpr(_,false,bool).
/*(NUM)*/
typeExpr(_,num(X),int) :-
 	integer(X).
/*(IDENT)*/
typeExpr(C,id(X),T) :-
	assoc(X,C,T).
/*(IF)*/
typeExpr(C,if(COND,E1,E2),T) :-
	typeExpr(C,COND,bool),
	typeExpr(C,E1,T),
	typeExpr(C,E2,T).
/*(APP)*/
typeExpr(C,apply(id(F),ARGS),TYPEF) :-
	assoc(F,C,arrow(ARGSTYPE,TYPEF)),
	verif(C,ARGS,ARGSTYPE).
typeExpr(C,apply(lambda(ARGSTYPE,BODY),ARGS),TYPEF) :-
	get_typeargs(ARGSTYPE,RES),
	verif(C,ARGS,RES),
	append(ARGSTYPE,C,CBIS),
	typeExpr(CBIS,BODY,TYPEF).
typeExpr(C,apply(apply(X,Y),ARGS),TYPERETOUR) :-
	get_type(ARGS,RES),
	typeExpr(C,apply(X,Y),arrow(RES,TYPERETOUR)).

/*(ABS)*/
typeExpr(C,lambda(ARGS,BODY),arrow(_,TYPEF)) :-
	append(ARGS,C,CBIS),
	typeExpr(CBIS,BODY,TYPEF).		

/**************APS2****************/
typeExpr(C,nth(E1,E2),TYPEL):-
	typeExpr(C,E1,vec(TYPEL)),
	typeExpr(C,E2,int).

typeExpr(C,len(E),int):-
	typeExpr(C,E,vec(_)).
	
typeExpr(C,alloc(E),vec(_)):-
	typeExpr(C,E,int).
	
/**********************************/

/*Opérations mathématiques*/
typeExpr(C,add(X,Y),int) :-
	typeExpr(C,X,int),
	typeExpr(C,Y,int).

typeExpr(C,sub(X,Y),int) :-
	typeExpr(C,X,int),
	typeExpr(C,Y,int).

typeExpr(C,mul(X,Y),int) :-
	typeExpr(C,X,int),
	typeExpr(C,Y,int).

typeExpr(C,div(X,Y),int) :-
	typeExpr(C,X,int),
	typeExpr(C,Y,int).

/*Opérations booléennes*/
typeExpr(C,and(X,Y),bool) :-
	typeExpr(C,X,bool),
	typeExpr(C,Y,bool).

typeExpr(C,or(X,Y),bool) :-
	typeExpr(C,X,bool),
	typeExpr(C,Y,bool).

typeExpr(C,eq(X,Y),bool) :-
	typeExpr(C,X,int),
	typeExpr(C,Y,int).

typeExpr(C,lt(X,Y),bool) :-
	typeExpr(C,X,int),
	typeExpr(C,Y,int).
	
typeExpr(C,not(X),bool) :-
	typeExpr(C,X,bool).
/*******APS1******/
typeBlock(C,block(X),void) :-
	typeCmds(C,X,void).

/*****************/
	
	
	
