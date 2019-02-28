main_stdin :-
	read(user_input,T),
	typeProg([],T,R),
	print(R),
	nl,
	exitCode(R).

mem(X, [X|_]).
mem(X, [_|XS]) :- mem(X,XS).

assoc(X, [(X,V)|_], V).
assoc(X, [_|XS], V) :- assoc(X, XS, V).

/*(PROG)*/
typeProg(C,prog(X),void) :-
	typeCmds(C,X,void).
/*(END)*/
/*******************************************************A FAIRE*/
/*(STAT)*/
typeCmds(C,stat(X),void) :-
	typeStat(C,X,void).

typeCmds(C,cmds(stat(X)),void) :-
	typeStat(C,X,void).

typeCmds(C,cmds(stat(X),Y),void) :-
	typeStat(C,X,void),
	typeCmds(C,Y,void).
/*(DEC)*/
typeCmds(C,cmds(dec(X),Y),void) :-
	typeDec(C,X,CBIS),
	typeCmds(CBIS,Y,void).
/*(ECHO)*/
typeStat(C,echo(X),void) :-
	typeExpr(C,X,int).
/*(CONST)*/
typeDec(C,const(X,TYPE,EXPR),CBIS) :-
	typeExpr(C,EXPR,TYPE),
	CBIS=[(X,TYPE)|C].
/*(FUN)*/

typeDec(C,fun(ID,TYPE,(X,T),BODY),CBIS):-
	append([(X,T)],C,CTER),
	typeExpr(CTER,BODY,TYPE),
	get_typeargs((X,T),RES),
	CBIS=[(ID,arrow_type(RES,TYPE))|C].


typeDec(C,fun(ID,TYPE,ARGS,BODY),CBIS):-
	append(ARGS,C,CTER),
	typeExpr(CTER,BODY,TYPE),
	get_typeargs(ARGS,RES),
	CBIS=[(ID,arrow_type(RES,TYPE))|C].

get_typeargs([],[]).
get_typeargs([(_,T)|ARGS],[T|RES]) :-
	get_typeargs(ARGS,RES).
/*******************************************************A FAIRE*/
/*(FUN REC)*/
/*******************************************************A FAIRE*/
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
/********************************************************A FINIR*/
/*(APP)*/
typeExpr(C,apply(id(F),ARGS),T) :-
	typeExpr(C,id(F),assoc(F,C,)),
	typeExpr(C,ARGS,get_typeargs()),/*a completer*/
	typeExpr(C,T,apreslafleche).
/******************************************************* A FINIR*/
/*(ABS)*/
/*******************************************************A FAIRE*/

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
