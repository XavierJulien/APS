main_stdin :- 
	read(user_input,T),
	typeProg(T,R),
	print(R),
	nl,
	exitCode(R).

assoc(X, [(X,V)|_], V).
assoc(X, [_|XS], V) :- assoc(X, XS, V).

/*(PROG)*/
typeProg(C,prog(X),void) :-
	typeCmds(C,X,void).
/*(END)*/
/*******************************************************A FAIRE*/
/*(STAT)*/
typeCmds(C,cmds(X,Y),void) :-
	typeStat(C,X,void),
	typeCmds(C,Y,void).
/*(ECHO)*/
typeStat(C,echo(X),void) :-
	typeExpr(C,X,int).
/*(DEC)*/
typeCmds(C,cmds(X,Y),void) :-
	typeDec(C,X,void),
	typeCmds(C,Y,void).
/*(CONST)*/
/*******************************************************A FAIRE*/
/*(FUN)*/
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
	/*verif type cond est bool dans C*/
	typeExpr(C,COND,bool),
	/*verif que e1 et e2 soient de type T dans C*/
	typeExpr(C,E1,T),
	typeExpr(C,E2,T).	
/********************************************************A FINIR*/
/*(APP)*/
typeExpr(C,apply(F,ARGS),T) :-	
	typeExpr(C,F,assoc(F,C,aveclafleche)),
	typeExpr(C,ARGS,avantlafleche)./*a completer*/
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


