:- discontiguous check/5.

verify(Input):-see(Input),read(T),read(L),read(S),read(F),seen,check(T,L,S,[],F),!.

% check X
check(_,L,S,[],X):-member([S,A],L),member(X,A).

% check neg(X)
check(_,L,S,[],neg(X)):- member([S,A],L), \+member(X,A).

checking_All(T,L,S,U,F):- member([S,K],T),checking_all_ways(T,L,U,F,K).

% check all possible ways (A)
checking_all_ways(_,_,_,_,[]).
checking_all_ways(T,L,U,F,[H|Tail]):- check(T,L,H,U,F),checking_all_ways(T,L,U,F,Tail).

% check some routes(E)
checking_some_ways(T,L,U,F,[H|Tail]):-check(T,L,H,U,F);checking_some_ways(T,L,U,F,Tail),!.

checking_some(T,L,S,U,F) :- member([S,V],T), checking_some_ways(T,L,U,F,V),!.

% check and(Y,G)
check(T,L,S,[],and(Y,G)):-check(T,L,S,[],Y), check(T,L,S,[],G).

% check or(Y,G)
check(T,L,S,[],or(Y,G)):-check(T,L,S,[],Y);check(T,L,S,[],G).

% check ax(X)
check(T,L,S,[],ax(X)):-checking_All(T,L,S,[],X).

% check ex(X)
check(T,L,S,[],ex(X)):-checking_some(T,L,S,[],X).

% check ag(X) basfall (1)
check(_,_,S,U,ag(_)):-member(S,U).

% check ag(X) (2)
check(T,L,S,U,ag(X)):- \+member(S,U), check(T,L,S,[],X), checking_All(T,L,S,[S|U],ag(X)).

% check af(X) (1)
check(T,L,S,U,af(X)):- \+member(S,U),check(T,L,S,[],X).

% check af(X) (2)
check(T,L,S,U,af(X)):- \+member(S,U), checking_All(T,L,S,[S|U],af(X)).

% check eg(X) basfall (1)
check(_,_,S,U,eg(_)):- member(S,U).

% check eg(X) (2)
check(T,L,S,U,eg(X)):- \+member(S,U),check(T,L,S,[],X), checking_some(T,L,S,[S|U],eg(X)).

% check ef(X) (1)
check(T,L,S,U,ef(X)):- \+member(S,U), check(T,L,S,[],X).

% check ef(X) (2)
check(T,L,S,U,ef(X)):- \+member(S,U), checking_some(T,L,S,[S|U],ef(X)).

