:- discontiguous proof_validation/3.

verify(InputFileName) :- see(InputFileName),
                         read(Prems), read(Goal), read(Proof),
                         seen,
                         valid_proof(Prems, Goal, Proof).


%cheking if the last element is goal and cheking is the proof is correct
valid_proof(Prems,Goal,Proof) :- goal_checking(Proof,Goal),
proof_Checking(Prems,Proof,[]), !.

%cut/1 predicat"!" prevents backtracking of the clauses, prolog wont backtrack beyond %the cut

% Cheking if the goal and the last line is the same, if the goal and the last line
% is the same but its en assumption then it fails
goal_checking(Proof,Goal):-last(Proof,[_,Goal,assumption]),!,fail.
goal_checking(Proof,Goal):-last(Proof,[_,Goal,_]).


% checking if the proof is valid, if we have empty list then we are done

proof_Checking(_,[],_).

proof_Checking(Prems,[H|T],Already_checked):-
proof_validation(Prems,H,Already_checked),
append(Already_checked,[H],NewList),
proof_Checking(Prems,T,NewList).


% box: cheking is we have a sublist in the proof and the first line and last line
% in the box
box_cheking(First, Last, Already_checked):- member([First|T],Already_checked),last(T,Last).

box_cheking(A,A,Already_checked):-member([A],Already_checked).

% handle premise
proof_validation(Prems, [_,Atom,premise], _):-member(Atom,Prems).

% handle assumption
proof_validation(Prems,[[_,_,assumption]|T],Already_checked):-
append(Already_checked,[[_,_,assumption]],NewList),proof_Checking(Prems,T,NewList).

% handle copy (copy(X))
proof_validation(_,[_,A,copy(X)],Already_checked):-member([X,A,_],Already_checked).

% handle and introduktion (andint(X,Y))
proof_validation(_,[_,and(A,H),andint(X,Y)], Already_checked):-member([X,A,_],Already_checked), member([Y,H,_],Already_checked).

% handle and elimination 1 (andel1(X))
proof_validation(_,[_,A,andel1(X)],Already_checked):- member([X,and(A,_),_],Already_checked).

% handle and elimination 2 (andel2(X))
proof_validation(_,[_,H,andel2(X)],Already_checked):- member([X,and(_,H),_],Already_checked).

%handle or introduktion 1 (orint1(X))
proof_validation(_,[_,or(A,_),orint1(X)], Already_checked):- member([X,A,_],Already_checked).


%handle or introduktion 2 (orint2(X))
proof_validation(_,[_,or(_,H), orint2(X)], Already_checked):- member([X,H,_],Already_checked).

%handle or elimination (orel(X,Y,U,V,W))
proof_validation(_,[_,A,orel(X,Y,U,V,W)],Already_checked):- member([X, or(B,H),_],Already_checked), box_cheking([Y,B,assumption],[U,A,_],Already_checked), box_cheking([V,H,assumption],[W,A,_],Already_checked).

% handle implikations elimination (impel(X,Y))
proof_validation(_,[_,B,impel(X,Y)],Already_checked):-member([X,A,_],Already_checked), member([Y, imp(A,B),_],Already_checked).

%handle implikations introduktion (impint(X,Y))
proof_validation(_,[_,imp(A,H),impint(X,Y)],Already_checked):-box_cheking([X,A,assumption],[Y,H,_],Already_checked).

% handle negations elimination (negel(X,Y))
proof_validation(_,[_,cont,negel(X,Y)],Already_checked):-member([X,A,_],Already_checked),member([Y,neg(A),_],Already_checked).

% handle negations introduktion (negint(X,Y))
proof_validation(_,[_,neg(A),negint(X,Y)],Already_checked):- box_cheking([X,A,assumption],[Y,cont,_],Already_checked).

%handle negations negations introduktion (negnegint(X))
proof_validation(_,[_,neg(neg(Atom)),negnegint(X)],Already_checked):-member([X,Atom,_],Already_checked).

% handle negations negations elimination (negnegel(X))
proof_validation(_,[_,Atom,negnegel(X)],Already_checked):-member([X,neg(neg(Atom)),_],Already_checked).

% handle contraduction (contel(X))
proof_validation(_,[_,_,contel(X)],Already_checked):-member([X,cont,_],Already_checked).

% handle MT (mt(X,Y))
proof_validation(_,[_,_,mt(X,Y)],Already_checked):-member([X,imp(_,B),_],Already_checked),member([Y,neg(B),_],Already_checked).

% handle PBC (pbc(X,Y))
proof_validation(_,[_,A,pbc(X,Y)],Already_checked):- box_cheking([X, neg(A),assumption],[Y,cont,_],Already_checked).

% handle LEM (lem)
proof_validation(_,[_,or(A,neg(A)),lem],_).



