

:- module(lambda, [
		   (^)/3, (^)/4, (^)/5, (^)/6, (^)/7, (^)/8, (^)/9, (^)/10,
		   (\)/1, (\)/2, (\)/3, (\)/4, (\)/5, (\)/6, (\)/7, (\)/8,
		   (+\)/2, (+\)/3, (+\)/4, (+\)/5, (+\)/6, (+\)/7, (+\)/8,
			(+\)/9, op(201,xfx,+\)]).



:- meta_predicate
	^(?,0,?),
	^(?,1,?,?),
	^(?,2,?,?,?),
	^(?,3,?,?,?,?),
	^(?,4,?,?,?,?,?),
	^(?,5,?,?,?,?,?,?),
	^(?,6,?,?,?,?,?,?,?),
	^(?,7,?,?,?,?,?,?,?,?),
	\(0),
	\(1,?),
	\(2,?,?),
	\(3,?,?,?),
	\(4,?,?,?,?),
	\(5,?,?,?,?,?),
	\(6,?,?,?,?,?,?),
	\(7,?,?,?,?,?,?,?),
	+\(?,0),
	+\(?,1,?),
	+\(?,2,?,?),
	+\(?,3,?,?,?),
	+\(?,4,?,?,?,?),
	+\(?,5,?,?,?,?,?),
	+\(?,6,?,?,?,?,?,?),
	+\(?,7,?,?,?,?,?,?,?).

:- meta_predicate no_hat_call(0).

^(V1,C_0,V1) :-
   no_hat_call(C_0).
^(V1,C_1,V1,V2) :-
   call(C_1,V2).
^(V1,C_2,V1,V2,V3) :-
   call(C_2,V2,V3).
^(V1,C_3,V1,V2,V3,V4) :-
   call(C_3,V2,V3,V4).
^(V1,C_4,V1,V2,V3,V4,V5) :-
   call(C_4,V2,V3,V4,V5).
^(V1,C_5,V1,V2,V3,V4,V5,V6) :-
   call(C_5,V2,V3,V4,V5,V6).
^(V1,C_6,V1,V2,V3,V4,V5,V6,V7) :-
   call(C_6,V2,V3,V4,V5,V6,V7).
^(V1,C_7,V1,V2,V3,V4,V5,V6,V7,V8) :-
   call(C_7,V2,V3,V4,V5,V6,V7,V8).

\(FC_0) :-
   copy_term_nat(FC_0,C_0),
   no_hat_call(C_0).
\(FC_1,V1) :-
   copy_term_nat(FC_1,C_1),
   call(C_1,V1).
\(FC_2,V1,V2) :-
   copy_term_nat(FC_2,C_2),
   call(C_2,V1,V2).
\(FC_3,V1,V2,V3) :-
   copy_term_nat(FC_3,C_3),
   call(C_3,V1,V2,V3).
\(FC_4,V1,V2,V3,V4) :-
   copy_term_nat(FC_4,C_4),
   call(C_4,V1,V2,V3,V4).
\(FC_5,V1,V2,V3,V4,V5) :-
   copy_term_nat(FC_5,C_5),
   call(C_5,V1,V2,V3,V4,V5).
\(FC_6,V1,V2,V3,V4,V5,V6) :-
   copy_term_nat(FC_6,C_6),
   call(C_6,V1,V2,V3,V4,V5,V6).
\(FC_7,V1,V2,V3,V4,V5,V6,V7) :-
   copy_term_nat(FC_7,C_7),
   call(C_7,V1,V2,V3,V4,V5,V6,V7).


+\(GV,FC_0) :-
   copy_term_nat(GV+FC_0,GV+C_0),
   no_hat_call(C_0).
+\(GV,FC_1,V1) :-
   copy_term_nat(GV+FC_1,GV+C_1),
   call(C_1,V1).
+\(GV,FC_2,V1,V2) :-
   copy_term_nat(GV+FC_2,GV+C_2),
   call(C_2,V1,V2).
+\(GV,FC_3,V1,V2,V3) :-
   copy_term_nat(GV+FC_3,GV+C_3),
   call(C_3,V1,V2,V3).
+\(GV,FC_4,V1,V2,V3,V4) :-
   copy_term_nat(GV+FC_4,GV+C_4),
   call(C_4,V1,V2,V3,V4).
+\(GV,FC_5,V1,V2,V3,V4,V5) :-
   copy_term_nat(GV+FC_5,GV+C_5),
   call(C_5,V1,V2,V3,V4,V5).
+\(GV,FC_6,V1,V2,V3,V4,V5,V6) :-
   copy_term_nat(GV+FC_6,GV+C_6),
   call(C_6,V1,V2,V3,V4,V5,V6).
+\(GV,FC_7,V1,V2,V3,V4,V5,V6,V7) :-
   copy_term_nat(GV+FC_7,GV+C_7),
   call(C_7,V1,V2,V3,V4,V5,V6,V7).


%% no_hat_call(:Goal_0)
%
% Like call, but issues an error for a goal (^)/2.  Such goals are
% likely the result of an insufficient number of arguments.

no_hat_call(MGoal_0) :-
   strip_module(MGoal_0, _, Goal_0),
   (  nonvar(Goal_0),
      Goal_0 = (_^_)
   -> throw(
			error(
				existence_error(lambda_parameter,MGoal_0),
				_))
	;	call(MGoal_0)
   ).

% I would like to replace this by:
% V1^Goal :- throw(error(existence_error(lambda_parameter,V1^Goal),_)).

solve:-
    solve(Moves),
    display(Moves).

% Find solution
solve(Moves):-
    jump([1], [2,3,4,5,6,7,8,9,10,11,12,13,14,15], [], Moves).

solve(Moves1):-
    jump([2], [1,3,4,5,6,7,8,9,10,11,12,13,14,15], [], Moves1).

solve(Moves2):-
    jump([3], [1,2,4,5,6,7,8,9,10,11,12,13,14,15], [], Moves2).

solve(Moves3):-
    jump([4], [1,2,3,5,6,7,8,9,10,11,12,13,14,15], [], Moves3).

solve(Moves4):-
    jump([5], [1,2,3,4,6,7,8,9,10,11,12,13,14,15], [], Moves4).

jump(_, [_], Lst, Moves):-
    reverse(Lst, Moves).

% Free = empty space
% Occupied = filled space
jump(Free, Occupied, Lst, Moves):-
    select(S, Occupied, Oc1),
    select(O, Oc1, Oc2),
    select(E, Free, F1),
    move(S, O, E),
    jump([S, O | F1], [E | Oc2], [move(S,O,E) | Lst], Moves).

% legal moves
move(S,2,E):-
    member([S,E], [[1,4], [4,1]]).
move(S,3,E):-
    member([S,E], [[1,6], [6,1]]).
move(S,4,E):-
    member([S,E], [[2,7], [7,2]]).
move(S,5,E):-
    member([S,E], [[2,9], [9,2]]).
move(S,5,E):-
    member([S,E], [[3,8], [8,3]]).
move(S,6,E):-
    member([S,E], [[3,10], [10,3]]).
move(S,5,E):-
    member([S,E], [[4,6], [6,4]]).
move(S,7,E):-
    member([S,E], [[4,11], [11,4]]).
move(S,8,E):-
    member([S,E], [[4,13], [13,4]]).
move(S,8,E):-
    member([S,E], [[5,12], [12,5]]).
move(S,9,E):-
    member([S,E], [[5,14], [14,5]]).
move(S,9,E):-
    member([S,E], [[6,13], [13,6]]).
move(S,10,E):-
    member([S,E], [[6,15], [15,6]]).
move(S,8,E):-
    member([S,E], [[9,7], [7,9]]).
move(S,9,E):-
    member([S,E], [[10,8], [8,10]]).
move(S,12,E):-
    member([S,E], [[11,13], [13,11]]).
move(S,13,E):-
    member([S,E], [[12,14], [14,12]]).
move(S,14,E):-
    member([S,E], [[15,13], [13,15]]).

% Display Solution 1
display(Sol):-
    display(Sol, [1]).
% Display solution by level
% Xs and Os
display([], Free):-
    numlist(1,15, Lst),
    maplist(\X^I^(member(X, Free) -> I = 'O'; I = 'X'), Lst, [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15]),
    format('    ~w        ~n', [I1]),
    format('   ~w ~w      ~n', [I2,I3]),
    format('  ~w ~w ~w    ~n', [I4,I5,I6]),
    format(' ~w ~w ~w ~w  ~n', [I7,I8,I9,I10]),
    format('~w ~w ~w ~w ~w ~n~n', [I11,I12,I13,I14,I15]),
    writeln(complete).
	
	display([move(Start, Middle, End) | Tail], Free):-
    numlist(1,15, Lst),
    maplist(\X^I^(member(X, Free) -> I = 'O'; I = 'X'), Lst, [I1,I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15]),
    format('    ~w        ~n', [I1]),
    format('   ~w ~w      ~n', [I2,I3]),
    format('  ~w ~w ~w    ~n', [I4,I5,I6]),
    format(' ~w ~w ~w ~w  ~n', [I7,I8,I9,I10]),
    format('~w ~w ~w ~w ~w ~n~n', [I11,I12,I13,I14,I15]),
    select(End, Free, F1),
    display(Tail,  [Start, Middle | F1]).
