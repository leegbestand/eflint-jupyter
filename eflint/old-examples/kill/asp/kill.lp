
% L0

fact(person(P1)) :- person(P1).

duty(not_to_kill(P1,P2)) :- person(P1), person(P2).
conditioned(not_to_kill(P1,P2),T) :- duty(not_to_kill(P1,P2)), time(T) . %,true. is implicit here

% L1

fact(prosecutor(P1)) :- person(P1).
fact(suspect(P1)) :- person(P1).
fact(victim(P1)) :- person(P1).
fact(investigator(P1)) :- person(P1).

act(prosecute(A,S,V)) :- fact(prosecutor(A)),fact(suspect(S)),fact(victim(V)).
conditioned(act(prosecute(A,S,V)),T) :- time(T), holdsAt(not_to_kill(S,V),T) , holdsAt(killed_by(V,S),T),act(prosecute(A,S,V)).

fact(killed_by(P1,P2)) :- person(P1), person(P2).

% L2
fact(poisoned_by(P1,P2)) :- person(P1), person(P2).

% L3
fact(alive(P)) :- person(P).

fact(substance(S)) :- substance(S).
fact(food(S)) :- food(S).
fact(poison(S)) :- substance(S).
fact(ingredient(S,F)) :- substance(S), food(F).
fact(mix_completed(P,S,F)) :- substance(S), food(F), person(P).
fact(eat_completed(P,F)) :- food(F), person(P).


act(mix(P,S,F)) :- fact(person(P)),fact(substance(S)),fact(food(F)).
conditioned(act(mix(P,S,F)),T) :- time(T), holdsAt(food(F),T), act(mix(P,S,F)).

initiates(mix(P,S,F),ingredient(S,F),T) :- time(T), act(mix(P,S,F)).
initiates(mix(P,S,F),mix_completed(P, S, F),T) :- time(T), act(mix(P,S,F)).


act(eat(P,F)) :-
							fact(person(P)), fact(food(F)).
conditioned(act(eat(P,F)),T) :-
							time(T), holdsAt(food(F),T), holdsAt(alive(P),T), act(mix(P,S,F)).

initiates(eat(P,F),eat_completed(P,F),T) :-
							time(T), act(eat(P,F)).

terminates(eat(P,F),food(F),T) :-
							time(T), act(eat(P,F)).

terminates(eat(P,F),alive(P),T) :-
   						time(T), act(eat(P,F)), holdsAt(mix_completed(P2,S,F),T), holdsAt(poison(S),T) .


act(qualify_poisoning(I,S,V)) :-
							fact(investigator(I)),
							fact(suspect(S)),
							fact(victim(V)).

conditioned(act(qualify_poisoning(I,Suspect,Victim)),T) :- act(qualify_poisoning(I,Suspect,Victim)),
							holdsAt(poison(Poison),T),
							holdsAt(mix_completed(Suspect,Poison,F),T),
							holdsAt(eat_completed(Victim,F),T),
							not holdsAt(alive(Victim),T).

initiates(qualify_poisoning(I,Suspect,Victim),poisoned_by(Victim,Suspect),T) :-
 							time(T), act(qualify_poisoning(I,Suspect,Victim)).


act(qualify_killing(I,S,V)) :-
							fact(investigator(I)), fact(suspect(S)), fact(victim(V)).

conditioned(act(qualify_killing(I,Suspect,Victim)),T) :- act(qualify_killing(I,Suspect,Victim)),
							holdsAt(poisoned_by(Victim,Suspect),T).

initiates(qualify_killing(I,Suspect,Victim),killed_by(Victim,Suspect),T) :-
							time(T), act(qualify_poisoning(I,Suspect,Victim)).

%============================
%============================

fluent(D) :- duty(D).
fluent(F) :- fact(F).
event(A) :- act(A).
%=======================================
% Act or not
%=======================================
%happens(F,T+1) ; false :- not happens(F2,T+1), conditioned(act(F),T), act(F), act(F2), time(T),time(T+1).
%:- happens(F1,T), happens(F2,T) , F1!=F2.
violation0(F,T) :- happens(F,T) ,not act(F), time(T).
violation1(F,T):- happens(F,T) ,not conditioned(act(F),T), time(T).


% All conditioned duties are held
holdsAt(D,T) :- duty(D), conditioned(D,T), time(T).
% Note: One can not create a conditional duty


:- releasedAt(F,0), fluent(F).


% eFlint examople voting
