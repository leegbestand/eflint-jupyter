%time(0).
%time(T+1) :- time(T), happens(E,T), event(E).
%final_time(T+1) :- time(T), not happens(F,T1),event(F), time(T1), not time(T+1).
terminated1(F,T) :- terminate(F,T).
initiated1(F,T) :- initiate(F,T).
