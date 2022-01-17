% clingo --verbose=4 -c maxtime=20 dec.lp kill.lp general.lp kill_0.lp


person(alice).
person(bob).
person(chloe).
person(david).

food(curry).
food(salad).


substance(salt).
substance(sugar).
substance(polonium).
substance(ratpoison).

holdsAt(person(P),0):- fact(person(P)).
holdsAt(alive(P),0):- fact(alive(P)).
holdsAt(food(F),0):- fact(food(F)).

holdsAt(poison(ratpoison),0).
holdsAt(poison(polonium),0).

happens(mix(alice,salt,curry),1).
happens(mix(alice,sugar,curry),2).
happens(mix(bob,sugar,curry),3).
happens(eat(bob,curry),4).
happens(qualify_poisoning(chloe,alice,bob),5).
%happens(act(mix(john,salt,curry)),0).

% conditioned(act(qualify_poisoning(chloe,bob,alice),5)).
%#show X: act(mix(X,Y,Z)).
%#show holdsAt/2.
#show happens/2.
#show violation0/2.
#show violation1/2.
%#show X : person(X), not holdsAt(alive(X),T), time(T).

%#show time/1.
%#show X : holdsAt(ingredient(X,curry),Z).
