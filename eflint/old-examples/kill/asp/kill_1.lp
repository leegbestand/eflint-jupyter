% clingo --verbose=4 -c maxtime=20 dec.lp kill.lp general.lp kill_1.lp


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
happens(mix(alice,ratpoison,curry),2).
happens(mix(bob,sugar,curry),3).
happens(eat(bob,curry),4).
terminate(alive(bob),5).
%happens(qualify_poisoning(chloe,alice,bob),6).
%happens(qualify_killing(chloe,alice,bob),7).
happens(prosecute(david,alice,bob),8).
%happens(act(mix(john,salt,curry)),0).

%#show X: act(mix(X,Y,Z)).
%#show holdsAt/2.
#show happens/2.
#show violation0/2.
#show violation1/2.
%#show holdsAt/2.
%#show Y : holdsAt(mix_completed(X,Y,Z),T), time(T).
%#show conditioned/2.
%#show I : act(qualify_poisoning(I,Suspect,Victim)).
%#show I : fact(investigator(I)).
%#show act/1.
%#show X : holdsAt(ingredient(X,curry),Z).
