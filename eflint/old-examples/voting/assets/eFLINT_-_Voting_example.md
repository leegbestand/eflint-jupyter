# eFLINT - Voting example
*The purpose of this document is to informally explain the core features of eFLINT through an example policy description. The policy is designed to demonstrate the core features of eFLINT and is not necessarily representative of any real-world policy.*

# Fact declarations

A policy description in eFLINT consists of several declarations of *facts*. 


    Fact citizen
    Fact candidate
    Fact administrator 

The fragment above introduces the *fact identifiers* `citizen`, `candidate`, and `administrator`. Depending on where they occur, fact identifiers play different roles. For example, when occurring in a type, as shown later, a fact identifier is a placeholder for a type. Every declaration assigns a type to its fact identifier. Implicitly, the above declarations assign the type `Atom`. Written in full, these declarations are as follows:


    Fact citizen Identified by Atom
    Fact candidate Identified by Atom
    Fact administrator Identified by Atom

The part completing the `Identified from`-clause is a type expression. An example of type expressions with a type variable is provided by the following declarations:


    Fact voter Identified by citizen
    Fact winner Identified by candidate

Examples of instances of the `Atom` type are `Alice` and `Bob` (atoms are uppercase-starting identifiers distinct from the uppercase-starting keywords). Example instances of type `citizen` are `Alice:citizen` and `Bob:citizen`. Instances of the form `e:n`, where `n` is a (declared) fact identifier and `e` is an instance of some other type, are called *potential facts*. Whether a potential fact holds true, at a particular moment in time $$t$$, is determined by a set of potential facts capturing the *state* (of the world) at time $$t$$. Thus, a potential fact $$f$$ holds true in the context of a state $$\sigma$$ if $$f\in\sigma$$. 

The intuition behind the fact identifiers introduced so far is that if `A` is an atom and `A:citizen` holds, then `A` has been recognized as a citizen (and similar for candidates and administrators). If `(A:citizen):voter` holds true, then `A` is not only recognized as a citizen, but as a citizen in the electorate. (As shown later, the fact that a particular citizen has this *right* to vote can be deduced from observing that voters have the power to cast a vote.) Similarly, if `(A:candidate):winner` holds true, then `A` is a candidate declared winner.

Types can be formed by taking the product of other types (non-recursively):


    Fact vote Identified by (voter * candidate)

An instance of a product-type is written in tuple-notation, i.e. `(V, C)` is an instance of `(voter * candidate])` if `V` is an instance of `voter` and `C` of candidate. A concrete example of an instance of the type `vote` is `((Alice:citizen):voter, Chloe:candidate):vote` and the instance represents that `Alice` has voted on `Chloe` if the instance holds true.

# Expressions

A fact identifier `x` appearing in an expression is a placeholder for an instance of the type `x`. Additional placeholders for the type `x` can be introduced by introducing aliases for fact identifiers.
For example, in the following fragment `other candidate` is an alias for the fact identifier `candidate` and can thus be used as a variable whose instances must be instances of the type `candidate` (the example also shows that identifiers can consist of several words):


    Placeholder other candidate For candidate

Without explicit `Placeholder`-declarations, fact identifiers can be decorated with trailing integers and prime symbols to form aliases of the fact identifier. For example, `candidate1`, `candidate2` and `candidate``'` are all aliases of `candidate`.

A fact identifier plays the role of a *constructor* (for creating instances) when provided with arguments as part of a constructor-application. For example, the expression `voter(Alice)` applies the identifier `voter` as a constructor to the atom `Alice`. The result of this application is the instance `(Alice:citizen):voter`. (The fact that `Alice` is an instance of `citizen` is inferred from the type of `voter`). An other example of constructor application is `vote(voter(Alice),Chloe)`, constructing the instance of the potential fact that `Alice`  has voted on `Chloe`. 
In the latter example, the relative positioning of the arguments is important. The first argument must be a valid instance of `voter` and the second argument must be a valid instance of `candidate`, as determined by the type of `vote`. The type of `vote` also determines that exactly two arguments need to be given, as the type is a product of two types.

In another style of constructor application, arguments can be named to connect them with the type for which the constructor is creating an instance. For example, in the expression `voter(candidate = Alice)`, it is made explicit that `Alice` is to take up the role of `candidate` in the created instance for `voter`. There are two benefits to using this style: arguments can be written in any order, and arguments can be omitted. When an argument is omitted, the constructor application is automatically completed with variables for the missing fact identifiers. For example `vote(candidate = Chloe)` is equivalent to `vote(candidate = Chloe, voter = voter)`. Both these expressions are only valid if the variable `voter` is bound by their context.
Note that this style of constructor application demands that if a fact identifier is assigned a product type, then the type variables that constitute the product must be distinct (analogous to why columns in a database table must have distinct names).

Other forms of expressions are literals such as atoms and integers, and the application of operators to sub-expressions. A complete breakdown of the structure of expressions (and also of types) can be found in the formalization of eFLINT provided in the supplementary materials.

## Nondeterminism

As suggested before, every occurrence of a variable must be ‘bound’ by the context in which the variable occurs. Bindings are introduced, for example, by the $$\exists$$-operator, concretely written as `(Exists x1,…,xn : e)` where `x1,…,xn` are ‘binders’ — variables for which bindings will be introduced — and `e` is a Boolean expression. All occurrences of the variables `x1,…,xn` are bound inside `e`. The semantics of `(Exists x1,…,xn : e)` are to determine whether there is a valid combination of instances for the variables `x1,…,xn` so that `e` evaluates to `True`, returning `True` if this is the case and `False` otherwise. The expression `(Exists x1,…,xn : e)` is nondeterministic in the sense that `e` is evaluated an unspecified amount of times and in an unspecified order. However, it is ‘effectively deterministic’ because the outcome of evaluation is the same regardless, as long as the implementation is sound with respect to the given semantics. The $$\exists$$-operator is only practical if types have a bounded number of instances, as otherwise infinitely many combinations of instantiations of the variables `x1,…,xn` might exist. To ensure this, types need are refined when concrete cases are analyzed, as discussed later.
More examples of locations where bindings are introduced, as well as of nondeterministic evaluation, are encountered in what follows.

# Acts and duties

Some fact declarations in eFLINT are special in the sense that they introduce facts with meta-properties. These facts capture the ‘duty-claim’ and ‘power-liability’ relations of Hohfeld. 

## Duties

A *duty declaration* is a fact declaration describing the structure of a particular ‘duty-claim’ relation, therefore consisting of a ‘holder’ and a ‘claimant’ component — the actors holding the duty or having a claim to the duty respectively — and zero or more ‘objects’. If an instance of a duty holds true, then the instance is an element of the duty-claim relation described by the duty (thus stating that the holder of the duty indeed holds the duty). 
An example is provided by the following fragment:


    Duty duty to vote Holder voter Claimant administrator 

In this example, the meta-properties of `duty to vote` are that the duty-holder is a voter and the duty-claimant is an administrator. The duty-claim relation described by this declaration has no objects. The type associated with identifier `duty to vote` is `(voter * administrator)`. In general, the type associated with any duty identifier is the product of the types of the holder, claimant and objects. 

## Acts

An *act declaration* is a fact declaration describing the structure of a particular ‘power-liability’ relation, therefore consisting of an ‘actor’ and a ‘recipient’ component, as well as zero or more objects (listed in the `Related to`-clause in the example below). The type associated with an act identifier is the product of the types of the actor, recipient and objects. An act declaration also associates a pre-condition (`Conditioned by` below) and several post-conditions with an act identifier. The pre-condition is a Boolean expression. The post-conditions are expressions that evaluate to fact instances. Post-conditions are either *terminating* (`Terminates` below) or *creating* (`Creates` below). An example is provided by the `cast vote` act declared in the following fragment:


    Act cast vote
      Actor voter
      Recipient administrator
      Related to candidate
      Conditioned by
        voter && !has voted()
      Creates
        vote()
      Terminates
        duty to vote()

An instance of `cast vote` thus contains a voter, an administrator and a candidate and, if it holds true, indicates that the voter has the power to vote on the candidate and that the administrator is liable to this power (is bound to accept the result of the execution of this power). Note that an instance of `cast vote` does **not** indicate that the voter has cast its vote on the candidate, but instead that it has the power to do so. More precisely, the voter only has this power in those states in which the pre-condition of the act evaluates to `True`. 
In this example, the pre-condition expresses that `voter` must hold true as writing a fact identifier in a Boolean expression evaluates to whether the substitution of that variables holds true. The pre-condition also states that the instance of `has voted` constructed by the application `has voted()` does not hold true, indicating that the `voter` has not already placed a vote (the declaration of `has voted` is given later).

If the pre-condition holds in a particular state, then the act enables a particular *action*. An action modifies the current state by removing and adding potential facts. Which potential facts are removed or added is indicated by the terminating and creating post-conditions, respectively, of the act. In this example, the instance of `vote` constructed by `vote()` will be added to the state and the instance constructed by `duty to vote()` will be removed. Note that these applications are implicitly equivalent to `vote(voter = voter, candidate = candidate)` and `duty to vote(voter = voter, administrator = administrator)` respectively. The variables `voter`, `candidate` and `administrator` occurring in these expressions are bound by the occurrences in the `Actor`, `Recipient` and `Related to`-clauses of the declaration.
To determine whether an instance of an act enables an action, and to determine the effects of that action, the pre-conditions and post-conditions associated with the act are evaluated with bindings for each of the (top-level) components of the instance. For example, for the instance `((Alice:citizen):voter, Admin:administrator, Chloe:candidate):cast vote`, the pre-condition and post-conditions are evaluated in the context with `voter`, `administrator`, and `candidate` bound to instances `(Alice:citizen):voter)`, `Admin:administrator` and `Chloe:candidate` respectively, but not with `citizen` bound to `Alice` as `citizen` is not a top-level component of `cast vote`.

# Derived facts

As explained earlier, a potential fact $$f$$ holds true in a state $$\sigma$$ if $$f\in\sigma$$, where $$\sigma$$ represents the current state of the world. The state changes through actions (and events, introduced later), starting with some initial state $$\sigma_0$$. 

A potential fact may also hold true in $$\sigma$$ if it can be *derived* from other facts in $$\sigma$$. A *potentially derived fact* $$g$$ is declared alongside a derivation expression that determines, in the context of some $$\sigma$$, which instances of the type of $$g$$ hold true in $$\sigma$$. The derivation expression may refer to potential facts or potentially derived facts (also if they do not hold true). Derived facts cannot be created or terminated by acts and cannot be listed in the initial state; derived facts are computed, and, as such, are not data. An example of a derived fact declaration is provided by `has voted`:


    Fact has voted Identified by voter
      Present When (Exists candidate : vote(voter,candidate))

The derivation expression follows the `Present When`-clause and, in this example, states that a `voter` has voted — i.e. `has voted(voter)` holds true — if there is a candidate for which `vote(voter,candidate)` hold true. The top-level components of the type of a derived fact are bound in the derivation expression of the fact. In the above example, only `voter` is bound.

The fact `has voted` is a predicate over voters and, implicitly, over states. The following examples of derived facts are predicates over states only:


    Predicate vote concluded When (Exists candidate : winner(candidate))
    Predicate voters done    When !(Exists citizen : voter() && !has voted())

If `<ID>` and `<EXPR>` are a fact identifier and a derivation expression, then the syntax `Predicate <ID> When <EXPR>` is syntactic sugar for the following (where `()` is the empty product-type):


    Fact <ID> Identified by () Present When <EXPR>

Returning to the example, the only instance of `vote concluded` is thus `():vote concluded`, (where `()` is the only instance of the empty product-type), which holds true only when there is a winning candidate. Similarly, `():voters done` holds true only if there is no citizen in the electorate that has not yet voted. Equivalently, `voters done` can also be declared as follows:


    Predicate voters done When (Forall citizen : !voter() || has voted(voter()))

In other words, the predicate `voters done` holds when every citizen is either not in the electorate or has indeed voted.
Note that in the derivation expression, the constructor application of `has voted` requires an argument, as there is no `voter` variable in scope.

# Aggregation
## Aggregator operators

The `Exists` and `Forall` operators demonstrate a mechanism in which a sub-expression is evaluated repeatedly in different context, each binding the variables mentioned as binders to a different combination of valid instances of the types of those variables. In the case of `Exists` and `Forall`, the sub-expression must be a Boolean expression. This section demonstrates an extended usage of this mechanism in which the sub-expression may produce arbitrary values, not just Booleans. The `Foreach`-operator has the same syntax as `Exists` and `Forall` (except for the keyword name) and expressions formed by the `Foreach`-operator may produce multiple result values, one for each evaluation of its sub-expression. However, to prevent this non-determinism from 'escaping’, the `Foreach`-operator must always be used in combination with an *aggregator*. An aggregator is an operator that combines the possibly many results produced by `Foreach` in to a single value. For example, the `Count`-operator is an aggregator that counts the number of evaluation results produced by `Foreach`. The `Sum`-operator expects `Foreach` to produce a collection of numbers, and yields the sum of these numbers as its (single) evaluation result.

As an example, the following declaration introduces `number of votes` as a derived fact:


    Fact number of votes Identified by Int
      Derived from Count(Foreach vote : vote When Holds(vote))

The declaration determines that if `I` is an instance of the type `Int` (that is, `I` is an integer), then `I:number of votes` is an instance of `number of votes`. The derivation expression is provided by the `Derived from`-clause. The `Derived from`-clause is different from `Present When` in that its derivation expression computes instances rather than a Boolean. The instance produced by this type of derivation expression are those instances that hold true according to the derivation expression. There are no bindings active when this type of derivation expression is evaluated.

In the case of `number of votes`, there is only one instance of `number of votes` that holds true, namely `I:number of votes`, where `I` is the number of instances of `vote` that hold true. (Note that the derivation expression computes `I`, which is automatically lifted to `I:number of votes`.) The `When` operator inside the application of `Foreach` effectively filters out certain evaluation results. In this case, only instances of `vote` that hold true must be counted, as indicated by the occurrence of `Holds(vote)` as the second operand of `When`. In general, the `When` operator has two operands and either evaluates to the result of evaluating the first operand or fails if the second operand evaluates to `False`. Applications of `Foreach`, `Exists` or `Forall` do not consider the results of evaluating their sub-expression in contexts that cause failure.

## Aggregation in post-conditions

As the following declaration of `enable vote` shows, actions may result in the addition (or removal) of more than one potential fact to (from) a state $$\sigma$$. Multiple expressions can be written in the `Creates` or `Terminates`-clauses of an act declaration. Moreover, each of these expressions may be wrapped inside an occurrence of `Foreach`, indicating that each instance produced by evaluating the expression with different combinations of bindings are to be added (or removed).


    Act enable vote
      Actor administrator
      Recipient citizen
      Conditioned by !voter() && !vote concluded
      Creates voter(),
              duty to vote(voter = voter()),
              (Foreach candidate : cast vote(voter = voter()))

The declaration of `enable vote` determines that administrators have the power to add a citizen to the electorate if the citizen is not already in the electorate and if the vote has not already been concluded. The effect of acting on this power is that the instance created by `voter()` will come to hold true, that the instance created by `duty of vote(voter = voter())` will come to hold true and that every instance constructed by `cast vote(voter = voter())` will come to hold true. Note that `cast vote(voter = voter())` is equivalent to  `cast vote(voter = voter(), candidate = candidate)` and that `candidate` is bound (to every instance of `candidate`) by the surrounding `Foreach`. To summarize, an administrator has the power to grant every citizen the power to vote on every candidate (and also gives them the duty to vote).

## `Present When` as syntactic sugar

In fact, the `Present When`-clause is syntactic sugar for a particular common usage of `Derived from`. If `<ID>` is a fact identifier and `<EXPR>` is a Boolean expression, then the `Present When <EXPR>` clause of the declaration of `<ID>` is equivalent to the following `Derived from`-clause:


      Derived from (Foreach x1,...,xn : <ID>() When <EXPR>)

The variables `x1,…,xn` that occur as binders in the `Foreach` are the top-level components of the type associated with `<ID>` by the overarching declaration. In the above fragment `<ID>()` is to be understood as the application of `<ID>` as a constructor, which implicitly has the arguments `x1 = x1`, `x2 = x2`, etc.

## Completing the example

Many of the discussed features come together in the declaration of `declare winner` which is given below and which completes the policy description.


    Act declare winner
      Actor administrator
      Recipient candidate
      Conditioned by !vote concluded && voters done &&
       (Forall other candidate : 
          Count(Foreach vote : vote[voter] When vote && vote[candidate] == other candidate) < 
          Count(Foreach vote : vote[voter] When vote && vote[candidate] == candidate)
         When other candidate != candidate)
      Creates winner(candidate)

The declaration of `declare winner` determines that an administrator has the power to declare a particular candidate as the winner of the vote if the vote has not been concluded (there is no winner yet), if all of the voters have voted and if all other candidates have (strictly) less votes. The first line starting with `Count` produces the number of voters that have voted for `other candidate`. The second line starting with `Count` produces the number of voters that have voted for `candidate`.
The next section explains how eFLINT policy descriptions can be tested using scripts.

# Testing policy descriptions (under construction)

This section describes a language extension that makes it possible to test policy descriptions. The first step is to refine a policy description by restricting the set of possible instances of each of the user-defined types and by describing an initial state. If the refinement is such that the set of instances of each user-defined type is finite, then exploration of the ‘state-space’ becomes feasible as there will be a finite number of actions that can happen in each state. The prototype implementation of eFLINT has a mode for manual exploration, allowing the user to step through the state-space by choosing one of the (enabled) actions at each step. This section demonstrates scripts, however, for stepping through the state-space automatically and testing whether the policy description encodes the expected set of behaviors.

## Type refinement

The first step of the refinement process is restrict the user-defined types to admit a finite set of instances. The declarations of a policy description can be divided based on whether the type of a declaration is a product-type or a simple type (all the act and duty declarations are of the former kind). If the instances of types are considered as tree structures (or terms), then the instances of simple types form the leaves of these trees. This intuition demonstrates that if all simple types have a finite number of instances, all product-types have a finite number of instances (since every product-type is formed out a finite number of components). A sufficient refinement of the types is thus achieved by re-declaring the fact identifiers associated with simple types and associating them with ‘smaller’, finite types instead. For example, the following declarations assign a finite set of values to each of the fact identifiers assigned a simple type in the policy (and declared without a derivation function).


    Fact citizen       Identified by [John, Frank, Peter, Chloe]
    Fact candidate     Identified by [Mary, David]
    Fact administrator Identified by Admin

The declarations determine that only `Mary:candidate` and `David:candidate` are valid instances of `candidate` and that the only valid instances of `administrator` is `Admin:administrator` (and similar for `citizen).

## Initial state

The second step of the refinement process is describing an initial state. This is achieved by writing a sequence of statements of the form `<EXPR>.` (an expression followed by a period) or `(Foreach x1,…,xn : <EXPR>)`, where `<EXPR>` is an expression evaluating to an instance. Consider for example, the following sequence of statements:


    administrator. 
    citizen. 
    candidate.
    (Foreach declare winner : declare winner).
    (Foreach citizen : enable vote(Admin, citizen)).

Note that the first three lines are all expressions consisting of a reference to a single, unbound variable. For brevity, any unbound variables occurring in the expression of a statement are implicitly bound with `Foreach`. The following sequence of statements is equivalent to the above:


    (Foreach administrator : administrator). 
    (Foreach citizen : citizen). 
    (Foreach candidate : candidate).
    (Foreach administrator, citizen : declare winner()).
    enable vote(Admin, citizen).

The first four lines determine that every instance of `administrator`, `citizen`, `candidate` and `declare winner` holds true in the initial state. Thus the fourth line determines that any administrator has the power to declare any citizen as the winner, (under the conditions given by the pre-condition of the declaration of  `declare winner`). The fifth line determines that `Admin` can enable any citizen to vote.

## Scripts

A script is a sequence of action calls, event calls, and queries.

An action call is a statement of the form `!<EXPR>.` (an expression preceded by an exclamation mark and trailed by a period), with `<EXPR>` an expression evaluating to an instance of an act. Any unbound variables in the expression are bound by `Foreach` implicitly, as is also the case for the statements describing an initial state. However, the result of evaluating the expression should be a single instance of an act. The action call fails if the expression does not evaluate to a single instance of an act, or if this instance does not enable an action (its pre-condition does not hold true).

An event call is a statement of the form `+<EXPR>.` or `-<EXPR>.`, with `<EXPR>`  an expression evaluating to a single instance. The action call fails if the expression evaluates to more than one instance or to no instance at all. An action call prefixed by `+` inserts the instance to which `<EXPR>` evaluates, or fails if the instance is already in the current state. An action call prefixed by `-` removes the instance to which `<EXPR>` evaluates, or fails if the instance is not in the current state. The intuition behind events is that they simulate changes to the world which were not foreseen by the policy creators (e.g. a candidate withdrawing from an election) or which the policy deliberately does not cover (e.g. the loss of votes due to a natural disaster affecting a data-centre).

A query is a statement of the form `?<EXPR>.`, with  `<EXPR>` an expression evaluating to a single instance. The query fails if the expression does not evaluate to a single instance, or if it evaluates to a single instance that is not in the current state. A query that does not fail does nothing.


## Positive and negative tests

Scripts can be used to test expected behavior (through action calls) and expected effects (through event calls and queries).  The prototype implementation of eFLINT can run scripts in testing mode, reporting the first point of failure (if any). A successful test is thus executed silently. 

In software engineering it is good practice to also write tests that deliberately fail. In the case of testing policy, scripts can be written that test the absence of unexpected behavior and effects. To support this, the prototype implementation can run scripts in a negative testing mode, during which the first failure point is reported, exactly as in positive testing mode, unless the first failure point is the last statement of the script, in which case the test is accepted (and the failure is not reported). If the last statement succeeds, then this is reported as a violation of the test.

