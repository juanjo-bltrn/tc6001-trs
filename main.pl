/* Logic operators are represented using this Prolog terms
* Negation ¬
* And /\
* Or \/
* Logical Implication ->
* Logical Equivalence <->
*/
:- op(600, xfy, <->).
:- op(575, xfy, ->).
:- op(550, xfy, \/).
:- op(525, xfy, /\).
:- op(500, fy, ¬).


/*
* proposionp(+Term) takes a prolog term, +Term,
* and returns true iff +Term is a well-formed formula.
*/
propositionp(P) :- constantp(P), !.
propositionp(¬P) :- !, propositionp(P).
propositionp(P) :-
    P =.. [Op,P1,P2],
    binaryOperatorp(Op),
    propositionp(P1),
    propositionp(P2).