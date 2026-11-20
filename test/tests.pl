:- use_module(library(plunit)). % Test framework.
:- ensure_loaded('../main'). % Load the main file.

%% Truth-table check: P and the clause list L agree under every assignment.
cnf_equivalent(P, L) :-
    atoms_in(P, As),
    forall(assignment(As, V),
           (  holds(P, V),        clauses_hold(L, V)
           ;  \+ holds(P, V),     \+ clauses_hold(L, V)
           )).

% All atoms in P are collected into a sorted list As.
atoms_in(P, [P]) :- constantp(P), !.
atoms_in(¬P, As) :- !, atoms_in(P, As).
atoms_in(P, As) :-
    P =.. [_, A, B],
    atoms_in(A, As1), atoms_in(B, As2),
    append(As1, As2, As0), sort(As0, As).

% Produces all assignments of truth values to the atoms in As.
assignment([], []).
assignment([A|As], [A-T|Vs]) :- member(T, [true,false]), assignment(As, Vs).

% Truth values of formulas under a given assignment V.
holds(P, V)      :- constantp(P), !, memberchk(P-true, V).
holds(¬P, V)     :- !, \+ holds(P, V).
holds(A /\ B, V) :- !, holds(A, V), holds(B, V).
holds(A \/ B, V) :- !, ( holds(A, V) ; holds(B, V) ).
holds(A -> B, V) :- !, ( \+ holds(A, V) ; holds(B, V) ).
holds(A <-> B, V):- !, ( holds(A, V), holds(B, V)
                       ; \+ holds(A, V), \+ holds(B, V) ).

/* clauses_hold(+L, +V)
 * True iff the clause set L is true under the truth assignment V.*/
clauses_hold(L, V) :-
    forall(member(_-C, L), ( member(Lit, C), lit_holds(Lit, V) )).

% Truth values of literals under a given assignment V.
lit_holds(¬A, V) :- !, memberchk(A-false, V).
lit_holds(A, V)  :- memberchk(A-true, V).



% Checks if the CNF conversion of P gives the expected list of clauses.
check(P, Expected) :-
    formula2cnf(P, L),
    assertion(L == Expected),          % observed = expected
    assertion(cnf_equivalent(P, L)).   % semantically equivalent

:- begin_tests(formula2cnf).

% Some basic tests for the CNF conversion.
% The expected results are given as lists of Id-Clause pairs.
test(atom)         :- check(p,               [1-[p]]).
test(negated_atom) :- check(¬ p,             [1-[¬p]]).
test(implication)  :- check(p -> q,          [1-[q,¬p]]).
test(equivalence)  :- check(p <-> q,         [1-[p,¬q], 2-[q,¬p]]).
test(nested_neg)   :- check(¬ ¬ p,           [1-[p]]).
test(distribution) :- check((p /\ q) \/ r,   [1-[p,r], 2-[q,r]]).
test(tautology)    :- check(p \/ ¬ p,        []).
test(contradiction):- check(p /\ ¬ p,        [1-[p], 2-[¬p]]).

% Extra tests
test(mixed)        :- check((a -> b) -> c,   [1-[a,c], 2-[c,¬b]]).
test(duplicates)   :- check((p \/ p \/ q) /\ (q \/ p), [1-[p,q]]).
test(reject_term, [fail]) :- formula2cnf(p + q, _).
test(reject_var,  [fail]) :- formula2cnf(p /\ _, _).

:- end_tests(formula2cnf).