/* Term Rewriting Systems in Prolog
 * Juan José H. Beltrán (A00836747)
 * Ph.D. in Computer Sciences */

/* Logic operators are represented using this Prolog terms
* Negation (¬), And (/\), Or (\/), Logical Implication (->),
* and Logical Equivalence (<->) */
:- op(600, xfy, <->).
:- op(575, xfy, ->).
:- op(550, xfy, \/).
:- op(525, xfy, /\).
:- op(500, fy,  ¬).



% First of all, the implementation of the input verification...

/* binaryOperatorp(?Op): Op is one of the binary connectives. */
binaryOperatorp((<->)).
binaryOperatorp((->)).
binaryOperatorp((\/)).
binaryOperatorp((/\)).

/* constantp(+P): P is an atomic proposition (a propositional letter),
 * Numbers, compound terms, variables and [] are rejected. */
constantp(P) :-
    atom(P),
    P \== [],
    P \== (¬),
    \+ binaryOperatorp(P).

% If P is an unbound variable, then it is not a proposition.
propositionp(P) :- var(P), !, fail. 

/* propositionp(+Term): true iff Term is a well-formed formula. */
propositionp(P) :- constantp(P), !.
propositionp(¬P) :- !, propositionp(P).
propositionp(P) :-
    P =.. [Op,P1,P2],
    binaryOperatorp(Op),
    propositionp(P1),
    propositionp(P2).



% Now the implementation of the normalization to CNF, 
% using rewrite rules and term rewriting...

:- use_module(library(lists)). % For nth1/3, nth1/4, reverse/2

/* Rewrite rules are written rr(Type, Name, Lhs :=> Rhs, Conditions).
 * Conditions is a list of goals that must hold ([] = none). */
:- op(800, xfx, :=>). % Define a new operator for rewrite rules.

%% Phase 'pre': eliminate <-> and ->
rr(pre, double_implication, (A <-> B) :=> (A -> B) /\ (B -> A), []).
rr(pre, implication,        (A -> B)  :=> ¬A \/ B,              []).

%% Phase 'cnf': push negation inward, then distribute \/ over /\
rr(cnf, not,              ¬ ¬ A      :=> A,              []).
rr(cnf, de_morgan_and,    ¬ (A /\ B) :=> ¬A \/ ¬B,       []).
rr(cnf, de_morgan_or,     ¬ (A \/ B) :=> ¬A /\ ¬B,       []).
rr(cnf, distribute_left,  A \/ (B /\ C) :=> (A \/ B) /\ (A \/ C), []).
rr(cnf, distribute_right, (A /\ B) \/ C :=> (A \/ C) /\ (B \/ C), []).

/* exp_at(+Exp, ?Pos, ?SubExp)
* Expression Exp contains SubExp at position Pos. Positions are lists 
* of integers representing tree-coordinates in the syntax-tree of the
* expression, but in reverse order. Furthermore, coordinate 0 represents 
* the function symbol of an expression, thus:
* exp_at(f(g(2,x),3), [2,1], x) and exp_at(f(g(2,x),3), [0,1], g).
* The definition is extended by defining [] as the position of Exp in Exp. 
* exp_at/3 fails if Pos is an invalid position in Exp. */
exp_at(Exp, Pos, Sub) :- exp_at_(Exp, [], Pos, Sub).

exp_at_(Exp, Pos, Pos, Exp).
exp_at_(Exp, Acc, Pos, Sub) :-
    compound(Exp), % Verify that Exp is a compound term
    Exp =.. [F|Args], % Split into functor and arguments
    (  I = 0, Arg = F
    ;  nth1(I, Args, Arg) % Iterates through each argument in Args
    ),
    exp_at_(Arg, [I|Acc], Pos, Sub). % Recursively descends into the chosen Arg
    % and prepends its index I onto the accumulator.

/* replace(+Pos, +New, +Exp, -NewExp): NewExp is Exp with the subterm at
 * Pos replaced by New. Pos uses the same reverse-order convention. */
replace(Pos, New, Exp, NewExp) :-
    reverse(Pos, Path), % Outermost coordinate first
    replace_(Path, New, Exp, NewExp).

replace_([], New, _, New). % Base case
replace_([0|Is], New, Exp, NewExp) :-
    Exp =.. [F|Args],
    replace_(Is, New, F, NewF),
    NewExp =.. [NewF|Args].
replace_([I|Is], New, Exp, NewExp) :-
    I > 0,
    Exp =.. [F|Args],
    nth1(I, Args, Sub, Rest),
    replace_(Is, New, Sub, NewSub),
    nth1(I, NewArgs, NewSub, Rest),
    NewExp =.. [F|NewArgs].

/* rewrite_step(+Type, +Formula, -NewFormula): one rewrite using any rule
 * of the given Type, at any position. Fails if no rule applies. */
rewrite_step(Type, Formula, NewFormula) :-
    exp_at(Formula, Pos, SubExp),
    rr(Type, _Name, SubExp :=> NewExp, Conds),
    maplist(call, Conds),
    replace(Pos, NewExp, Formula, NewFormula).

/* normalise(+Type, +Formula, -Normal): rewrite until no rule of Type applies. */
normalise(Type, F, NF) :-
    rewrite_step(Type, F, F1), !,
    normalise(Type, F1, NF).
normalise(_, F, F).

/* normalise_cnf(+P, -CNF): validate P, then run phase pre, then phase cnf. */
normalise_cnf(P, CNF) :-
    propositionp(P), % Verify that P is a well-formed formula.
    normalise(pre, P, P1),
    normalise(cnf, P1, CNF).



% Finally, the implementation of the CNF conversion to a list of clauses...

/* formula2cnf(+P, -L): L is a list of Id-Clause pairs, the CNF of P.
 *
 * Representation conventions:
 *   literal : an atom p, or ¬p (negation applied only to an atom)
 *   clause  : a list of literals, read as their disjunction, e.g. [p, ¬q]
 *   pair    : Id-Clause, where Id is an integer 1..N, unique in the result
 *   L       : list of pairs, read as the conjunction of its clauses
 * Simplifications (without losing logical equivalence):
 *   - duplicate literals inside a clause are removed (and literals sorted)
 *   - tautological clauses (containing both p and ¬p) are removed
 *   - duplicate clauses are removed
 *   - subsumed clauses are NOT removed
 * Special cases:
 *   - L = []  : empty clause set, i.e. a tautology (true)
 *   - the empty clause [] cannot arise, since the language has no constants;
 *     a contradiction such as p /\ ¬p gives [1-[p], 2-[¬p]], which is
 *     unsatisfiable but is not collapsed to the empty clause.
 */
formula2cnf(P, L) :-
    normalise_cnf(P, CNF), % Does all the work of converting P to CNF.
    conjuncts(CNF, Conjs),
    maplist(clause_literals, Conjs, Clauses0),
    exclude(tautologyp, Clauses0, Clauses1), % Drops tautological clauses
    sort(Clauses1, Clauses), % Drops duplicate clauses
    number_clauses(Clauses, 1, L).

/* conjuncts(+CNF, -Cs): the clauses of a conjunction, as disjunction terms. */
conjuncts(A /\ B, Cs) :- !,
    conjuncts(A, Cs1),
    conjuncts(B, Cs2),
    append(Cs1, Cs2, Cs).
conjuncts(C, [C]).

/* disjuncts(+Clause, -Lits): the literals of a disjunction. */
disjuncts(A \/ B, Ls) :- !,
    disjuncts(A, Ls1),
    disjuncts(B, Ls2),
    append(Ls1, Ls2, Ls).
disjuncts(L, [L]).

/* clause_literals(+Disj, -Lits): literal list, sorted, no duplicates. */
clause_literals(Disj, Lits) :-
    disjuncts(Disj, Ls),
    sort(Ls, Lits).

/* tautologyp(+Clause): Clause contains some p together with ¬p. */
tautologyp(Clause) :-
    member(¬A, Clause),
    memberchk(A, Clause). % To just check if A is in Clause.

/* number_clauses(+Clauses, +N, -Pairs)
 * Pairs contain each clause paired with a unique integer id starting at N */
number_clauses([], _, []).
number_clauses([C|Cs], N, [N-C|Rest]) :-
    N1 is N + 1,
    number_clauses(Cs, N1, Rest).