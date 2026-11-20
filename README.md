# tc6001-trs

The present work develops a Prolog program that, given a formula $P$, and an adequate set of rewrite rules, converts $P$ into its clausal normal form (CNF). The output of this program is $L$, a list of pairs of the form $\langle i, C_i \rangle$, where $i$ is the clause identifier, and $C_i$ is the corresponding clause.

Developed by Juan José H. Beltrán.

## Repository structure

```text
tc6001-trs/
├── main.pl             # Prolog implementation of formula normalization and CNF conversion
├── README.md           # Project overview and usage instructions
├── report.pdf          # Project report
└── test/
    ├── tests.pl        # PLUnit test suite
    ├── propositions.txt # Example propositional formulas
    ├── normalize.txt   # Normalization examples
    └── cnf.txt         # CNF conversion examples
```

## Run

This program requires a Prolog installation on the system. SWIPL 11.0.0 was used for development.

To run the set of tests run the following command in a terminal placed on the root folder of the repository.

```{bash}
swipl -g run_tests -t halt test/tests.pl 
```

If you want to test the program by yourself, you can load the main.pl file and make queries using `formula2cnf(P,L)`. An example is shown below. More examples can be found in the `tests/___.txt` files of the repository.

```{bash}
swipl main.pl
formula2cnf((p \/ p \/ q) /\ (q \/ p), L).
```

