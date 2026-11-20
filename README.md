# tc6001-trs


## Run

```{bash}
swipl main.pl
formula2cnf((p \/ p \/ q) /\ (q \/ p), L).
```

```{bash}
swipl -g run_tests -t halt test/tests.pl 
```

