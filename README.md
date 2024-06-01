Important files

* `qset.rkt` defines quorumsets, slices, network configurations, etc. and functions to manipulate them, as well as a fast, incomplete quorum-intersection check.
* `truth-tables.rkt` defines the truth tables of the 3-valued logic that we call 3vl.
* `characteristic-fmla.rkt` defines a procedure that takes a network configuration (mapping each node to its slices) and produces a formula in 3vl that is valid if and only if quorum-intersection holds.
* `3to2.rkt` defines a translation from 3vl to standard propositional logic.
* `rosette-sat.rkt` uses Rosette to obtain a 3vl solver by symbolically executing the 3vl truth tables, and a propositional solver that just forwards formulas to Z3 (no symbolic execution involved)
* `stellarbeat.rkt` provides procedure to download Stellar's current network configuration from https://stellarbeat.io
* `intersection-checker.rkt` ties everything together to obtain and provides a command-line interface
* `3vl-tests.rkt` contain tests for the 3vl logic

In practice, I suspect that the fast check defined in `qset.rkt` will be sufficient.
