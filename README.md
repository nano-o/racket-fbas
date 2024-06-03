# racket-fbas

This repository contains a bunch of Racket code related to checking quorum-intersection and related properties in a federated byzantine agreement system.
What's important is mostly in `qset.rkt`.
The reduction to SAT is interesting but what's in `qset.rkt` should cover most cases.

## Description of some of the files

* `qset.rkt` defines quorumsets, slices, network configurations, etc. and functions to manipulate them, as well as a fast, incomplete quorum-intersection check and a conservative but quick to compute safety bound.
* `truth-tables.rkt` defines the truth tables of the 3-valued logic that we call 3vl.
* `characteristic-fmla.rkt` defines a procedure that takes a fbas and produces a formula in 3vl that is valid if and only if quorum-intersection holds.
* `3to2.rkt` defines a translation from 3vl to standard propositional logic.
* `rosette-sat.rkt` uses Rosette to obtain a 3vl solver by symbolically executing the 3vl truth tables, and a propositional solver that just forwards formulas to Z3 (no symbolic execution involved)
* `stellarbeat.rkt` provides procedure to download Stellar's current network configuration from https://stellarbeat.io
* `intersection-checker.rkt` ties everything together to provide a command-line interface
* `3vl-tests.rkt` contain tests for the 3vl logic
* `test-data/` contains some synthetic networks to try stuff on

In practice, I suspect that the fast check defined in `qset.rkt` will be sufficient.

## Running

* After installing racket, clone this repository and run `raco pkg install` in it.
* To run test: `ls *.rkt | xargs -I{} raco test -x {}`
* To check that the stellar network intertwined using the fast heuristic (with fallback to SAT): `racket intersection-checker.rkt --fast`
* Same check on a synthetic, asymmetric network with 16 orgs: `racket intersection-checker.rkt --fast test-data/almost_symmetric_network_16_orgs_delete_prob_factor_2.json`
* This one triggers the SAT fallback: `racket intersection-checker.rkt --fast test-data/almost_symmetric_network_16_orgs_delete_prob_factor_15.json` (it's a sparse network where intersection does not hold).
* To get a lower bound on the number of failures that the Stellar network can tolerate while remaining safe: `racket intersection-checker.rkt --safety-bound`
