# Assignment 1: Sequent Calculus Prover
### Hyunkyung Lee (s5432909)

This repository includes my implementation for Assignment 1 in 3806ICT Logic and Automated Reasoning. 
Based on Algorithm 2 from the course textbook(Hou, 2021), this project provides a baseline backward proof search prover for FOL as well as an improved version that makes use of memoization and loop detection. 

## Project Structure

```text

src/
  formula.py # term and formula representations 
  sequent.py # sequent representation
  parser.py # minimal parser for FOL syntax
  baseline.py # baseline prover based on Algorithm 2 (p.67)
  improved.py # improved prover with memoization and loop detection 
  generator.py # synthetic formula generator
  build_dataset.py # synthetic dataset builder
  pelletier.py # manually encoded Pelletier benchmark problems

tests/
  run_step1_experiment.py # custom test + Pelletier 1-17
  run_step2_experiment.py # synthetic benchmark experiment (genAI)
  run_step3_for_challenge_experiment.py # Pelletier 18-34 FOL challenge benchmark
  test_formulae.py # test formulae

data/
  synthetic_dataset.json
  step1_results.csv
  step2_results.csv
  ste3_fol_challenge_results_60s.csv
  step3_fol_challenge_results.csv

tptp/
  selected TPTP files used as references for manual Pelletier encoding
```

## Notes
The parser functions only as a partial version of a parser for TPTP; thus, it provides a project specific syntax for the current implementation. Selected Pelletier problems were manually encoded into internal formula representation.

The output not_provide indicats that the formula itself was not found to be semantically invalid but rather that the prover was unable to produce a proof using the search strategy as implemented within the limits of time and resource restrictions. 

The experiment outlined in step 3 was conducted over a maximum of 60 seconds per formula due to the use of Pelletier's problem 18 through 34 as the more challenging benchmark for establishing the first-order challenge benchmark 



