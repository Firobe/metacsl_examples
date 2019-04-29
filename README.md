# metacsl_examples
Examples of MetAcsl specification to support the TAP paper "Sail through your C
Code with MetAcsl: Specifying, Testing and Proving High-Level Properties"  

Each folder contains the following data relative to its case study:
- The correct implementation `name.c/h`,
- A file `test_suite.c` containing several tests of the implementation,
- A `mutants` folder containing number of mutants deriving from the correct
  implementation,
- A file `results.csv` containing the results of each analysis on each mutant (and what
  mutation has been applied for each mutant).
