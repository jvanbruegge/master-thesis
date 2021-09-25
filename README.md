# Binding aware data types for Isabelle/HOL (master's thesis)

The latest PDF of the thesis can be viewed [here](https://github.com/jvanbruegge/master-thesis/releases/download/thesis/thesis.pdf).

## Roadmap

It is not clear how far on this roadmap I will get

- [x] Create a function that converts a BNF (regular Isabelle data type) to a MRBNF (binding aware datatype)
    - This is needed for the definition of MRBNFs by composition

- [ ] Implement the definition of MRBNFs by composition
    - Already described in the roshard bachelor thesis, but not implemented
    - Recursively go over the data type, converting BNFs (like sum and product) to MRBNFs on the fly, resulting in a true new MRBNF
    - Reuse the MRBNF composition from the bachelor thesis here
    - This datatype is **not** recursive yet, it is the _pre_ data type

- [ ] Implement the MRBNF fixpoint operation
    - Take the MRBNF (with the extra variables for the recursion) from step 2 and create the fixpoint equation
    - This removes the extra variables and returns a proper recursive data type

- [ ] Figure out what to do about induction and recursive function, as well as variable for variable and variable for term substitution
