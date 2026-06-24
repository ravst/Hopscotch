# Introduction: How to Write a Cryptographic Proof Using Game-Hopping

To use this library, follow these steps:

1. Formulate the cryptographic statement you want to prove as an indistinguishability (IND) statement. In particular, you should define two oracle implementations that no adversary can distinguish from each other.  
   Also formulate all assumptions as indistinguishability assumptions (they have the same form as above: a pair of oracle implementations).  
   You can find more information on how to define oracle implementations in [OracleImplementation.md](GameHoppingInLean/Examples/Doc/OracleImplementation.md).

2. Formulate the proof as a sequence of hybrids. We will prove that each two consecutive hybrids are IND.  
   For each pair of hybrids, one of the following should hold:

   - They are behaviorally identical: they induce the same distribution on outputs for any sequence of queries. Proofs of indistinguishability in this case are usually carried out via the abstraction technique. More details can be found in [ObservationalEquivalence.md](ObservationalEquivalence.md).
   - They correspond to a reduction step:  
     The hybrid on the left should have the syntactic form of a reduction `r` applied to the left side of an assumption `X`.  
     The hybrid on the right should be equal to the same reduction, but applied to the right side of the same assumption `X`.  
     For more details about how to define reductions, see [Reductions.md](Reductions.md).

3. Finally, complete your proof using the `game_hopping` tactic. More information on how to use it will be provided in TODO.