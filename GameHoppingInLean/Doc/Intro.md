# Intruduction: how to write cryptographic proof using game-hopping.

Generally, to use this library follow this steps:
1. Formulate the crpyotgraphic statment you want to prove as indisitnguishibility (ind for short) statement. In particular, you should define two oracle implementations that no adversary can disitnguish with eah other.
  Also formlate all used assumptions as inditinguishibility assumptions (thay have the same form as above: a pair of oracle implementations).
  You could find more info on how to define oracle implementations in [GameHoppingInLean/Examples/Doc/OracleImplementatin.md](OracleImplementatin.md).
3. Formulate the proof as sequence of hybrids. We will be proving that each two conseutive hybris are ind.
  For each pair of hybrids they should be either:
  * identicil behaviorally -- they have the same distribuition of outputs ofr any sequence of queries. Proofs of indistinguishability are usually carriad via abstration technique. More detail could be find in [ObservationalEquivalence](ObservationalEquivalence.md).
  * the should correspond to reduction step. The hybrid on the left should have syntactic form of Reduction r applyied to left side of assumption X. The hybrid on the right should be equal to the same reduction but applied to the right side of assumption X (the same assumption). For more details about how to define reductions see [](Reductions.md).
4. Finally your proof is done using game_hopping tactic. More info on how to use it is provided in TODO.