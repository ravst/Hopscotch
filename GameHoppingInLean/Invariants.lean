import GameHoppingInLean.StatefulRandomOracle


def correctInvariant (O : RStateOracle I) (φ : O.stateType → Prop) : Prop := sorry

def withInvariant (O : RStateOracle I) (φ : O.stateType → Prop) : RStateOracle I where
  stateType := {s : O.stateType | φ s}
  initialState := sorry
  queries := sorry
