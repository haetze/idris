module EsumOsum

data State : Type where 
  Esum : State 
  Osum : State
  
delta : Nat -> State -> State
delta Z     Osum = Osum
delta (S Z) Osum = Esum
delta Z     Esum = Esum
delta (S Z) Esum = Osum
delta (S (S n)) state = delta n state

delta_minus_one : Nat -> State -> State 
delta_minus_one = delta

data Word : Nat -> State -> (Nat -> State -> State) -> Type where 
            Eps  : Word Z Esum EsumOsum.delta 
            Cons : (x : Nat) -> Word n state f -> Word (S n) (f x state) f 

data AccRun : Nat -> State -> State -> (Nat -> State -> State) -> Type where
            Final     : (s : State) -> AccRun Z s s EsumOsum.delta_minus_one
            BackStep  : (w : Nat) -> AccRun n q_0 q_n f -> AccRun (S n) (f w q_0) q_n f

h : Word n state EsumOsum.delta ->AccRun n state Esum EsumOsum.delta_minus_one
h Eps = Final Esum
h (Cons w ws) = BackStep w $ h ws


equal : (x : Nat) -> (state: State) -> EsumOsum.delta_minus_one x state = EsumOsum.delta x state
equal x state = Refl


