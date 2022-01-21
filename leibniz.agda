module leibniz where
open import Agda.Primitive
leibniz : {i j : Level} → _
leibniz {i} {j} = \(A : Set i) -> \(x : A) -> \(y : A) -> forall (P : (A -> Set j)) -> (P x) -> P y

refl::leibniz : {i j : Level} → _
refl::leibniz  {i} {j} = \(A : Set i) -> \(x : A) -> \(P : A -> Set j) -> \(H : P x) -> (H)

postulate sym::leibniz : {i j : Level} → (A : Set i) -> forall (x : A) -> forall (y : A) -> (leibniz {_} {j} (A) x y) -> leibniz {_} {j} (A) y x
