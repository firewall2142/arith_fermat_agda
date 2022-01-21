module connectives where
open import Agda.Primitive
data True : Set where
  I : True

data False : Set where


data Not : Set -> Set where
  nmk : (A : Set) -> (A -> False) -> Not A

data And : Set -> Set -> Set where
  conj : (A : Set) -> (B : Set) -> A -> B -> And A B

data Or : Set -> Set -> Set where
  or::introl : (A : Set) -> (B : Set) -> A -> Or A B
  or::intror : (A : Set) -> (B : Set) -> B -> Or A B

data ex : (A : Set) -> (A -> Set) -> Set where
  ex::intro : (A : Set) -> (P : (A -> Set)) -> (x : A) -> (P x) -> ex (A) P

data equal {i : Level} : (A : Set i) -> A -> A -> Set i where
  refl::equal : (A : Set i) -> (x : A) -> equal A x x

postulate falsity : {i : Level} → (t : Set i) -> False -> t

postulate Not::ind : (A : Set) -> (Q : Set) -> ((A -> False) -> Q) -> (Not A) -> Q
postulate match::And::prop : (A : Set) -> (B : Set) -> (return : Set) -> (A -> B -> return) -> (And A B) -> return
postulate match::Or::prop : (A : Set) -> (B : Set) -> (return : Set) -> (A -> return) -> (B -> return) -> (Or A B) -> return
postulate match::ex::prop : (A : Set) -> (P : (A -> Set)) -> (return : Set) -> ((x : A) -> (P x) -> return) -> (ex (A) P) -> return
postulate equal::leibniz : {i j : Level} → (A : Set i) -> (x : A) -> (y : A) -> (equal (A) x y) -> (P : (A -> Set j)) -> (P x) -> P y
