module connectives where
open import Agda.Primitive
data True : Set where
  I : True

data False : Set where


data Not : Set -> Set where
  nmk : forall (A : Set) -> (A -> False) -> Not A

postulate And : Set -> Set -> Set

data Or (A : Set) (B : Set) : Set where
  or::introl : A -> Or A B
  or::intror : B -> Or A B

data ex : (A : Set) -> (A -> Set) -> Set where
  ex::intro : (A : Set) -> forall (P : (A -> Set)) -> forall (x : A) -> (P x) -> ex (A) P

data equal {i : Level} (A : Set i) (x : A) : A -> Set i where
  refl::equal : equal A x x

postulate falsity : {i : Level} → forall (t : Set i) -> False -> t

postulate Not::ind : forall (A : Set) -> forall (Q : Set) -> ((A -> False) -> Q) -> (Not A) -> Q
postulate conj : forall (A : Set) -> forall (B : Set) -> A -> B -> And A B
postulate match::And::prop : forall (A : Set) -> forall (B : Set) -> forall (return : Set) -> (A -> B -> return) -> (And A B) -> return
postulate match::Or::prop : forall (A : Set) -> forall (B : Set) -> forall (return : Set) -> (A -> return) -> (B -> return) -> (Or A B) -> return
postulate match::ex::prop : (A : Set) -> forall (P : (A -> Set)) -> forall (return : Set) -> (forall (x : A) -> (P x) -> return) -> (ex (A) P) -> return
postulate equal::leibniz : {i j : Level} → (A : Set i) -> forall (x : A) -> forall (y : A) -> (equal (A) x y) -> forall (P : (A -> Set j)) -> (P x) -> P y
