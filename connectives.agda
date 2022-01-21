module connectives where
open import Agda.Primitive
postulate True : Set
postulate False : Set
postulate Not : Set -> Set
postulate And : Set -> Set -> Set
postulate Or : Set -> Set -> Set
postulate ex : (A : Set) -> (A -> Set) -> Set
postulate equal : {i : Level} → (A : Set i) -> A -> A -> Set i
postulate I : True
postulate falsity : {i : Level} → forall (t : Set i) -> False -> t
postulate nmk : forall (A : Set) -> (A -> False) -> Not A
postulate Not::ind : forall (A : Set) -> forall (Q : Set) -> ((A -> False) -> Q) -> (Not A) -> Q
postulate conj : forall (A : Set) -> forall (B : Set) -> A -> B -> And A B
postulate match::And::prop : forall (A : Set) -> forall (B : Set) -> forall (return : Set) -> (A -> B -> return) -> (And A B) -> return
postulate or::introl : forall (A : Set) -> forall (B : Set) -> A -> Or A B
postulate or::intror : forall (A : Set) -> forall (B : Set) -> B -> Or A B
postulate match::Or::prop : forall (A : Set) -> forall (B : Set) -> forall (return : Set) -> (A -> return) -> (B -> return) -> (Or A B) -> return
postulate ex::intro : (A : Set) -> forall (P : (A -> Set)) -> forall (x : A) -> (P x) -> ex (A) P
postulate match::ex::prop : (A : Set) -> forall (P : (A -> Set)) -> forall (return : Set) -> (forall (x : A) -> (P x) -> return) -> (ex (A) P) -> return
postulate refl::equal : {i : Level} → (A : Set i) -> forall (x : A) -> equal (A) x x
postulate equal::leibniz : {i j : Level} → (A : Set i) -> forall (x : A) -> forall (y : A) -> (equal (A) x y) -> forall (P : (A -> Set j)) -> (P x) -> P y
