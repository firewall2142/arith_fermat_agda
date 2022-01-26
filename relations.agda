module relations where
open import Agda.Primitive
import connectives
import logic
reflexive : (A : Set) -> (A -> A -> Set) -> Set
reflexive = \(A : Set) -> \(R : (A -> A -> Set)) -> forall (x : A) -> R x x

transitive : (A : Set) -> (A -> A -> Set) -> Set
transitive = \(A : Set) -> \(R : (A -> A -> Set)) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> (R x y) -> (R y z) -> R x z

RC : (A : Set) -> (A -> A -> Set) -> A -> A -> Set
RC = \(A : Set) -> \(R : (A -> A -> Set)) -> \(x : A) -> \(y : A) -> connectives.Or (R x y) (logic.eq (A) x y)

RC::reflexive : (A : Set) -> forall (R : (A -> A -> Set)) -> reflexive (A) (RC (A) R)
RC::reflexive = \(A : Set) -> \(R : A -> A -> Set) -> \(x : A) -> (((connectives.or::intror) (R x x)) (logic.eq (A) x x)) (((logic.refl) (A)) (x))

injective:: : (A : Set) -> (B : Set) -> (A -> B) -> Set
injective:: = \(A : Set) -> \(B : Set) -> \(f : (A -> B)) -> forall (x : A) -> forall (y : A) -> (logic.eq (B) (f x) (f y)) -> logic.eq (A) x y

commutative : (A : Set) -> (A -> A -> A) -> Set
commutative = \(A : Set) -> \(f : (A -> A -> A)) -> forall (x : A) -> forall (y : A) -> logic.eq (A) (f x y) (f y x)

associative : (A : Set) -> (A -> A -> A) -> Set
associative = \(A : Set) -> \(f : (A -> A -> A)) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> logic.eq (A) (f (f x y) z) (f x (f y z))

monotonic : (A : Set) -> (A -> A -> Set) -> (A -> A) -> Set
monotonic = \(A : Set) -> \(R : (A -> A -> Set)) -> \(f : (A -> A)) -> forall (x : A) -> forall (y : A) -> (R x y) -> R (f x) (f y)

distributive : (A : Set) -> (A -> A -> A) -> (A -> A -> A) -> Set
distributive = \(A : Set) -> \(f : (A -> A -> A)) -> \(g : (A -> A -> A)) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> logic.eq (A) (f x (g y z)) (g (f x y) (f x z))

