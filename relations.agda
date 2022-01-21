module relations where
open import Agda.Primitive
open import connectives
open import logic
reflexive : _
reflexive = \(A : Set) -> \(R : (A -> A -> Set)) -> forall (x : A) -> R x x

transitive : _
transitive = \(A : Set) -> \(R : (A -> A -> Set)) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> (R x y) -> (R y z) -> R x z

RC : _
RC = \(A : Set) -> \(R : (A -> A -> Set)) -> \(x : A) -> \(y : A) -> connectives.Or (R x y) (logic.eq (A) x y)

RC::reflexive : _
RC::reflexive = \(A : Set) -> \(R : A -> A -> Set) -> \(x : A) -> (((connectives.or::intror) (R x x)) (logic.eq (A) x x)) (((logic.refl) (A)) (x))

injective:: : _
injective:: = \(A : Set) -> \(B : Set) -> \(f : (A -> B)) -> forall (x : A) -> forall (y : A) -> (logic.eq (B) (f x) (f y)) -> logic.eq (A) x y

commutative : _
commutative = \(A : Set) -> \(f : (A -> A -> A)) -> forall (x : A) -> forall (y : A) -> logic.eq (A) (f x y) (f y x)

associative : _
associative = \(A : Set) -> \(f : (A -> A -> A)) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> logic.eq (A) (f (f x y) z) (f x (f y z))

monotonic : _
monotonic = \(A : Set) -> \(R : (A -> A -> Set)) -> \(f : (A -> A)) -> forall (x : A) -> forall (y : A) -> (R x y) -> R (f x) (f y)

distributive : _
distributive = \(A : Set) -> \(f : (A -> A -> A)) -> \(g : (A -> A -> A)) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> logic.eq (A) (f x (g y z)) (g (f x y) (f x z))

