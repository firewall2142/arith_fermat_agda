module fact where
open import Agda.Primitive
open import connectives
open import leibniz
open import nat
postulate fact : nat.nat -> nat.nat
postulate fact::body : nat.nat -> nat.nat
postulate axiom::fact : forall (n : nat.nat) -> connectives.equal (nat.nat) (fact n) (nat.filter::nat::type (nat.nat) fact::body n)
eq::fact : _
eq::fact = \(n : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (fact n)) (nat.filter::nat::type (nat.nat) fact::body n)) ((axiom::fact) (n))

sym::eq::fact : _
sym::eq::fact = \(n : nat.nat) -> ((((leibniz.sym::leibniz) (nat.nat)) (fact n)) (nat.filter::nat::type (nat.nat) fact::body n)) ((eq::fact) (n))

postulate axiom::fact::body::O : connectives.equal (nat.nat) (fact::body nat.O) (nat.S nat.O)
eq::fact::body::O : _
eq::fact::body::O = ((((connectives.equal::leibniz) (nat.nat)) (fact::body nat.O)) (nat.S nat.O)) (axiom::fact::body::O)

sym::eq::fact::body::O : _
sym::eq::fact::body::O = ((((leibniz.sym::leibniz) (nat.nat)) (fact::body nat.O)) (nat.S nat.O)) (eq::fact::body::O)

postulate axiom::fact::body::S : forall (n : nat.nat) -> connectives.equal (nat.nat) (fact::body (nat.S n)) (nat.times (fact n) (nat.S n))
eq::fact::body::S : _
eq::fact::body::S = \(n : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (fact::body (nat.S n))) (nat.times (fact n) (nat.S n))) ((axiom::fact::body::S) (n))

sym::eq::fact::body::S : _
sym::eq::fact::body::S = \(n : nat.nat) -> ((((leibniz.sym::leibniz) (nat.nat)) (fact::body (nat.S n))) (nat.times (fact n) (nat.S n))) ((eq::fact::body::S) (n))

