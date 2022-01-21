module fact where
open import Agda.Primitive
open import connectives
open import leibniz
open import nat
postulate fact : nat.nat -> nat.nat
postulate fact::body : nat.nat -> nat.nat
postulate axiom::fact : forall (n : nat.nat) -> connectives.equal (nat.nat) (fact n) (nat.filter::nat::type (nat.nat) fact::body n)
eq::fact : {j : Level} -> _
eq::fact {j} = \(n : nat.nat) -> ((((connectives.equal::leibniz {_} {j}) (nat.nat)) (fact n)) (nat.filter::nat::type (nat.nat) fact::body n)) ((axiom::fact) (n))

sym::eq::fact : {j : Level} -> _
sym::eq::fact {j} = \(n : nat.nat) -> ((((leibniz.sym::leibniz {_} {j}) (nat.nat)) (fact n)) (nat.filter::nat::type (nat.nat) fact::body n)) ((eq::fact) (n))

postulate axiom::fact::body::O : connectives.equal (nat.nat) (fact::body nat.O) (nat.S nat.O)
eq::fact::body::O : {j : Level} -> _
eq::fact::body::O {j} = ((((connectives.equal::leibniz {_} {j}) (nat.nat)) (fact::body nat.O)) (nat.S nat.O)) (axiom::fact::body::O)

sym::eq::fact::body::O : {j : Level} -> _
sym::eq::fact::body::O {j} = ((((leibniz.sym::leibniz {_} {j}) (nat.nat)) (fact::body nat.O)) (nat.S nat.O)) (eq::fact::body::O)

postulate axiom::fact::body::S : forall (n : nat.nat) -> connectives.equal (nat.nat) (fact::body (nat.S n)) (nat.times (fact n) (nat.S n))
eq::fact::body::S : {j : Level} -> _
eq::fact::body::S {j} = \(n : nat.nat) -> ((((connectives.equal::leibniz {_} {j}) (nat.nat)) (fact::body (nat.S n))) (nat.times (fact n) (nat.S n))) ((axiom::fact::body::S) (n))

sym::eq::fact::body::S : {j : Level} -> _
sym::eq::fact::body::S {j} = \(n : nat.nat) -> ((((leibniz.sym::leibniz {_} {j}) (nat.nat)) (fact::body (nat.S n))) (nat.times (fact n) (nat.S n))) ((eq::fact::body::S) (n))

