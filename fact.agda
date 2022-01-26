module fact where
open import Agda.Primitive
import connectives
import nat
postulate fact : nat.nat -> nat.nat
postulate fact::body : nat.nat -> nat.nat
postulate axiom::fact : forall (n : nat.nat) -> connectives.equal (nat.nat) (fact n) (nat.filter::nat::type (nat.nat) fact::body n)
eq::fact : forall (n : nat.nat) -> forall (P : (nat.nat -> Set)) -> (P (fact n)) -> P (nat.filter::nat::type (nat.nat) fact::body n)
eq::fact = \(n : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (fact n)) (nat.filter::nat::type (nat.nat) fact::body n)) ((axiom::fact) (n))

sym::eq::fact : forall (n : nat.nat) -> forall (P : (nat.nat -> Set)) -> (P (nat.filter::nat::type (nat.nat) fact::body n)) -> P (fact n)
sym::eq::fact = \(n : nat.nat) -> \(P : nat.nat -> Set) -> \(H : P (nat.filter::nat::type (nat.nat) fact::body n)) -> (((((eq::fact) (n)) (\(a : nat.nat) -> (P a) -> P (fact n))) (\(px : P (fact n)) -> (px))) (H))

postulate axiom::fact::body::O : connectives.equal (nat.nat) (fact::body nat.O) (nat.S nat.O)
eq::fact::body::O : forall (P : (nat.nat -> Set)) -> (P (fact::body nat.O)) -> P (nat.S nat.O)
eq::fact::body::O = ((((connectives.equal::leibniz) (nat.nat)) (fact::body nat.O)) (nat.S nat.O)) (axiom::fact::body::O)

sym::eq::fact::body::O : forall (P : (nat.nat -> Set)) -> (P (nat.S nat.O)) -> P (fact::body nat.O)
sym::eq::fact::body::O = \(P : nat.nat -> Set) -> \(H : P (nat.S nat.O)) -> ((((eq::fact::body::O) (\(a : nat.nat) -> (P a) -> P (fact::body nat.O))) (\(px : P (fact::body nat.O)) -> (px))) (H))

postulate axiom::fact::body::S : forall (n : nat.nat) -> connectives.equal (nat.nat) (fact::body (nat.S n)) (nat.times (fact n) (nat.S n))
eq::fact::body::S : forall (n : nat.nat) -> forall (P : (nat.nat -> Set)) -> (P (fact::body (nat.S n))) -> P (nat.times (fact n) (nat.S n))
eq::fact::body::S = \(n : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (fact::body (nat.S n))) (nat.times (fact n) (nat.S n))) ((axiom::fact::body::S) (n))

sym::eq::fact::body::S : forall (n : nat.nat) -> forall (P : (nat.nat -> Set)) -> (P (nat.times (fact n) (nat.S n))) -> P (fact::body (nat.S n))
sym::eq::fact::body::S = \(n : nat.nat) -> \(P : nat.nat -> Set) -> \(H : P (nat.times (fact n) (nat.S n))) -> (((((eq::fact::body::S) (n)) (\(a : nat.nat) -> (P a) -> P (fact::body (nat.S n)))) (\(px : P (fact::body (nat.S n))) -> (px))) (H))

