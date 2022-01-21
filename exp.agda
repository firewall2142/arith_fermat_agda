module exp where
open import Agda.Primitive
open import connectives
open import leibniz
open import nat
postulate exp : nat.nat -> nat.nat -> nat.nat
postulate exp::body : nat.nat -> nat.nat -> nat.nat
postulate axiom::exp : forall (n : nat.nat) -> forall (m : nat.nat) -> connectives.equal (nat.nat) (exp n m) (nat.filter::nat::type (nat.nat) (exp::body n) m)
eq::exp : _
eq::exp = \(n : nat.nat) -> \(m : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (exp n m)) (nat.filter::nat::type (nat.nat) (exp::body n) m)) (((axiom::exp) (n)) (m))

sym::eq::exp : _
sym::eq::exp = \(n : nat.nat) -> \(m : nat.nat) -> ((((leibniz.sym::leibniz) (nat.nat)) (exp n m)) (nat.filter::nat::type (nat.nat) (exp::body n) m)) (((eq::exp) (n)) (m))

postulate axiom::exp::body::O : forall (n : nat.nat) -> connectives.equal (nat.nat) (exp::body n nat.O) (nat.S nat.O)
eq::exp::body::O : _
eq::exp::body::O = \(n : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (exp::body n nat.O)) (nat.S nat.O)) ((axiom::exp::body::O) (n))

sym::eq::exp::body::O : _
sym::eq::exp::body::O = \(n : nat.nat) -> ((((leibniz.sym::leibniz) (nat.nat)) (exp::body n nat.O)) (nat.S nat.O)) ((eq::exp::body::O) (n))

postulate axiom::exp::body::S : forall (n : nat.nat) -> forall (m : nat.nat) -> connectives.equal (nat.nat) (exp::body n (nat.S m)) (nat.times (exp n m) n)
eq::exp::body::S : _
eq::exp::body::S = \(n : nat.nat) -> \(m : nat.nat) -> ((((connectives.equal::leibniz) (nat.nat)) (exp::body n (nat.S m))) (nat.times (exp n m) n)) (((axiom::exp::body::S) (n)) (m))

sym::eq::exp::body::S : _
sym::eq::exp::body::S = \(n : nat.nat) -> \(m : nat.nat) -> ((((leibniz.sym::leibniz) (nat.nat)) (exp::body n (nat.S m))) (nat.times (exp n m) n)) (((eq::exp::body::S) (n)) (m))

lt::O::exp : _
lt::O::exp = \(n : nat.nat) -> \(m : nat.nat) -> ((((nat.nat::ind) (\(::x::365 : nat.nat) -> (nat.lt nat.O n) -> nat.lt nat.O (exp n ::x::365))) (((((sym::eq::exp) (n)) (nat.O)) (\(y : nat.nat) -> (nat.lt nat.O n) -> nat.lt nat.O y)) (((((nat.sym::eq::filter::nat::type::O) (nat.nat)) (exp::body n)) (\(y : nat.nat) -> (nat.lt nat.O n) -> nat.lt nat.O y)) ((((sym::eq::exp::body::O) (n)) (\(y : nat.nat) -> (nat.lt nat.O n) -> nat.lt nat.O y)) (\(auto : nat.le (nat.S nat.O) n) -> ((nat.lt::O::S) (nat.O))))))) (\(a : nat.nat) -> ((((sym::eq::exp) (n)) (nat.S a)) (\(y : nat.nat) -> ((nat.lt nat.O n) -> nat.lt nat.O (exp n a)) -> (nat.lt nat.O n) -> nat.lt nat.O y)) ((((((nat.sym::eq::filter::nat::type::S) (nat.nat)) (exp::body n)) (a)) (\(y : nat.nat) -> ((nat.lt nat.O n) -> nat.lt nat.O (exp n a)) -> (nat.lt nat.O n) -> nat.lt nat.O y)) (((((sym::eq::exp::body::S) (n)) (a)) (\(y : nat.nat) -> ((nat.lt nat.O n) -> nat.lt nat.O (exp n a)) -> (nat.lt nat.O n) -> nat.lt nat.O y)) (\(Hind : (nat.le (nat.S nat.O) n) -> nat.le (nat.S nat.O) (exp n a)) -> (\(posn : nat.le (nat.S nat.O) n) -> (((nat.eq::times::body::O) (\(y : (nat.nat -> nat.nat)) -> nat.le (nat.S (y (nat.S nat.O))) (nat.times (exp n a) n))) (((((nat.eq::filter::nat::type::O) (nat.nat -> nat.nat)) (nat.times::body)) (\(y : (nat.nat -> nat.nat)) -> nat.le (nat.S (y (nat.S nat.O))) (nat.times (exp n a) n))) ((((nat.eq::times) (nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (nat.S (y (nat.S nat.O))) (nat.times (exp n a) n))) (((nat.eq::plus::body::O) (\(y : (nat.nat -> nat.nat)) -> nat.le (nat.S (y (nat.times nat.O (nat.S nat.O)))) (nat.times (exp n a) n))) (((((nat.eq::filter::nat::type::O) (nat.nat -> nat.nat)) (nat.plus::body)) (\(y : (nat.nat -> nat.nat)) -> nat.le (nat.S (y (nat.times nat.O (nat.S nat.O)))) (nat.times (exp n a) n))) ((((nat.eq::plus) (nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (nat.S (y (nat.times nat.O (nat.S nat.O)))) (nat.times (exp n a) n))) ((((nat.eq::plus::body::S) (nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (y (nat.times nat.O (nat.S nat.O))) (nat.times (exp n a) n))) ((((((nat.eq::filter::nat::type::S) (nat.nat -> nat.nat)) (nat.plus::body)) (nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (y (nat.times nat.O (nat.S nat.O))) (nat.times (exp n a) n))) ((((nat.eq::plus) (nat.S nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (y (nat.times nat.O (nat.S nat.O))) (nat.times (exp n a) n))) ((((nat.eq::times::body::S) (nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (y (nat.S nat.O)) (nat.times (exp n a) n))) ((((((nat.eq::filter::nat::type::S) (nat.nat -> nat.nat)) (nat.times::body)) (nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (y (nat.S nat.O)) (nat.times (exp n a) n))) ((((nat.eq::times) (nat.S nat.O)) (\(y : (nat.nat -> nat.nat)) -> nat.le (y (nat.S nat.O)) (nat.times (exp n a) n))) (((((((nat.le::times) (nat.S nat.O)) (exp n a)) (nat.S nat.O)) (n)) ((Hind) (posn))) (posn)))))))))))))))))))) (m)

