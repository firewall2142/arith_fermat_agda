module primes where
open import Agda.Primitive
import bool
import connectives
import div::mod
import logic
import nat
import relations
postulate divides : nat.nat -> nat.nat -> Set
postulate quotient : forall (n : nat.nat) -> forall (m : nat.nat) -> forall (q : nat.nat) -> (logic.eq (nat.nat) m (nat.times n q)) -> divides n m
postulate match::divides::prop : forall (n : nat.nat) -> forall (m : nat.nat) -> forall (return::type : Set) -> (forall (q : nat.nat) -> (logic.eq (nat.nat) m (nat.times n q)) -> return::type) -> (divides n m) -> return::type
reflexive::divides : relations.reflexive (nat.nat) divides
reflexive::divides = \(x : nat.nat) -> ((((quotient) (x)) (x)) (nat.S nat.O)) (((((((logic.rewrite::r) (nat.nat)) (nat.times x (nat.S nat.O))) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.times x (nat.S nat.O)))) (((logic.refl) (nat.nat)) (nat.times x (nat.S nat.O)))) (x)) ((nat.times::n::1) (x)))

divides::to::div::mod::spec : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O n) -> (divides n m) -> div::mod.div::mod::spec m n (div::mod.div m n) nat.O
divides::to::div::mod::spec = \(n : nat.nat) -> \(m : nat.nat) -> \(posn : nat.lt nat.O n) -> (\(::clearme : divides n m) -> ((((((match::divides::prop) (n)) (m)) (div::mod.div::mod::spec m n (div::mod.div m n) nat.O)) (\(q : nat.nat) -> \(eqm : logic.eq (nat.nat) m (nat.times n q)) -> (((((((div::mod.div::mod::spec::intro) (m)) (n)) (div::mod.div m n)) (nat.O)) (posn)) (((((((logic.eq::ind::r) (nat.nat)) (nat.times n q)) (\(x : nat.nat) -> logic.eq (nat.nat) x (nat.plus (nat.times (div::mod.div x n) n) nat.O))) (((((((logic.eq::ind::r) (nat.nat)) (nat.times q n)) (\(x : nat.nat) -> logic.eq (nat.nat) x (nat.plus (nat.times (div::mod.div x n) n) nat.O))) (((((((logic.eq::ind::r) (nat.nat)) (q)) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.times q n) (nat.plus (nat.times x n) nat.O))) (((((((logic.rewrite::r) (nat.nat)) (nat.times n q)) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.plus (nat.times q n) nat.O))) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.plus (nat.times q n) nat.O))) (((((((logic.rewrite::r) (nat.nat)) (nat.times n q)) (\(:::: : nat.nat) -> logic.eq (nat.nat) m (nat.plus :::: nat.O))) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (nat.nat) m (nat.plus :::: nat.O))) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (nat.nat) m ::::)) (((logic.refl) (nat.nat)) (m))) (nat.plus m nat.O)) ((nat.plus::n::O) (m)))) (nat.times n q)) (eqm))) (nat.times q n)) (((nat.commutative::times) (q)) (n)))) (nat.times n q)) (eqm))) (nat.times q n)) (((nat.commutative::times) (q)) (n)))) (div::mod.div (nat.times q n) n)) ((((div::mod.div::times) (q)) (n)) (posn)))) (nat.times n q)) (((nat.commutative::times) (n)) (q)))) (m)) (eqm))))) (::clearme)))

divides::to::mod::O : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O n) -> (divides n m) -> logic.eq (nat.nat) (div::mod.mod m n) nat.O
divides::to::mod::O = \(n : nat.nat) -> \(m : nat.nat) -> \(posn : nat.lt nat.O n) -> (\(divnm : divides n m) -> (((((((((div::mod.div::mod::spec::to::eq2) (m)) (n)) (div::mod.div m n)) (div::mod.mod m n)) (div::mod.div m n)) (nat.O)) ((((div::mod.div::mod::spec::div::mod) (m)) (n)) (posn))) (((((divides::to::div::mod::spec) (n)) (m)) (posn)) (divnm))))

mod::O::to::divides : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O n) -> (logic.eq (nat.nat) (div::mod.mod m n) nat.O) -> divides n m
mod::O::to::divides = \(n : nat.nat) -> \(m : nat.nat) -> \(auto : nat.lt nat.O n) -> (\(auto' : logic.eq (nat.nat) (div::mod.mod m n) nat.O) -> (((((quotient) (n)) (m)) (div::mod.div m n)) (((((((logic.rewrite::l) (nat.nat)) (nat.times n (div::mod.div m n))) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.times n (div::mod.div m n)))) (((logic.refl) (nat.nat)) (nat.times n (div::mod.div m n)))) (m)) (((((((logic.rewrite::r) (nat.nat)) (nat.minus m nat.O)) (\(:::: : nat.nat) -> logic.eq (nat.nat) (nat.times n (div::mod.div m n)) ::::)) (((((((logic.rewrite::l) (nat.nat)) (div::mod.mod m n)) (\(:::: : nat.nat) -> logic.eq (nat.nat) (nat.times n (div::mod.div m n)) (nat.minus m ::::))) (((((((logic.rewrite::l) (nat.nat)) (nat.times (div::mod.div m n) n)) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.minus m (div::mod.mod m n)))) (((div::mod.eq::times::div::minus::mod) (m)) (n))) (nat.times n (div::mod.div m n))) (((nat.commutative::times) (div::mod.div m n)) (n)))) (nat.O)) (auto'))) (m)) ((nat.minus::n::O) (m))))))

divides::n::O : forall (n : nat.nat) -> divides n nat.O
divides::n::O = \(n : nat.nat) -> ((((quotient) (n)) (nat.O)) (nat.O)) (((((((logic.rewrite::r) (nat.nat)) (nat.times n nat.O)) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.times n nat.O))) (((logic.refl) (nat.nat)) (nat.times n nat.O))) (nat.O)) ((nat.times::n::O) (n)))

divides::n::n : forall (n : nat.nat) -> divides n n
divides::n::n = \(n : nat.nat) -> (reflexive::divides) (n)

eq::mod::to::divides : forall (n : nat.nat) -> forall (m : nat.nat) -> forall (q : nat.nat) -> (nat.lt nat.O q) -> (logic.eq (nat.nat) (div::mod.mod n q) (div::mod.mod m q)) -> divides q (nat.minus n m)
eq::mod::to::divides = \(n : nat.nat) -> \(m : nat.nat) -> \(q : nat.nat) -> \(posq : nat.lt nat.O q) -> (\(eqmod : logic.eq (nat.nat) (div::mod.mod n q) (div::mod.mod m q)) -> ((((((nat.leb::elim) (n)) (m)) (\(:::: : bool.bool) -> divides q (nat.minus n m))) (\(nm : nat.le n m) -> (((((logic.eq::coerc) (divides q nat.O)) (divides q (nat.minus n m))) ((divides::n::O) (q))) (((((((logic.rewrite::r) (nat.nat)) (nat.O)) (\(:::: : nat.nat) -> logic.eq (Set) (divides q nat.O) (divides q ::::))) (((logic.refl) (Set)) (divides q nat.O))) (nat.minus n m)) (((((logic.sym::eq) (nat.nat)) (nat.O)) (nat.minus n m)) (((((logic.eq::coerc) (logic.eq (nat.nat) (nat.minus nat.O (nat.minus m n)) (nat.minus (nat.plus nat.O n) m))) (logic.eq (nat.nat) nat.O (nat.minus n m))) (((((nat.minus::le::minus::minus::comm) (m)) (n)) (nat.O)) (nm))) (((((((logic.rewrite::l) (nat.nat)) (nat.O)) (\(:::: : nat.nat) -> logic.eq (Set) (logic.eq (nat.nat) :::: (nat.minus (nat.plus nat.O n) m)) (logic.eq (nat.nat) nat.O (nat.minus n m)))) (((((((logic.rewrite::l) (nat.nat)) (n)) (\(:::: : nat.nat) -> logic.eq (Set) (logic.eq (nat.nat) nat.O (nat.minus :::: m)) (logic.eq (nat.nat) nat.O (nat.minus n m)))) (((logic.refl) (Set)) (logic.eq (nat.nat) nat.O (nat.minus n m)))) (nat.plus nat.O n)) ((nat.plus::O::n) (n)))) (nat.minus nat.O (nat.minus m n))) ((nat.minus::O::n) (nat.minus m n))))))))) (\(nm : connectives.Not (nat.le n m)) -> (((((quotient) (q)) (nat.minus n m)) (nat.minus (div::mod.div n q) (div::mod.div m q))) (((((((logic.eq::ind::r) (nat.nat)) (nat.minus (nat.times q (div::mod.div n q)) (nat.times q (div::mod.div m q)))) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) x)) (((((((logic.eq::ind::r) (nat.nat)) (nat.times (div::mod.div n q) q)) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) (nat.minus x (nat.times q (div::mod.div m q))))) (((((((logic.eq::ind::r) (nat.nat)) (nat.times (div::mod.div m q) q)) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) (nat.minus (nat.times (div::mod.div n q) q) x))) (((((((logic.eq::ind::r) (nat.nat)) (nat.minus n (div::mod.mod n q))) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) (nat.minus x (nat.times (div::mod.div m q) q)))) (((((((logic.eq::ind::r) (nat.nat)) (nat.minus n (nat.plus (div::mod.mod n q) (nat.times (div::mod.div m q) q)))) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) x)) (((((((logic.eq::ind::r) (nat.nat)) (div::mod.mod m q)) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) (nat.minus n (nat.plus x (nat.times (div::mod.div m q) q))))) (((((((logic.eq::ind::r) (nat.nat)) (nat.plus (nat.times (div::mod.div m q) q) (div::mod.mod m q))) (\(x : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) (nat.minus n x))) (((((((logic.eq::ind) (nat.nat)) (m)) (\(x::1 : nat.nat) -> logic.eq (nat.nat) (nat.minus n m) (nat.minus n x::1))) (((logic.refl) (nat.nat)) (nat.minus n m))) (nat.plus (nat.times (div::mod.div m q) q) (div::mod.mod m q))) (((div::mod.div::mod) (m)) (q)))) (nat.plus (div::mod.mod m q) (nat.times (div::mod.div m q) q))) (((nat.commutative::plus) (div::mod.mod m q)) (nat.times (div::mod.div m q) q)))) (div::mod.mod n q)) (eqmod))) (nat.minus (nat.minus n (div::mod.mod n q)) (nat.times (div::mod.div m q) q))) ((((nat.minus::plus) (n)) (div::mod.mod n q)) (nat.times (div::mod.div m q) q)))) (nat.times (div::mod.div n q) q)) (((((((logic.rewrite::r) (nat.nat)) (nat.times q (div::mod.div n q))) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.minus n (div::mod.mod n q)))) (((((((logic.rewrite::l) (nat.nat)) (nat.times q (div::mod.div n q))) (\(:::: : nat.nat) -> logic.eq (nat.nat) (nat.times q (div::mod.div n q)) ::::)) (((logic.refl) (nat.nat)) (nat.times q (div::mod.div n q)))) (nat.minus n (div::mod.mod n q))) (((((((logic.rewrite::l) (nat.nat)) (nat.times (div::mod.div n q) q)) (\(:::: : nat.nat) -> logic.eq (nat.nat) :::: (nat.minus n (div::mod.mod n q)))) (((div::mod.eq::times::div::minus::mod) (n)) (q))) (nat.times q (div::mod.div n q))) (((nat.commutative::times) (div::mod.div n q)) (q))))) (nat.times (div::mod.div n q) q)) (((nat.commutative::times) (div::mod.div n q)) (q))))) (nat.times q (div::mod.div m q))) (((nat.commutative::times) (q)) (div::mod.div m q)))) (nat.times q (div::mod.div n q))) (((nat.commutative::times) (q)) (div::mod.div n q)))) (nat.times q (nat.minus (div::mod.div n q) (div::mod.div m q)))) ((((nat.distributive::times::minus) (q)) (div::mod.div n q)) (div::mod.div m q)))))))

let::clause::1531 : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O m) -> (divides n m) -> forall (d : nat.nat) -> (logic.eq (nat.nat) m (nat.times n nat.O)) -> logic.eq (nat.nat) m nat.O
let::clause::1531 = \(n : nat.nat) -> \(m : nat.nat) -> \(posm : nat.lt nat.O m) -> (\(::clearme : divides n m) -> (\(d : nat.nat) -> \(eqm : logic.eq (nat.nat) m (nat.times n nat.O)) -> (((((((logic.rewrite::r) (nat.nat)) (nat.times n nat.O)) (\(:::: : nat.nat) -> logic.eq (nat.nat) m ::::)) (eqm)) (nat.O)) ((nat.times::n::O) (n)))))

let::clause::15311 : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O m) -> (divides n m) -> forall (d : nat.nat) -> forall (p : nat.nat) -> (logic.eq (nat.nat) m (nat.times n (nat.S p))) -> logic.eq (nat.nat) m (nat.plus n (nat.times n p))
let::clause::15311 = \(n : nat.nat) -> \(m : nat.nat) -> \(posm : nat.lt nat.O m) -> (\(::clearme : divides n m) -> (\(d : nat.nat) -> \(p : nat.nat) -> \(eqm : logic.eq (nat.nat) m (nat.times n (nat.S p))) -> (((((((logic.rewrite::r) (nat.nat)) (nat.times n (nat.S p))) (\(:::: : nat.nat) -> logic.eq (nat.nat) m ::::)) (eqm)) (nat.plus n (nat.times n p))) (((nat.times::n::Sm) (n)) (p)))))

divides::to::le : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O m) -> (divides n m) -> nat.le n m
divides::to::le = \(n : nat.nat) -> \(m : nat.nat) -> \(posm : nat.lt nat.O m) -> (\(::clearme : divides n m) -> ((((((match::divides::prop) (n)) (m)) (nat.le n m)) (\(d : nat.nat) -> ((((nat.match::nat::prop) (\(:::: : nat.nat) -> (logic.eq (nat.nat) m (nat.times n ::::)) -> nat.le n m)) (\(eqm : logic.eq (nat.nat) m (nat.times n nat.O)) -> (((connectives.falsity) (nat.le n m)) ((((logic.absurd) (nat.le (nat.S m) nat.O)) (((((logic.eq::coerc) (nat.le (nat.S nat.O) m)) (nat.le (nat.S m) nat.O)) (posm)) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (Set) (nat.le (nat.S ::::) m) (nat.le (nat.S m) nat.O))) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (Set) (nat.le (nat.S m) m) (nat.le (nat.S m) ::::))) (((logic.refl) (Set)) (nat.le (nat.S m) m))) (nat.O)) (((((((let::clause::1531) (n)) (m)) (posm)) (::clearme)) (d)) (eqm)))) (nat.O)) (((((((let::clause::1531) (n)) (m)) (posm)) (::clearme)) (d)) (eqm))))) ((nat.not::le::Sn::O) (m)))))) (\(p : nat.nat) -> \(eqm : logic.eq (nat.nat) m (nat.times n (nat.S p))) -> (((((((logic.eq::ind::r) (nat.nat)) (nat.times n (nat.S p))) (\(x : nat.nat) -> nat.le n x)) (((((logic.eq::coerc) (nat.le n (nat.plus n (nat.times n p)))) (nat.le n (nat.times n (nat.S p)))) (((nat.le::plus::n::r) (nat.times n p)) (n))) (((((((logic.rewrite::l) (nat.nat)) (nat.plus n (nat.times n p))) (\(:::: : nat.nat) -> logic.eq (Set) (nat.le n (nat.plus n (nat.times n p))) (nat.le n ::::))) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (Set) (nat.le n (nat.plus n (nat.times n p))) (nat.le n ::::))) (((((((logic.rewrite::l) (nat.nat)) (m)) (\(:::: : nat.nat) -> logic.eq (Set) (nat.le n ::::) (nat.le n m))) (((logic.refl) (Set)) (nat.le n m))) (nat.plus n (nat.times n p))) ((((((((let::clause::15311) (n)) (m)) (posm)) (::clearme)) (d)) (p)) (eqm)))) (nat.plus n (nat.times n p))) ((((((((let::clause::15311) (n)) (m)) (posm)) (::clearme)) (d)) (p)) (eqm)))) (nat.times n (nat.S p))) (((nat.times::n::Sm) (n)) (p))))) (m)) (eqm)))) (d))) (::clearme)))

dividesb : nat.nat -> nat.nat -> bool.bool
dividesb = \(n : nat.nat) -> \(m : nat.nat) -> nat.eqb (div::mod.mod m n) nat.O

dividesb::true::to::divides : forall (n : nat.nat) -> forall (m : nat.nat) -> (logic.eq (bool.bool) (dividesb n m) bool.true) -> divides n m
dividesb::true::to::divides = \(n : nat.nat) -> \(m : nat.nat) -> ((((((connectives.match::Or::prop) (nat.lt nat.O n)) (logic.eq (nat.nat) nat.O n)) ((logic.eq (bool.bool) (dividesb n m) bool.true) -> divides n m)) (\(posn : nat.lt nat.O n) -> (\(divbnm : logic.eq (bool.bool) (dividesb n m) bool.true) -> (((((mod::O::to::divides) (n)) (m)) (posn)) ((((nat.eqb::true::to::eq) (div::mod.mod m n)) (nat.O)) (divbnm)))))) (\(eqnO : logic.eq (nat.nat) nat.O n) -> (((((((logic.eq::ind) (nat.nat)) (nat.O)) (\(x::1 : nat.nat) -> (logic.eq (bool.bool) (dividesb x::1 m) bool.true) -> divides x::1 m)) ((((((nat.sym::eq::match::nat::type::O) (nat.nat)) (m)) (\(p : nat.nat) -> div::mod.mod::aux m m p)) (\(y : nat.nat) -> (logic.eq (bool.bool) (nat.eqb y nat.O) bool.true) -> divides nat.O m)) (\(eqbmO : logic.eq (bool.bool) (nat.eqb m nat.O) bool.true) -> (((((((logic.eq::ind::r) (nat.nat)) (nat.O)) (\(x : nat.nat) -> divides nat.O x)) ((divides::n::n) (nat.O))) (m)) ((((nat.eqb::true::to::eq) (m)) (nat.O)) (eqbmO)))))) (n)) (eqnO)))) ((((nat.le::to::or::lt::eq) (nat.O)) (n)) ((nat.le::O::n) (n)))

dividesb::false::to::not::divides : forall (n : nat.nat) -> forall (m : nat.nat) -> (logic.eq (bool.bool) (dividesb n m) bool.false) -> connectives.Not (divides n m)
dividesb::false::to::not::divides = \(n : nat.nat) -> \(m : nat.nat) -> ((((((connectives.match::Or::prop) (nat.lt nat.O n)) (logic.eq (nat.nat) nat.O n)) ((logic.eq (bool.bool) (dividesb n m) bool.false) -> connectives.Not (divides n m))) (\(posn : nat.lt nat.O n) -> (\(ndivbnm : logic.eq (bool.bool) (dividesb n m) bool.false) -> (((((logic.not::to::not) (divides n m)) (logic.eq (nat.nat) (div::mod.mod m n) nat.O)) ((((divides::to::mod::O) (n)) (m)) (posn))) ((((nat.eqb::false::to::not::eq) (div::mod.mod m n)) (nat.O)) (ndivbnm)))))) (\(eqnO : logic.eq (nat.nat) nat.O n) -> (((((((logic.eq::ind) (nat.nat)) (nat.O)) (\(x::1 : nat.nat) -> (logic.eq (bool.bool) (dividesb x::1 m) bool.false) -> connectives.Not (divides x::1 m))) ((((((nat.sym::eq::match::nat::type::O) (nat.nat)) (m)) (\(p : nat.nat) -> div::mod.mod::aux m m p)) (\(y : nat.nat) -> (logic.eq (bool.bool) (nat.eqb y nat.O) bool.false) -> connectives.Not (divides nat.O m))) (((((nat.nat::case) (m)) (\(:::: : nat.nat) -> (logic.eq (bool.bool) (nat.eqb :::: nat.O) bool.false) -> connectives.Not (divides nat.O ::::))) ((((nat.sym::eq::eqb) (nat.O)) (\(y : (nat.nat -> bool.bool)) -> (logic.eq (nat.nat) m nat.O) -> (logic.eq (bool.bool) (y nat.O) bool.false) -> connectives.Not (divides nat.O nat.O))) (((((nat.sym::eq::filter::nat::type::O) (nat.nat -> bool.bool)) (nat.eqb::body)) (\(y : (nat.nat -> bool.bool)) -> (logic.eq (nat.nat) m nat.O) -> (logic.eq (bool.bool) (y nat.O) bool.false) -> connectives.Not (divides nat.O nat.O))) (((nat.sym::eq::eqb::body::O) (\(y : (nat.nat -> bool.bool)) -> (logic.eq (nat.nat) m nat.O) -> (logic.eq (bool.bool) (y nat.O) bool.false) -> connectives.Not (divides nat.O nat.O))) ((((((nat.sym::eq::match::nat::type::O) (bool.bool)) (bool.true)) (\(q : nat.nat) -> bool.false)) (\(y : bool.bool) -> (logic.eq (nat.nat) m nat.O) -> (logic.eq (bool.bool) y bool.false) -> connectives.Not (divides nat.O nat.O))) (\(auto : logic.eq (nat.nat) m nat.O) -> (\(auto' : logic.eq (bool.bool) bool.true bool.false) -> (((((logic.not::to::not) (divides nat.O nat.O)) (logic.eq (bool.bool) bool.true bool.false)) (\(auto'' : divides nat.O nat.O) -> (((((((logic.rewrite::l) (bool.bool)) (bool.true)) (\(:::: : bool.bool) -> logic.eq (bool.bool) bool.true ::::)) (((logic.refl) (bool.bool)) (bool.true))) (bool.false)) (auto')))) (bool.not::eq::true::false))))))))) (\(a : nat.nat) -> \(:::: : logic.eq (nat.nat) m (nat.S a)) -> (\(::0 : logic.eq (bool.bool) (nat.eqb (nat.S a) nat.O) bool.false) -> (((connectives.nmk) (divides nat.O (nat.S a))) (\(::clearme : divides nat.O (nat.S a)) -> ((((((match::divides::prop) (nat.O)) (nat.S a)) (connectives.False)) (\(q : nat.nat) -> \(auto : logic.eq (nat.nat) (nat.S a) (nat.times nat.O q)) -> ((((logic.absurd) (logic.eq (nat.nat) nat.O (nat.S a))) (((((((logic.rewrite::r) (nat.nat)) (n)) (\(::::1 : nat.nat) -> logic.eq (nat.nat) ::::1 (nat.S a))) (((((((logic.rewrite::l) (nat.nat)) (nat.S a)) (\(::::1 : nat.nat) -> logic.eq (nat.nat) ::::1 (nat.S a))) (((logic.refl) (nat.nat)) (nat.S a))) (n)) (((((((logic.rewrite::l) (nat.nat)) (nat.O)) (\(::::1 : nat.nat) -> logic.eq (nat.nat) (nat.S a) ::::1)) (((((((logic.rewrite::r) (nat.nat)) (nat.times q nat.O)) (\(::::1 : nat.nat) -> logic.eq (nat.nat) (nat.S a) ::::1)) (((((((logic.rewrite::l) (nat.nat)) (nat.times nat.O q)) (\(::::1 : nat.nat) -> logic.eq (nat.nat) (nat.S a) ::::1)) (auto)) (nat.times q nat.O)) (((nat.commutative::times) (nat.O)) (q)))) (nat.O)) ((nat.times::n::O) (q)))) (n)) (eqnO)))) (nat.O)) (eqnO))) ((nat.not::eq::O::S) (a))))) (::clearme))))))))) (n)) (eqnO)))) ((((nat.le::to::or::lt::eq) (nat.O)) (n)) ((nat.le::O::n) (n)))

decidable::divides : forall (n : nat.nat) -> forall (m : nat.nat) -> logic.decidable (divides n m)
decidable::divides = \(n : nat.nat) -> \(m : nat.nat) -> ((((((connectives.match::Or::prop) (logic.eq (bool.bool) (dividesb n m) bool.true)) (logic.eq (bool.bool) (dividesb n m) bool.false)) (logic.decidable (divides n m))) (\(auto : logic.eq (bool.bool) (dividesb n m) bool.true) -> ((((connectives.or::introl) (divides n m)) (connectives.Not (divides n m))) ((((dividesb::true::to::divides) (n)) (m)) (((((((logic.rewrite::r) (bool.bool)) (bool.true)) (\(:::: : bool.bool) -> logic.eq (bool.bool) :::: bool.true)) (((logic.refl) (bool.bool)) (bool.true))) (dividesb n m)) (auto)))))) (\(auto : logic.eq (bool.bool) (dividesb n m) bool.false) -> ((((connectives.or::intror) (divides n m)) (connectives.Not (divides n m))) ((((dividesb::false::to::not::divides) (n)) (m)) (((((((logic.rewrite::r) (bool.bool)) (bool.false)) (\(:::: : bool.bool) -> logic.eq (bool.bool) :::: bool.false)) (((logic.refl) (bool.bool)) (bool.false))) (dividesb n m)) (auto)))))) ((bool.true::or::false) (dividesb n m))

divides::to::dividesb::true : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O n) -> (divides n m) -> logic.eq (bool.bool) (dividesb n m) bool.true
divides::to::dividesb::true = \(n : nat.nat) -> \(m : nat.nat) -> \(posn : nat.lt nat.O n) -> (\(divnm : divides n m) -> (((((((connectives.match::Or::prop) (logic.eq (bool.bool) (dividesb n m) bool.true)) (logic.eq (bool.bool) (dividesb n m) bool.false)) (logic.eq (bool.bool) (dividesb n m) bool.true)) (\(auto : logic.eq (bool.bool) (dividesb n m) bool.true) -> (((((((logic.rewrite::r) (bool.bool)) (bool.true)) (\(:::: : bool.bool) -> logic.eq (bool.bool) :::: bool.true)) (((logic.refl) (bool.bool)) (bool.true))) (dividesb n m)) (auto)))) (\(ndivbnm : logic.eq (bool.bool) (dividesb n m) bool.false) -> (((connectives.falsity) (logic.eq (bool.bool) (dividesb n m) bool.true)) ((((logic.absurd) (divides n m)) (divnm)) ((((dividesb::false::to::not::divides) (n)) (m)) (((((((logic.rewrite::r) (bool.bool)) (bool.false)) (\(:::: : bool.bool) -> logic.eq (bool.bool) :::: bool.false)) (((logic.refl) (bool.bool)) (bool.false))) (dividesb n m)) (ndivbnm))))))) ((bool.true::or::false) (dividesb n m))))

not::divides::to::dividesb::false : forall (n : nat.nat) -> forall (m : nat.nat) -> (nat.lt nat.O n) -> (connectives.Not (divides n m)) -> logic.eq (bool.bool) (dividesb n m) bool.false
not::divides::to::dividesb::false = \(n : nat.nat) -> \(m : nat.nat) -> \(posn : nat.lt nat.O n) -> (((((((connectives.match::Or::prop) (logic.eq (bool.bool) (dividesb n m) bool.true)) (logic.eq (bool.bool) (dividesb n m) bool.false)) ((connectives.Not (divides n m)) -> logic.eq (bool.bool) (dividesb n m) bool.false)) (\(divbnm : logic.eq (bool.bool) (dividesb n m) bool.true) -> (\(ndivnm : connectives.Not (divides n m)) -> (((connectives.falsity) (logic.eq (bool.bool) (dividesb n m) bool.false)) ((((logic.absurd) (divides n m)) ((((dividesb::true::to::divides) (n)) (m)) (((((((logic.rewrite::r) (bool.bool)) (bool.true)) (\(:::: : bool.bool) -> logic.eq (bool.bool) :::: bool.true)) (((logic.refl) (bool.bool)) (bool.true))) (dividesb n m)) (divbnm)))) (ndivnm)))))) (\(auto : logic.eq (bool.bool) (dividesb n m) bool.false) -> (\(auto' : connectives.Not (divides n m)) -> (((((((logic.rewrite::r) (bool.bool)) (bool.false)) (\(:::: : bool.bool) -> logic.eq (bool.bool) :::: bool.false)) (((logic.refl) (bool.bool)) (bool.false))) (dividesb n m)) (auto))))) ((bool.true::or::false) (dividesb n m)))

prime : nat.nat -> Set
prime = \(n : nat.nat) -> connectives.And (nat.lt (nat.S nat.O) n) (forall (m : nat.nat) -> (divides m n) -> (nat.lt (nat.S nat.O) m) -> logic.eq (nat.nat) m n)

prime::to::lt::O : forall (p : nat.nat) -> (prime p) -> nat.lt nat.O p
prime::to::lt::O = \(p : nat.nat) -> \(::clearme : prime p) -> ((((((connectives.match::And::prop) (nat.lt (nat.S nat.O) p)) (forall (m : nat.nat) -> (divides m p) -> (nat.lt (nat.S nat.O) m) -> logic.eq (nat.nat) m p)) (nat.lt nat.O p)) (\(lt1p : nat.lt (nat.S nat.O) p) -> (\(auto : forall (m : nat.nat) -> (divides m p) -> (nat.lt (nat.S nat.O) m) -> logic.eq (nat.nat) m p) -> ((((nat.lt::S::to::lt) (nat.O)) (p)) (lt1p))))) (::clearme))

prime::to::lt::SO : forall (p : nat.nat) -> (prime p) -> nat.lt (nat.S nat.O) p
prime::to::lt::SO = \(p : nat.nat) -> \(::clearme : prime p) -> ((((((connectives.match::And::prop) (nat.lt (nat.S nat.O) p)) (forall (m : nat.nat) -> (divides m p) -> (nat.lt (nat.S nat.O) m) -> logic.eq (nat.nat) m p)) (nat.lt (nat.S nat.O) p)) (\(lt1p : nat.lt (nat.S nat.O) p) -> (\(auto : forall (m : nat.nat) -> (divides m p) -> (nat.lt (nat.S nat.O) m) -> logic.eq (nat.nat) m p) -> (lt1p)))) (::clearme))
