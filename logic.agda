module logic where
open import Agda.Primitive
import connectives
postulate eq : {i : Level} (A : Set i) -> A -> A -> Set i
postulate refl : {i : Level} (A : Set i) -> forall (x : A) -> eq (A) x x
postulate eq::ind : {i j : Level} (A : Set i) -> forall (x : A) -> forall (P : (A -> Set j)) -> (P x) -> forall (y : A) -> (eq (A) x y) -> P y
eq::rect::r : {i j : Level} (A : Set i) -> forall (a : A) -> forall (x : A) -> (eq (A) x a) -> forall (P : (A -> Set j)) -> (P a) -> P x
eq::rect::r {i} {j} = \(A : Set i) -> \(a : A) -> \(x : A) -> \(p : eq (A) x a) -> (((((((eq::ind) (A)) (x)) (\(:::: : A) -> forall (P : (A -> Set j)) -> (P ::::) -> P x)) (\(P : A -> Set j) -> \(auto : P x) -> (auto))) (a)) (p))

eq::ind::r : {i j : Level} (A : Set i) -> forall (a : A) -> forall (P : (A -> Set j)) -> (P a) -> forall (x : A) -> (eq (A) x a) -> P x
eq::ind::r {i} {j} = \(A : Set i) -> \(a : A) -> \(P : A -> Set j) -> \(p : P a) -> (\(x0 : A) -> \(p0 : eq (A) x0 a) -> (((((((eq::rect::r) (A)) (a)) (x0)) (p0)) (\(x01 : A) -> P x01)) (p)))

rewrite::l : {i j : Level} (A : Set i) -> forall (x : A) -> forall (P : (A -> Set j)) -> (P x) -> forall (y : A) -> (eq (A) x y) -> P y
rewrite::l {i} {j} = \(A : Set i) -> \(x : A) -> \(P : A -> Set j) -> \(Hx : P x) -> (\(y : A) -> \(Heq : eq (A) x y) -> (((((((eq::ind) (A)) (x)) (\(:::: : A) -> P ::::)) (Hx)) (y)) (Heq)))

sym::eq : {i : Level} (A : Set i) -> forall (x : A) -> forall (y : A) -> (eq (A) x y) -> eq (A) y x
sym::eq {i} = \(A : Set i) -> \(x : A) -> \(y : A) -> \(Heq : eq (A) x y) -> (((((((rewrite::l) (A)) (x)) (\(:::: : A) -> eq (A) :::: x)) (((refl) (A)) (x))) (y)) (((((((rewrite::l) (A)) (x)) (\(:::: : A) -> eq (A) x ::::)) (((refl) (A)) (x))) (y)) (Heq)))

rewrite::r : {i j : Level} (A : Set i) -> forall (x : A) -> forall (P : (A -> Set j)) -> (P x) -> forall (y : A) -> (eq (A) y x) -> P y
rewrite::r {i} {j} = \(A : Set i) -> \(x : A) -> \(P : A -> Set j) -> \(Hx : P x) -> (\(y : A) -> \(Heq : eq (A) y x) -> (((((((eq::ind) (A)) (x)) (\(:::: : A) -> P ::::)) (Hx)) (y)) (((((sym::eq) (A)) (y)) (x)) (Heq))))

eq::coerc : forall (A : Set) -> forall (B : Set) -> A -> (eq (Set) A B) -> B
eq::coerc = \(A : Set) -> \(B : Set) -> \(Ha : A) -> (\(Heq : eq (Set) A B) -> (((((((eq::ind) (Set)) (A)) (\(x::19 : Set) -> x::19)) (Ha)) (B)) (Heq)))

trans::eq : (A : Set) -> forall (x : A) -> forall (y : A) -> forall (z : A) -> (eq (A) x y) -> (eq (A) y z) -> eq (A) x z
trans::eq = \(A : Set) -> \(x : A) -> \(y : A) -> \(z : A) -> \(H1 : eq (A) x y) -> (\(H2 : eq (A) y z) -> (((((((eq::ind::r) (A)) (y)) (\(x0 : A) -> eq (A) x0 z)) (((((((rewrite::l) (A)) (x)) (\(:::: : A) -> eq (A) :::: z)) (((((((rewrite::l) (A)) (x)) (\(:::: : A) -> eq (A) x ::::)) (((refl) (A)) (x))) (z)) (((((((rewrite::r) (A)) (y)) (\(:::: : A) -> eq (A) :::: z)) (H2)) (x)) (H1)))) (y)) (H1))) (x)) (H1)))

eq::f : (A : Set) -> (B : Set) -> forall (f : (A -> B)) -> forall (x : A) -> forall (y : A) -> (eq (A) x y) -> eq (B) (f x) (f y)
eq::f = \(A : Set) -> \(B : Set) -> \(f : A -> B) -> \(x : A) -> \(y : A) -> \(H : eq (A) x y) -> (((((((eq::ind::r) (A)) (y)) (\(x0 : A) -> eq (B) (f x0) (f y))) (((((((rewrite::l) (A)) (x)) (\(:::: : A) -> eq (B) (f ::::) (f y))) (((((((rewrite::l) (A)) (x)) (\(:::: : A) -> eq (B) (f x) (f ::::))) (((refl) (B)) (f x))) (y)) (H))) (y)) (H))) (x)) (H))

eq::f2 : (A : Set) -> (B : Set) -> (C : Set) -> forall (f : (A -> B -> C)) -> forall (x1 : A) -> forall (x2 : A) -> forall (y1 : B) -> forall (y2 : B) -> (eq (A) x1 x2) -> (eq (B) y1 y2) -> eq (C) (f x1 y1) (f x2 y2)
eq::f2 = \(A : Set) -> \(B : Set) -> \(C : Set) -> \(f : A -> B -> C) -> \(x1 : A) -> \(x2 : A) -> \(y1 : B) -> \(y2 : B) -> \(E1 : eq (A) x1 x2) -> (\(E2 : eq (B) y1 y2) -> (((((((eq::ind::r) (A)) (x2)) (\(x : A) -> eq (C) (f x y1) (f x2 y2))) (((((((eq::ind::r) (B)) (y2)) (\(x : B) -> eq (C) (f x2 x) (f x2 y2))) (((((((rewrite::l) (A)) (x1)) (\(:::: : A) -> eq (C) (f :::: y2) (f x2 y2))) (((((((rewrite::l) (B)) (y1)) (\(:::: : B) -> eq (C) (f x1 ::::) (f x2 y2))) (((((((rewrite::l) (A)) (x1)) (\(:::: : A) -> eq (C) (f x1 y1) (f :::: y2))) (((((((rewrite::l) (B)) (y1)) (\(:::: : B) -> eq (C) (f x1 y1) (f x1 ::::))) (((refl) (C)) (f x1 y1))) (y2)) (E2))) (x2)) (E1))) (y2)) (E2))) (x2)) (E1))) (y1)) (E2))) (x1)) (E1)))

absurd : forall (A : Set) -> A -> (connectives.Not A) -> connectives.False
absurd = \(A : Set) -> \(H : A) -> (\(Hn : connectives.Not A) -> (((((connectives.Not::ind) (A)) (connectives.False)) (\(::x::80 : A -> connectives.False) -> ((::x::80) (H)))) (Hn)))

not::to::not : forall (A : Set) -> forall (B : Set) -> (A -> B) -> (connectives.Not B) -> connectives.Not A
not::to::not = \(A : Set) -> \(B : Set) -> \(auto : A -> B) -> (\(auto' : connectives.Not B) -> (((connectives.nmk) (A)) (\(auto'' : A) -> ((((absurd) (B)) ((auto) (auto''))) (auto')))))

sym::not::eq : (A : Set) -> forall (x : A) -> forall (y : A) -> (connectives.Not (eq (A) x y)) -> connectives.Not (eq (A) y x)
sym::not::eq = \(A : Set) -> \(x : A) -> \(y : A) -> \(auto : connectives.Not (eq (A) x y)) -> (((connectives.nmk) (eq (A) y x)) (\(auto' : eq (A) y x) -> ((((absurd) (eq (A) x y)) (((((((rewrite::r) (A)) (x)) (\(:::: : A) -> eq (A) x ::::)) (((refl) (A)) (x))) (y)) (auto'))) (auto))))

proj1 : forall (A : Set) -> forall (B : Set) -> (connectives.And A B) -> A
proj1 = \(A : Set) -> \(B : Set) -> \(AB : connectives.And A B) -> ((((((connectives.match::And::prop) (A)) (B)) (A)) (\(::x::120 : A) -> (\(::x::119 : B) -> (::x::120)))) (AB))

proj2 : forall (A : Set) -> forall (B : Set) -> (connectives.And A B) -> B
proj2 = \(A : Set) -> \(B : Set) -> \(AB : connectives.And A B) -> ((((((connectives.match::And::prop) (A)) (B)) (B)) (\(::x::120 : A) -> (\(::x::119 : B) -> (::x::119)))) (AB))

decidable : Set -> Set
decidable = \(A : Set) -> connectives.Or A (connectives.Not A)

