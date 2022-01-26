module bool where
open import Agda.Primitive
import connectives
import logic
import relations
data bool : Set where
postulate true : bool
postulate false : bool
postulate match::bool::prop : {i : Level} -> forall (return : (bool -> Set i)) -> (return true) -> (return false) -> forall (z : bool) -> return z
postulate match::bool::type : {i : Level} (return : Set i) -> return -> return -> bool -> return
postulate axiom::match::bool::type::true : {i : Level} (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> connectives.equal (return) (match::bool::type (return) case::true case::false true) case::true

eq::match::bool::type::true : {i j : Level} (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> forall (P : (return -> Set j)) -> (P (match::bool::type (return) case::true case::false true)) -> P case::true
eq::match::bool::type::true {i} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> ((((connectives.equal::leibniz) (return)) (match::bool::type (return) case::true case::false true)) (case::true)) ((((axiom::match::bool::type::true) (return)) (case::true)) (case::false))

postulate axiom::match::bool::type::false : {i : Level} -> (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> connectives.equal (return) (match::bool::type (return) case::true case::false false) case::false

eq::match::bool::type::false : {i j : Level} (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> forall (P : (return -> Set j)) -> (P (match::bool::type (return) case::true case::false false)) -> P case::false
eq::match::bool::type::false {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> ((((connectives.equal::leibniz) (return)) (match::bool::type (return) case::true case::false false)) (case::false)) ((((axiom::match::bool::type::false) (return)) (case::true)) (case::false))

sym::eq::match::bool::type::true : {i j : Level} (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> forall (P : (return -> Set j)) -> (P case::true) -> P (match::bool::type (return) case::true case::false true)
sym::eq::match::bool::type::true {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> \(P : return -> Set j) -> \(H : P case::true) -> ((((((((connectives.equal::leibniz) (return)) (match::bool::type (return) case::true case::false true)) (case::true)) ((((axiom::match::bool::type::true) (return)) (case::true)) (case::false))) (\(a : return) -> (P a) -> P (match::bool::type (return) case::true case::false true))) (\(px : P (match::bool::type (return) case::true case::false true)) -> (px))) (H))

sym::eq::match::bool::type::false : {i j : Level} (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> forall (P : (return -> Set j)) -> (P case::false) -> P (match::bool::type (return) case::true case::false false)
sym::eq::match::bool::type::false {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> \(P : return -> Set j) -> \(H : P case::false) -> ((((((((connectives.equal::leibniz) (return)) (match::bool::type (return) case::true case::false false)) (case::false)) ((((axiom::match::bool::type::false) (return)) (case::true)) (case::false))) (\(a : return) -> (P a) -> P (match::bool::type (return) case::true case::false false))) (\(px : P (match::bool::type (return) case::true case::false false)) -> (px))) (H))

bool::discr : _
--forall (x : bool) -> forall (y : bool) -> (logic.eq (bool) x y) -> match::bool::type (_) (match::bool::type (_) (forall (P : Set) -> P -> P) (forall (P : Set) -> P) y) (match::bool::type (_) (forall (P : _) -> P) (forall (P : _) -> P -> P) y) x
bool::discr = \(x : bool) -> \(y : bool) -> \(Deq : logic.eq (bool) x y) -> 
   logic.eq::ind bool x 
     (\(x::13 : bool) -> match::bool::type _ (match::bool::type _ (forall (P : Set) -> P -> P) (forall (P : Set) -> P) x::13) (match::bool::type _ (forall (P : Set) -> P) (forall (P : Set) -> P -> P) x::13) x) 
     ((match::bool::prop 
       (\(:::: : bool) -> match::bool::type _ (match::bool::type _ (forall (P : Set) -> P -> P) (forall (P : Set) -> P) ::::) (match::bool::type _ (forall (P : Set) -> P) (forall (P : Set) -> P -> P) ::::) ::::) 
       (sym::eq::match::bool::type::true 
         Set₁
         (match::bool::type Set₁ (forall (P : Set) -> P -> P) (forall (P : Set) -> P) true) 
         (match::bool::type Set₁ (forall (P : Set) -> P) (forall (P : Set) -> P -> P) true)
         (\ (x0 : Set₁) -> x0) 
         (sym::eq::match::bool::type::true 
           _ 
           (forall (P : Set) -> P -> P) 
           (forall (P : Set) -> P) 
           (\(x0 : Set₁) -> x0) 
           (\(P : Set) -> \(DH : P) -> DH))
        ) 

       ((((((sym::eq::match::bool::type::false) _) (match::bool::type _ (forall (P : Set) -> P -> P) (forall (P : Set) -> P) false)) (match::bool::type _ (forall (P : Set) -> P) (forall (P : Set) -> P -> P) false)) (\(x0 : Set₁) -> x0)) ((((((sym::eq::match::bool::type::false) _) (forall (P : Set) -> P)) (forall (P : Set) -> P -> P)) (\(x0 : Set₁) -> x0)) (\(P : Set) -> \(DH : P) -> (DH))))) x)
   y
   Deq

not::eq::true::false : connectives.Not (logic.eq (bool) true false)
not::eq::true::false = ((connectives.nmk) (logic.eq (bool) true false)) (\(Heq : logic.eq (bool) true false) -> ((((((((connectives.equal::leibniz) (_)) (match::bool::type (_) (forall (P : _) -> P -> P) (forall (P : _) -> P) false)) (forall (P : _) -> P)) ((((axiom::match::bool::type::false) (_)) (forall (P : _) -> P -> P)) (forall (P : _) -> P))) (\(x : _) -> x)) (((((((connectives.equal::leibniz) (_)) (match::bool::type (_) (match::bool::type (_) (forall (P : _) -> P -> P) (forall (P : _) -> P) false) (match::bool::type (_) (forall (P : _) -> P) (forall (P : _) -> P -> P) false) true)) (match::bool::type (_) (forall (P : _) -> P -> P) (forall (P : _) -> P) false)) ((((axiom::match::bool::type::true) (_)) (match::bool::type (_) (forall (P : _) -> P -> P) (forall (P : _) -> P) false)) (match::bool::type (_) (forall (P : _) -> P) (forall (P : _) -> P -> P) false))) (\(x : _) -> x)) ((((bool::discr) (true)) (false)) (Heq)))) (connectives.False)))

notb : bool -> bool
notb = \(b : bool) -> match::bool::type (bool) false true b

andb : bool -> bool -> bool
andb = \(b1 : bool) -> \(b2 : bool) -> match::bool::type (bool) b2 false b1

andb::true::l : forall (b1 : bool) -> forall (b2 : bool) -> (logic.eq (bool) (andb b1 b2) true) -> logic.eq (bool) b1 true
andb::true::l = \(b1 : bool) -> ((((match::bool::prop) (\(:::: : bool) -> forall (b2 : bool) -> (logic.eq (bool) (andb :::: b2) true) -> logic.eq (bool) :::: true)) (\(b2 : bool) -> (((((((connectives.equal::leibniz) (bool)) (match::bool::type (bool) b2 false true)) (b2)) ((((axiom::match::bool::type::true) (bool)) (b2)) (false))) (\(a : bool) -> ((logic.eq (bool) a true) -> logic.eq (bool) true true) -> (logic.eq (bool) (match::bool::type (bool) b2 false true) true) -> logic.eq (bool) true true)) (\(px : (logic.eq (bool) (match::bool::type (bool) b2 false true) true) -> logic.eq (bool) true true) -> (px))) (\(auto : logic.eq (bool) b2 true) -> (((((((logic.rewrite::l) (bool)) (b2)) (\(:::: : bool) -> logic.eq (bool) :::: true)) (((((((logic.rewrite::l) (bool)) (b2)) (\(:::: : bool) -> logic.eq (bool) b2 ::::)) (((logic.refl) (bool)) (b2))) (true)) (auto))) (true)) (auto))))) (\(::b2 : bool) -> (((((((connectives.equal::leibniz) (bool)) (match::bool::type (bool) ::b2 false false)) (false)) ((((axiom::match::bool::type::false) (bool)) (::b2)) (false))) (\(a : bool) -> ((logic.eq (bool) a true) -> logic.eq (bool) false true) -> (logic.eq (bool) (match::bool::type (bool) ::b2 false false) true) -> logic.eq (bool) false true)) (\(px : (logic.eq (bool) (match::bool::type (bool) ::b2 false false) true) -> logic.eq (bool) false true) -> (px))) (\(auto : logic.eq (bool) false true) -> (((((((logic.rewrite::r) (bool)) (true)) (\(:::: : bool) -> logic.eq (bool) :::: true)) (((logic.refl) (bool)) (true))) (false)) (auto))))) (b1)

andb::true::r : forall (b1 : bool) -> forall (b2 : bool) -> (logic.eq (bool) (andb b1 b2) true) -> logic.eq (bool) b2 true
andb::true::r = \(b1 : bool) -> \(b2 : bool) -> ((((match::bool::prop) (\(:::: : bool) -> (logic.eq (bool) (andb :::: b2) true) -> logic.eq (bool) b2 true)) ((((((((connectives.equal::leibniz) (bool)) (match::bool::type (bool) b2 false true)) (b2)) ((((axiom::match::bool::type::true) (bool)) (b2)) (false))) (\(a : bool) -> ((logic.eq (bool) a true) -> logic.eq (bool) b2 true) -> (logic.eq (bool) (match::bool::type (bool) b2 false true) true) -> logic.eq (bool) b2 true)) (\(px : (logic.eq (bool) (match::bool::type (bool) b2 false true) true) -> logic.eq (bool) b2 true) -> (px))) (\(auto : logic.eq (bool) b2 true) -> (((((((logic.rewrite::l) (bool)) (b2)) (\(:::: : bool) -> logic.eq (bool) b2 ::::)) (((logic.refl) (bool)) (b2))) (true)) (auto))))) ((((((((connectives.equal::leibniz) (bool)) (match::bool::type (bool) b2 false false)) (false)) ((((axiom::match::bool::type::false) (bool)) (b2)) (false))) (\(a : bool) -> ((logic.eq (bool) a true) -> logic.eq (bool) b2 true) -> (logic.eq (bool) (match::bool::type (bool) b2 false false) true) -> logic.eq (bool) b2 true)) (\(px : (logic.eq (bool) (match::bool::type (bool) b2 false false) true) -> logic.eq (bool) b2 true) -> (px))) (((((match::bool::prop) (\(:::: : bool) -> (logic.eq (bool) false true) -> logic.eq (bool) :::: true)) (\(auto : logic.eq (bool) false true) -> (((logic.refl) (bool)) (true)))) (\(auto : logic.eq (bool) false true) -> (((((((logic.rewrite::r) (bool)) (true)) (\(:::: : bool) -> logic.eq (bool) :::: true)) (((logic.refl) (bool)) (true))) (false)) (auto)))) (b2)))) (b1)

true::or::false : forall (b : bool) -> connectives.Or (logic.eq (bool) b true) (logic.eq (bool) b false)
true::or::false = \(b : bool) -> ((((match::bool::prop) (\(:::: : bool) -> connectives.Or (logic.eq (bool) :::: true) (logic.eq (bool) :::: false))) ((((connectives.or::introl) (logic.eq (bool) true true)) (logic.eq (bool) true false)) (((logic.refl) (bool)) (true)))) ((((relations.RC::reflexive) (bool)) (\(:::: : bool) -> \(::0 : bool) -> logic.eq (bool) false true)) (false))) (b)

