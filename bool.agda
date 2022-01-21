module bool where
open import Agda.Primitive
open import connectives
open import leibniz
open import logic
open import relations
postulate bool : Set
postulate true : bool
postulate false : bool
postulate match::bool::prop : {l : Level} ->  (return : (bool -> Set l)) -> (return true) -> (return false) -> forall (z : bool) -> return z
postulate match::bool::type : {l : Level} -> (return : Set l) -> return -> return -> bool -> return
postulate axiom::match::bool::type::true : {i : Level} → (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> connectives.equal (return) (match::bool::type (return) case::true case::false true) case::true
eq::match::bool::type::true : {i j : Level} → _
eq::match::bool::type::true {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> ((((connectives.equal::leibniz) {_} {j} (return)) (match::bool::type (return) case::true case::false true)) (case::true)) ((((axiom::match::bool::type::true) (return)) (case::true)) (case::false))

postulate axiom::match::bool::type::false : {i : Level} → (return : Set i) -> forall (case::true : return) -> forall (case::false : return) -> connectives.equal (return) (match::bool::type (return) case::true case::false false) case::false
eq::match::bool::type::false : {i j : Level} → _
eq::match::bool::type::false {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> ((((connectives.equal::leibniz) {_} {j} (return)) (match::bool::type (return) case::true case::false false)) (case::false)) ((((axiom::match::bool::type::false) (return)) (case::true)) (case::false))

sym::eq::match::bool::type::true : {i j : Level} →  _
sym::eq::match::bool::type::true {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> (((leibniz.sym::leibniz {_} {j}  (return)) (match::bool::type (return) case::true case::false true)) (case::true)) ((((eq::match::bool::type::true) (return)) (case::true)) (case::false))

sym::eq::match::bool::type::false : {i j : Level} → _
sym::eq::match::bool::type::false {i} {j} = \(return : Set i) -> \(case::true : return) -> \(case::false : return) -> ((((leibniz.sym::leibniz) {_} {j} (return)) (match::bool::type (return) case::true case::false false)) (case::false)) ((((eq::match::bool::type::false) (return)) (case::true)) (case::false))

bool::discr : _
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

not::eq::true::false : _
not::eq::true::false = ((connectives.nmk) (logic.eq (bool) true false)) (\(Heq : logic.eq (bool) true false) -> (((((((eq::match::bool::type::false) _) (forall (P : Set) -> P -> P)) (forall (P : Set) -> P)) (\(x) -> x)) ((((((eq::match::bool::type::true) _) (match::bool::type _ (forall (P : Set) -> P -> P) (forall (P : Set) -> P) false)) (match::bool::type _ (forall (P : Set) -> P) (forall (P : Set) -> P -> P) false)) (\(x) -> x)) ((((bool::discr) (true)) (false)) (Heq)))) (connectives.False)))

notb : _
notb = \(b : bool) -> match::bool::type (bool) false true b

andb : _
andb = \(b1 : bool) -> \(b2 : bool) -> match::bool::type (bool) b2 false b1

andb::true::l : _
andb::true::l = \(b1 : bool) -> ((((match::bool::prop) (\(:::: : bool) -> forall (b2 : bool) -> (logic.eq (bool) (andb :::: b2) true) -> logic.eq (bool) :::: true)) (\(b2 : bool) -> (((((sym::eq::match::bool::type::true) (bool)) (b2)) (false)) (\(x : bool) -> (logic.eq (bool) x true) -> logic.eq (bool) true true)) (\(auto : logic.eq (bool) b2 true) -> (((((((logic.rewrite::l) (bool)) (b2)) (\(:::: : bool) -> logic.eq (bool) :::: true)) (((((((logic.rewrite::l) (bool)) (b2)) (\(:::: : bool) -> logic.eq (bool) b2 ::::)) (((logic.refl) (bool)) (b2))) (true)) (auto))) (true)) (auto))))) (\(::b2 : bool) -> (((((sym::eq::match::bool::type::false) (bool)) (::b2)) (false)) (\(x : bool) -> (logic.eq (bool) x true) -> logic.eq (bool) false true)) (\(auto : logic.eq (bool) false true) -> (((((((logic.rewrite::r) (bool)) (true)) (\(:::: : bool) -> logic.eq (bool) :::: true)) (((logic.refl) (bool)) (true))) (false)) (auto))))) (b1)

andb::true::r : _
andb::true::r = \(b1 : bool) -> \(b2 : bool) -> ((((match::bool::prop) (\(:::: : bool) -> (logic.eq (bool) (andb :::: b2) true) -> logic.eq (bool) b2 true)) ((((((sym::eq::match::bool::type::true) (bool)) (b2)) (false)) (\(x : bool) -> (logic.eq (bool) x true) -> logic.eq (bool) b2 true)) (\(auto : logic.eq (bool) b2 true) -> (((((((logic.rewrite::l) (bool)) (b2)) (\(:::: : bool) -> logic.eq (bool) b2 ::::)) (((logic.refl) (bool)) (b2))) (true)) (auto))))) ((((((sym::eq::match::bool::type::false) (bool)) (b2)) (false)) (\(x : bool) -> (logic.eq (bool) x true) -> logic.eq (bool) b2 true)) (((((match::bool::prop) (\(:::: : bool) -> (logic.eq (bool) false true) -> logic.eq (bool) :::: true)) (\(auto : logic.eq (bool) false true) -> (((logic.refl) (bool)) (true)))) (\(auto : logic.eq (bool) false true) -> (((((((logic.rewrite::r) (bool)) (true)) (\(:::: : bool) -> logic.eq (bool) :::: true)) (((logic.refl) (bool)) (true))) (false)) (auto)))) (b2)))) (b1)

true::or::false : _
true::or::false = \(b : bool) -> ((((match::bool::prop) (\(:::: : bool) -> connectives.Or (logic.eq (bool) :::: true) (logic.eq (bool) :::: false))) ((((connectives.or::introl) (logic.eq (bool) true true)) (logic.eq (bool) true false)) (((logic.refl) (bool)) (true)))) ((((relations.RC::reflexive) (bool)) (\(:::: : bool) -> \(::0 : bool) -> logic.eq (bool) false true)) (false))) (b)

