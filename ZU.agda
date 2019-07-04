{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

---- Contents:
----   ℤ. integers using a small universe
----   ℤisInitial. Initiality of the integers as a type with an inhabitant and equality.
----   ElisPath. Loops space of the circle is the integers


-- ℤ-algebras and ℤ-algebra morphism

record ℤ-alg {l : _} : Type (ℓ-suc l) where
  field
    car : Type l
    el : car
    end : car ≡ car

open ℤ-alg

record is-ℤ-alg-morph {l m : _} {T : ℤ-alg {l}} {T' : ℤ-alg {m}} (mor : car T → car T') : Type (ℓ-max l m) where
  field
    pr_el : mor (el T) ≡ el T'
    pr_end : PathP (λ i → (end T) i → (end T' i)) mor mor

open is-ℤ-alg-morph

record ℤ-alg-morph {l m : _} (T : ℤ-alg {l}) (T' : ℤ-alg {m}) : Type (ℓ-max l m) where
  field
    mor : (car T) → (car T')
    ismor : is-ℤ-alg-morph {l} {m} {T} {T'} mor

open ℤ-alg-morph


data U : Set where
  int : U
  eq : int ≡ int 

data El : U → Set where
  zero : El int

ℤ : Set
ℤ = El int

-- the type family El is equivalent to the pathspace fibration
-- in particular, it follows from the usual proof that ℤ is equivalent to the integers presented as a signed natural numbers

to_path : (u : U) → El u → int ≡ u
to_path .int zero = refl

to_El : (u : U) → int ≡ u → El u
to_El u p = transport (λ i → El (p i)) zero

topathtoEl : (u : U) → (e : El u) → to_El u (to_path u e) ≡ e
topathtoEl .int zero = transportRefl zero

toEltopath : (u : U) → (p : int ≡ u) → to_path u (to_El u p) ≡ p
toEltopath u p = J (λ u p → to_path u (to_El u p) ≡ p)
                   (cong (to_path int) (transportRefl zero)) p

ElisPath : (u : U) → El u ≃ (int ≡ u)
ElisPath u = isoToEquiv
  (record {fun = to_path u ; inv = to_El u ; rightInv = toEltopath u ; leftInv = topathtoEl u })

-- ℤ is a universal ℤ-algebra

ℤ-as-alg : ℤ-alg
ℤ-as-alg = record { car = ℤ ; el = zero ; end = cong El eq }


M : (X : Set)(e : X ≡ X) → U → Set
M X e int = X
M X e (eq i) = e i

Muniq : (X : Set)(e : X ≡ X) →
        (f : U → Set) → (prX : f int ≡ X) → (pre : PathP (λ i → prX i ≡ prX i) (cong f eq) e) →
          (u : U) → f u ≡ M X e u
Muniq X e f prX pre int = prX
Muniq X e f prX pre (eq i) = λ j → pre j i


Rℤaux : (X : Set)(z : X)(e : X ≡ X) → (x : U) → El x → M X e x
Rℤaux X z e .int zero = z

Rℤauxuniq : (X : Set)(z : X)(e : X ≡ X) →
            (f : (x : U) → El x → M X e x) → (pr0 : f int zero ≡ Rℤaux X z e int zero) →
              (x : U) → (el : El x) → f x el ≡ Rℤaux X z e x el
Rℤauxuniq X z e f pr0 .int zero = pr0

Rℤ : (X : Set)(z : X)(e : X ≡ X) → ℤ → X
Rℤ X z e = Rℤaux X z e int


fromℤalgmorph : (X : Set)(x : X)(e : X ≡ X) →
                (f : ℤ → X) → (pre : PathP (λ i → El (eq i) → e i) f f) →
                  (u : U) → El u → M X e u
fromℤalgmorph X x e f pre int = f
fromℤalgmorph X x e f pre (eq i) = pre i

Rℤuniq : (X : Set)(x : X)(e : X ≡ X) →
         (f : ℤ → X) → (pr0 : f zero ≡ x) → (pre : PathP (λ i → El (eq i) → e i) f f) →
           (z : ℤ) → f z ≡ Rℤ X x e z
Rℤuniq X x e f pr0 pre = Rℤauxuniq X x e (fromℤalgmorph X x e f pre) pr0 int



Rℤ_pr_el : (X : Set)(z : X)(e : X ≡ X) → Rℤ X z e zero ≡ z
Rℤ_pr_el X z e = refl


Rℤ_pr_end : (X : Set)(z : X)(e : X ≡ X) →
    PathP (λ i → El (eq i) → e i) (Rℤ X z e) (Rℤ X z e)
Rℤ_pr_end X z e = cong (Rℤaux X z e) eq


existence : (X : ℤ-alg) → (ℤ-alg-morph ℤ-as-alg X)
existence X = record { mor = Rℤ (car X) (el X) (end X)
                     ; ismor = record { pr_el = Rℤ_pr_el _ _ (end X)
                                      ; pr_end = Rℤ_pr_end _ _ _ } }

existence' : (X : ℤ-alg) → (ℤ-alg-morph ℤ-as-alg X)
existence' X = record { mor = Rℤaux (car X) (el X) (end X) int
                      ; ismor = record { pr_el = refl
                                       ; pr_end = cong (Rℤaux (car X) (el X) (end X)) eq} }


uniqueness_aux : (X : ℤ-alg) → (m : ℤ-alg-morph ℤ-as-alg X) →
                   (z : ℤ) → mor m z ≡ mor (existence X) z
uniqueness_aux X m z = Rℤuniq (car X) (el X) (end X) (mor m) (pr_el (ismor m)) (pr_end (ismor m)) z


uniqueness : (X : ℤ-alg) → (m : ℤ-alg-morph ℤ-as-alg X) →
               m ≡ existence X
uniqueness X m = λ i → record { mor = (λ z → Rℤuniq (car X) (el X) (end X) (mor m) (pr_el (ismor m)) (pr_end (ismor m)) z i)
                              ; ismor = record { pr_el = λ j → pr_el (ismor m) (i ∨ j)
                                               ; pr_end = λ j → λ z →
                                                            Rℤauxuniq (car X) (el X) (end X)
                                                                      (fromℤalgmorph (car X) (el X) (end X) (mor m) (pr_end (ismor m)))
                                                                      (pr_el (ismor m)) (eq j) z i } }


ℤisInitial : (X : ℤ-alg) → isContr (ℤ-alg-morph ℤ-as-alg X)
ℤisInitial X = (existence X , λ m → (uniqueness X m)⁻¹ )
