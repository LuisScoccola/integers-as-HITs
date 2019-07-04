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
----   Theory of bi-invertible maps
----   ℤ. using biinvertible maps
----   recℤsimp. Map out of ℤ into type with element and isomorphism
----   indℤsimp. Prove proposition about ℤ by proving it for 0, succ, and pred1.
----   uniquenessℤ. Prove that maps is equal to the one given by recursion.
----   ℤisℤ. The equivalence with the usual definition of integers.


-- cubical lemmas

Square : {ℓ : _} → {A : Type ℓ} → {a0 a1 b0 b1 : A} →
         a0 ≡ a1 → b0 ≡ b1 → a0 ≡ b0 → a1 ≡ b1 → Type ℓ
Square α β γ δ = PathP (λ i → α i ≡ β i) γ δ

top-face : {ℓ : _} → {A : Type ℓ} → {a00 a01 a10 a11 b00 b01 b10 b11 : A} →
           {a0x : a00 ≡ a01} → {a1x : a10 ≡ a11} → {ax0 : a00 ≡ a10} → {ax1 : a01 ≡ a11} →
           {b0x : b00 ≡ b01} → {b1x : b10 ≡ b11} → {bx0 : b00 ≡ b10} → {bx1 : b01 ≡ b11} →
           {x00 : b00 ≡ a00} → {x01 : b01 ≡ a01} → {x10 : b10 ≡ a10} → {x11 : b11 ≡ a11} →
           Square b0x a0x x00 x01 → Square b1x a1x x10 x11 →
           Square bx0 ax0 x00 x10 → Square bx1 ax1 x01 x11 →
           Square a0x a1x ax0 ax1 →
             Square b0x b1x bx0 bx1 
top-face α β γ δ ε = λ i j →
  hcomp (λ k → \ { (i = i0) → γ j (~ k)
                 ; (i = i1) → δ j (~ k)
                 ; (j = i0) → α i (~ k)
                 ; (j = i1) → β i (~ k)}) (ε i j)

diag1 : {ℓ : _} → {A : Type ℓ} → {a0 a1 : A} → (p : a0 ≡ a1) →
          Square refl (λ i → p (~ i)) p refl
diag1 p = λ i j → p (~ i ∧ j)

diag2 : {ℓ : _} → {A : Type ℓ} → {a0 a1 : A} → (p : a0 ≡ a1) →
          Square refl p (λ i → p (~ i)) refl
diag2 p = λ i j → p (i ∨ ~ j)

diag3 : {ℓ : _} → {A : Type ℓ} → {a0 a1 : A} → (p : a0 ≡ a1) →
          Square p refl p refl
diag3 p = λ i j → p (i ∨ j)

diag5 : {ℓ : _} → {A : Type ℓ} → {a0 a1 : A} → (p : a0 ≡ a1) →
          Square refl p refl p
diag5 p = λ i j → p (i ∧ j)

diag6 : {ℓ : _} → {A : Type ℓ} → {a0 a1 : A} → (p : a0 ≡ a1) →
          Square (λ i → p (~ i)) refl refl p
diag6 p = λ i j → p (~ i ∨ j)

deg1 : {ℓ : _} → {A : Type ℓ} → {a0 a1 : A} → (p : a0 ≡ a1) →
          Square p p refl refl
deg1 p = λ i j → p i

diag4 : {ℓ : _} → {A : Type ℓ} → {a0 a1 a0' : A} →
        (p : a0 ≡ a1) → (q : a0' ≡ a1) →
          Square (λ i → q (~ i)) p (λ i → p (~ i)) q
diag4 p q =
  top-face
    (diag6 q)
    (deg1 p)
    (deg1 (λ i → p (~ i)))
    (diag3 q)
    (diag2 p)

compfill1 : {ℓ : _} → {A : Type ℓ} → {a0 a1 a2 : A} →
             (p : a0 ≡ a1) → (q : a1 ≡ a2) →
               Square (p ∙ q) p refl (λ i → q (~ i))
compfill1 p q = λ i j → compPath-filler p q (~ j) i

compress1 : {ℓ : _} → {A : Type ℓ} → {a0 a1 b0 b1 : A} →
            (α : a0 ≡ a1) → (β : b0 ≡ b1) → (γ : a0 ≡ b0) → (δ : a1 ≡ b1) →
            Square α β γ δ →
              Square α (λ i → δ (~ i)) (γ ∙ β) refl
compress1 α β γ δ s =
  top-face
    (deg1 α)
    (diag4 β δ) 
    (compfill1 γ β)
    (diag5 δ)
    s

compfill2 : {ℓ : _} → {A : Type ℓ}{a0 a1 a2 : A}
            (p : a0 ≡ a1) (q : a1 ≡ a2) →
              Square (p ∙ q) q p refl
compfill2 p q = transport (λ i → Square (p ∙ q) q (lUnit p (~ i)) refl)
                  (compress1 _ _ _ _ (λ i j → compPath-filler p q (~ j) i))


coherence1 : {ℓ : _} → {A B : Type ℓ} → {a0 a1 a2 : A} (b1 : B) →
             (f : A → B) → (p : a0 ≡ a1) → (q : a1 ≡ a2) → (r : f a2 ≡ b1) →
               Square ((cong f (p ∙ q)) ∙ r) ((cong f q) ∙ r) (cong f p) refl
coherence1 b1 f p q r =
  top-face
    (compfill2 (cong f (p ∙ q)) r)
    (compfill2 (cong f q) r)
    (λ i j → f (compfill2 p q j i))
    (λ i j → b1)
    (λ i j → r i)


-- BiInvertible maps and preservation of BiInvertible maps

  -- Def
record isBiInv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  constructor buildisBiInv
  field
    g : B → A
    h : B → A
    sec : ∀ a → g (f a) ≡ a
    ret : ∀ b → f (h b) ≡ b

open isBiInv


  -- Identity is BiInv
idIsBiInv : {l : _} (A : Type l) → isBiInv (idfun A)
idIsBiInv A = record { g = λ a → a ; h = λ a → a ; sec = λ a i → a ; ret = λ a i → a }


  -- An equality in the universe gives a BiInv map
EqtoBiInv : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (h : A ≡ B) → Σ (A → B) (λ f → isBiInv f)
EqtoBiInv h = transport h , (buildisBiInv (transport⁻ h) (transport⁻ h)
                                          (transport⁻Transport h) (transportTransport⁻ h))


  -- A BiInv map gives an iso
unique_ret : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (finv : B → A)
             (fr : (b : B) → f (finv b) ≡ b)
             (g : B → A) (fs' : (a : A) → g (f a) ≡ a) →
               (b : B) → g b ≡ finv b
unique_ret f finv fr g fs' b = (cong g (fr b))⁻¹ ∙ (fs' (finv b))

unique_sec : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (finv : B → A)
             (fs : (a : A) → finv (f a) ≡ a)
             (g : B → A) (fr' : (b : B) → f (g b) ≡ b) →
               (b : B) → g b ≡ finv b
unique_sec f finv fs g fr' b = (fs (g b))⁻¹ ∙ cong finv (fr' b)

BiInvtoIso : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (is : isBiInv f) → Iso A B
BiInvtoIso f is = record { fun = f
                         ; inv = h is
                         ; rightInv = ret is
                         ; leftInv = λ x → transport
                             (λ i → (unique_ret f (h is) (ret is) (g is) (sec is) (f x) i) ≡ x)
                             ((sec is) x) }

  -- A BiInv map gives an equivalence
BiInvtoEquiv : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (is : isBiInv f) → isEquiv f
BiInvtoEquiv f is = isoToIsEquiv (BiInvtoIso f is)

  -- An equivalece gives a BiInv map
EquivtoBiInv : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (h : isEquiv f) → isBiInv f
EquivtoBiInv f h = buildisBiInv inv inv
                     (λ a → cong fst (snd ((equiv-proof h) (f a)) (a , refl)))
                     (λ b → snd (fst ((equiv-proof h) b))) 
  where inv = (λ b → fst (fst ((equiv-proof h) b)))


  -- BiInv-induction
comp1 : ∀ {ℓ} (A : Type ℓ) → (EquivtoBiInv (idfun A) (idIsEquiv A)) ≡ idIsBiInv A
comp1 A = refl

comp2 : ∀ {ℓ} (A : Type ℓ) → (BiInvtoEquiv (idfun A) (idIsBiInv A)) ≡ idIsEquiv A
comp2 A = isPropIsEquiv (idfun A) _ _

BiInvtoEq : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (h : isBiInv f) → A ≡ B
BiInvtoEq f h = ua (f , BiInvtoEquiv f h)

EquivJ' : {ℓ ℓ' : _} (P : (B A : Type ℓ) → (e : B ≃ A) → Type ℓ')
        → (P0 : (A : Type ℓ) → P A A (idEquiv A))
        → (B A : Type ℓ) → (e : B ≃ A) → P B A e
EquivJ' P P0 B A e = EquivJ (λ A B e → P B A e) P0 A B e

D : {l l' : _} (X Y : Type l) (f : X ≃ Y) → Type (ℓ-max (ℓ-suc l) (ℓ-suc l'))
D {l} {l'} X Y f = (C : (Z : Type l) → (X ≃ Z) → Type l') → C X (idEquiv X) → C Y f

d : {l l' : _} (X : Type l) → D {l} {l'} X X (idEquiv X)
d X C c = c

F : {l l' : _} (X Y : Type l) (f : X ≃ Y) → D {l} {l'} X Y f
F X Y f = EquivJ' D d X Y f

EquivInduction' : {l l' : _} (A : Type l) →
                  (P : (B : Type l) → (f : A ≃ B) → Type l') →
                  (p0 : P A (idEquiv A)) →
                  (B : Type l) → (f : A ≃ B) → P B f
EquivInduction' A P p0 B f = F A B f P p0


EquivInduction : {l l' : _} (A : Type l) →
                 (P : (B : Type l) → (f : A → B) → (h : isEquiv f) → Type l') →
                 (p0 : P A (idfun A) (idIsEquiv A)) →
                 (B : Type l) → (f : A → B) → (h : isEquiv f) → P B f h
EquivInduction A P p0 B f h = EquivInduction' A (λ B f → P B (fst f) (snd f)) p0 B (f , h)

isBiInvId' : ∀ {ℓ} {A : Type ℓ} (x : isBiInv (idfun A)) → x ≡ idIsBiInv A
isBiInvId' x = λ i → record { g = λ a → (sec x a) i ;
                              h = λ a → (ret x a) i ;
                              sec = λ a j → (sec x a) (i ∨ j) ;
                              ret = λ a j → (ret x a) (i ∨ j) }

isPropBiInv' : ∀ {ℓ} {A : Type ℓ} (B : Type ℓ) (f : A → B) (h : isEquiv f) → isProp (isBiInv f)
isPropBiInv' B f h = EquivInduction _ (λ B f h → isProp (isBiInv f))
                     (λ x y → (isBiInvId' x) ∙ (isBiInvId' y)⁻¹) B f h

inhabprop : ∀ {ℓ} {A : Type ℓ} (i : (a : A) → isProp A) → isProp A
inhabprop i x y = i x x y

isPropBiInv : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) → isProp (isBiInv f)
isPropBiInv f = inhabprop (λ h → isPropBiInv' _ f (BiInvtoEquiv f h))

BiInduction : {l l' : _} (A : Type l) →
              (P : (B : Type l) → (f : A → B) → (h : isBiInv f) → Type l') →
              (p0 : P A (idfun A) (idIsBiInv A)) →
              (B : Type l) → (f : A → B) → (h : isBiInv f) → P B f h
BiInduction A P p0 B f h =
  subst (P B f) (isPropBiInv f (EquivtoBiInv f (BiInvtoEquiv f h)) h)
    (EquivInduction A (λ B f h → P B f (EquivtoBiInv f h))
                    (subst (P A (idfun A)) (comp1 A) p0)
                    B f (BiInvtoEquiv f h))



  -- preservation of BiInv-map
record pr_Bi {ℓ} {A B A' B' : Type ℓ} (α : A → A') (β : B → B')
                  (e : A → B) (BIe : isBiInv e)
                  (e' : A' → B') (BIe' : isBiInv e') : Type ℓ where
  field
    pr_e : (a : A) → e' (α a) ≡ β (e a) 
    pr_g : (b : B) → (g BIe') (β b) ≡ α ((g BIe) b)
    pr_h : (b : B) → (h BIe') (β b) ≡ α ((h BIe) b)
    pr_sec : (a : A) → Square (sec BIe' (α a)) (pr_g (e a)) (cong (g BIe') (pr_e a)) ((cong α (sec BIe a))⁻¹)
    pr_ret : (b : B) → Square (ret BIe' (β b)) (pr_e (h BIe b)) (cong e' (pr_h b)) ((cong β (ret BIe b))⁻¹)

open pr_Bi


  -- to preserve a bi-invertible map it is enough to preserve the map
to_pr_Bi' : {A A' B' : Set} →
            (e' : A' → B') → (BIe' : isBiInv e') →
            (α : A → A') → (β : A → B') →
              (pr_e : (a : A) → e' (α a) ≡ β ((idfun A) a)) →
                 pr_Bi α β (idfun A) (idIsBiInv A) e' BIe'
to_pr_Bi' {A} {A'} {B'} h' BIh' α β pr_h =
      BiInduction A' (λ B' h' BIh' → (α : A → A') → (β : A → B') →
                        (pr_h : (a : A) → h' (α a) ≡ β a) →
                        pr_Bi α β (idfun A) (idIsBiInv A) h' BIh')
                  (λ α β H → record { pr_e = H ; pr_g = λ a → (H a)⁻¹ ; pr_h = λ a → (H a)⁻¹
                                    ; pr_sec = λ a → diag1 (H a)
                                    ; pr_ret = λ a → diag2 (H a) })
                  B' h' BIh' α β pr_h

to_pr_Bi : {A B A' B' : Set} →
           (e : A → B) → (BIe : isBiInv e) →
           (e' : A' → B') → (BIe' : isBiInv e') →
           (α : A → A') → (β : B → B') →
           (pr_e : (a : A) → e' (α a) ≡ β (e a)) →
             pr_Bi α β e BIe e' BIe'
to_pr_Bi {A} {B} {A'} {B'} h BIh h' BIh' α β pr_h =
  (BiInduction A
    (λ B h BIh → (h' : A' → B') → (BIh' : isBiInv h') → (α : A → A') → (β : B → B') →
      (pr_h : (a : A) → h' (α a) ≡ β (h a)) → pr_Bi α β h BIh h' BIh')
    to_pr_Bi'
    B h BIh) h' BIh' α β pr_h


-- ℤ using biInvertible maps

data ℤ : Set where
  zero : ℤ
  succ : ℤ → ℤ 
  pred1 : ℤ → ℤ 
  pred2 : ℤ → ℤ 
  s : (z : ℤ) → pred1 (succ z) ≡ z
  r : (z : ℤ) → succ (pred2 z) ≡ z

pred1ispred2 : (z : ℤ) → pred1 z ≡ pred2 z
pred1ispred2 z = cong pred1 (r z)⁻¹ ∙ s (pred2 z)

recℤ : {l : _} (T : Type l) → (t : T) → (succT : T → T) → (pred1T : T → T) → (pred2T : T → T) →
       (sT : (t : T) → pred1T (succT t) ≡ t) → (rT : (t : T) → succT (pred2T t) ≡ t) →
         ℤ → T
recℤ T t succT pred1T pred2T sT rT zero = t
recℤ T t succT pred1T pred2T sT rT (succ n) = succT (recℤ T t succT pred1T pred2T sT rT n)
recℤ T t succT pred1T pred2T sT rT (pred1 n) = pred1T (recℤ T t succT pred1T pred2T sT rT n)
recℤ T t succT pred1T pred2T sT rT (pred2 n) = pred2T (recℤ T t succT pred1T pred2T sT rT n)
recℤ T t succT pred1T pred2T sT rT (s n i) = sT (recℤ T t succT pred1T pred2T sT rT n) i
recℤ T t succT pred1T pred2T sT rT (r n i) = rT (recℤ T t succT pred1T pred2T sT rT n) i


  -- simple recursion
recℤsimpl : (T : Set) → (t : T) → (succT : T → T) → (predT : T → T) →
            (sT : (t : T) → predT (succT t) ≡ t) →
            (rT : (t : T) → succT (predT t) ≡ t) → ℤ → T
recℤsimpl T t succT predT sT rT = recℤ T t succT predT predT sT rT


transpProp : {X : Set} (P : X → Set) (ip : (x : X) → isProp (P x))
             (x y : X) (q : x ≡ y) (px : P x) (py : P y) →
               PathP (λ i → P (q i)) px py
transpProp P ip x y q px py = toPathP (ip y _ _)


  -- simple induction
indℤsimpl : (P : ℤ → Set) → (ip : (z : ℤ) → isProp (P z)) →
            (p0 : P zero) →
            (ps : (z : ℤ) → P z → P (succ z)) →
            (pp : (z : ℤ) → P z → P (pred1 z)) →
              (z : ℤ) → P z
indℤsimpl P ip p0 ps pp zero = p0
indℤsimpl P ip p0 ps pp (succ n) = ps n (indℤsimpl P ip p0 ps pp n)
indℤsimpl P ip p0 ps pp (pred1 n) = pp n (indℤsimpl P ip p0 ps pp n)
indℤsimpl P ip p0 ps pp (pred2 n) = transport (λ i → P (pred1ispred2 n i))
                                      (pp n (indℤsimpl P ip p0 ps pp n))
indℤsimpl P ip p0 ps pp (s n i) = transpProp P ip _ _ (s n)
                                    (pp _ (ps _ (indℤsimpl P ip p0 ps pp n)))
                                    (indℤsimpl P ip p0 ps pp n) i
indℤsimpl P ip p0 ps pp (r n i) = transpProp P ip _ _ (r n)
                                    (ps _ (transport (λ i → P (pred1ispred2 n i))
                                            (pp n (indℤsimpl P ip p0 ps pp n))))
                                    (indℤsimpl P ip p0 ps pp n) i


-- initiality of ℤ

  -- a map out of ℤ that preserves 0, succ, and biinvertible structure is the one given by recursion 
uniqueness : (T : Set) → (t : T) → (succT : T → T) → (pred1T : T → T) → (pred2T : T → T) →
             (sT : (t : T) → pred1T (succT t) ≡ t) → (rT : (t : T) → succT (pred2T t) ≡ t) →
             (f : ℤ → T) → (p : t ≡ f zero) → (P : pr_Bi f f succ (buildisBiInv pred1 pred2 s r)
                                                   succT (buildisBiInv pred1T pred2T sT rT)) →
             (z : ℤ) → (recℤ T t succT pred1T pred2T sT rT) z ≡ f z
uniqueness T t succT pred1T pred2T sT rT f p P zero = p
uniqueness T t succT pred1T pred2T sT rT f p P (succ n) =
  cong succT (uniqueness T t succT pred1T pred2T sT rT f p P n) ∙ (pr_e P n)
uniqueness T t succT pred1T pred2T sT rT f p P (pred1 n) =
  cong pred1T (uniqueness T t succT pred1T pred2T sT rT f p P n) ∙ (pr_g P n)
uniqueness T t succT pred1T pred2T sT rT f p P (pred2 n) =
  cong pred2T (uniqueness T t succT pred1T pred2T sT rT f p P n) ∙ (pr_h P n)
uniqueness T t succT pred1T pred2T sT rT f p P (s n i) =
  (top-face
    (λ i j → cong sT (uniqueness T t succT pred1T pred2T sT rT f p P n) j i)
    (deg1 (cong f (s n)))
    (coherence1 _ pred1T _ _ _)
    (diag3 (uniqueness T t succT pred1T pred2T sT rT f p P n))
    (compress1 _ _ _ _ (pr_sec P n))) i
uniqueness T t succT pred1T pred2T sT rT f p P (r n i) =
  (top-face
    (λ i j → cong rT (uniqueness T t succT pred1T pred2T sT rT f p P n) j i)
    (deg1 (cong f (r n)))
    (coherence1 _ succT _ _ _)
    (diag3 (uniqueness T t succT pred1T pred2T sT rT f p P n))
    (compress1 _ _ _ _ (pr_ret P n))) i



-- MAIN THEOREM

  -- a map out of ℤ is determined by zero and succ
uniquenessℤ : (T : Set) → (t : T) → (succT : T → T) → (pred1T : T → T) →
                     (pred2T : T → T) → (sT : (t : T) → pred1T (succT t) ≡ t) →
                     (rT : (t : T) → succT (pred2T t) ≡ t) →
                     (f : ℤ → T) → (p : t ≡ f zero) →
                     (pr_e : (n : ℤ) → succT (f n) ≡ f (succ n)) →
                       (z : ℤ) → (recℤ T t succT pred1T pred2T sT rT) z ≡ f z
uniquenessℤ T t succT pred1T pred2T sT rT f p pr_e z =
  uniqueness T t succT pred1T pred2T sT rT f p
    (to_pr_Bi succ (buildisBiInv pred1 pred2 s r)
              succT (buildisBiInv pred1T pred2T sT rT) f f pr_e) z


-- Equivalence with usual def of ℤ

data 𝕫 : Set where
  zero : 𝕫
  strpos : ℕ → 𝕫
  strneg : ℕ → 𝕫

succ𝕫 : 𝕫 → 𝕫
succ𝕫 zero = strpos zero
succ𝕫 (strpos n) = strpos (suc n)
succ𝕫 (strneg zero) = zero
succ𝕫 (strneg (suc n)) = strneg n

pred𝕫 : 𝕫 → 𝕫
pred𝕫 zero = strneg zero
pred𝕫 (strpos zero) = zero
pred𝕫 (strpos (suc n)) = strpos n
pred𝕫 (strneg n) = strneg (suc n)

s𝕫 : (z : 𝕫) → pred𝕫 (succ𝕫 z) ≡ z
s𝕫 zero = refl
s𝕫 (strpos n) = refl
s𝕫 (strneg zero) = refl
s𝕫 (strneg (suc n)) = refl

r𝕫 : (z : 𝕫) → succ𝕫 (pred𝕫 z) ≡ z
r𝕫 zero = refl
r𝕫 (strpos zero) = refl
r𝕫 (strpos (suc n)) = refl
r𝕫 (strneg n) = refl

ℤto𝕫 : ℤ → 𝕫
ℤto𝕫 zero = zero
ℤto𝕫 (succ n) = succ𝕫 (ℤto𝕫 n)
ℤto𝕫 (pred1 n) = pred𝕫 (ℤto𝕫 n)
ℤto𝕫 (pred2 n) = pred𝕫 (ℤto𝕫 n)
ℤto𝕫 (s n i) = s𝕫 (ℤto𝕫 n) i
ℤto𝕫 (r n i) = r𝕫 (ℤto𝕫 n) i

𝕫toℤ : 𝕫 → ℤ
𝕫toℤ zero = zero
𝕫toℤ (strpos zero) = succ zero
𝕫toℤ (strpos (suc n)) = succ (𝕫toℤ (strpos n))
𝕫toℤ (strneg zero) = pred1 zero
𝕫toℤ (strneg (suc n)) = pred1 (𝕫toℤ (strneg n))


coh : (z : ℤ) → pred1 z ≡ pred2 z
coh z = cong pred1 (r z)⁻¹ ∙ s (pred2 z)

r' : (z : ℤ) → succ (pred1 z) ≡ z
r' z = cong succ (coh z) ∙ r z

prsucc : (n : 𝕫) → succ (𝕫toℤ n) ≡ 𝕫toℤ (succ𝕫 n)
prsucc zero = refl
prsucc (strpos n) = refl
prsucc (strneg zero) = r' zero
prsucc (strneg (suc n)) = r' (𝕫toℤ (strneg n))


ℤto𝕫toℤ' : (z : ℤ) → (recℤ ℤ zero succ pred1 pred2 s r) z ≡ 𝕫toℤ (ℤto𝕫 z)
ℤto𝕫toℤ' z =
  uniquenessℤ ℤ zero succ pred1 pred2 s r
    (𝕫toℤ ∘ ℤto𝕫) refl (prsucc ∘ ℤto𝕫) z

rec_is_id : (z : ℤ) → (recℤ ℤ zero succ pred1 pred2 s r) z ≡ z
rec_is_id zero = refl
rec_is_id (succ n) = cong succ (rec_is_id n)
rec_is_id (pred1 n) = cong pred1 (rec_is_id n)
rec_is_id (pred2 n) = cong pred2 (rec_is_id n)
rec_is_id (s n i) = λ j → s (rec_is_id n j) i
rec_is_id (r n i) = λ j → r (rec_is_id n j) i


  -- equivalence

𝕫toℤto𝕫 : (z : 𝕫) → ℤto𝕫 (𝕫toℤ z) ≡ z
𝕫toℤto𝕫 zero = refl
𝕫toℤto𝕫 (strpos zero) = refl
𝕫toℤto𝕫 (strpos (suc n)) = cong succ𝕫 (𝕫toℤto𝕫 (strpos n))
𝕫toℤto𝕫 (strneg zero) = refl
𝕫toℤto𝕫 (strneg (suc n)) = cong pred𝕫 (𝕫toℤto𝕫 (strneg n))

ℤto𝕫toℤ : (z : ℤ) → 𝕫toℤ (ℤto𝕫 z) ≡ z
ℤto𝕫toℤ z = (ℤto𝕫toℤ' z)⁻¹ ∙ (rec_is_id z)

ℤisℤ : ℤ ≃ 𝕫
ℤisℤ = isoToEquiv
  (record {fun = ℤto𝕫 ; inv = 𝕫toℤ ; rightInv = 𝕫toℤto𝕫 ; leftInv = ℤto𝕫toℤ  })
