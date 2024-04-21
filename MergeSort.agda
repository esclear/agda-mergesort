{-# OPTIONS --rewriting --exact-split --guardedness #-}

-- An Agda implementation of merge sort
-- The goal is to show that
-- 1. The result is sorted
-- 2. The result is a permutation of the input (i.e. a sorted arrangement of the input data)

open import Data.Nat using (ℕ ; zero ; suc; _+_ ; ⌊_/2⌋ ; ⌈_/2⌉) renaming (_<_ to _<ₙ_)
open import Data.Nat.Properties using (+-assoc ; +-suc ; +-identityʳ ; +-comm ; ⌊n/2⌋+⌈n/2⌉≡n ; ⌊n/2⌋<n ; ⌈n/2⌉<n)
open import Data.Nat.Induction
open import Data.Product using (_×_ ; _,_ ; ∃₂ ; proj₁ ; proj₂ ; swap)
open import Data.Vec using (Vec ; [] ; _∷_ ; _++_ ; split ; splitAt ; take ; drop)
open import Data.Vec.Relation.Unary.All as All

open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.Properties.DecTotalOrder using (≰⇒≥)
open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl; trans to ≡-trans)
open import Relation.Binary.Structures
open import Relation.Nullary hiding (proof)
open import Relation.Unary

open import Level using (Level ; 0ℓ)

{-# BUILTIN REWRITE _≡_ #-}

module MergeSort (dto : DecTotalOrder 0ℓ 0ℓ 0ℓ) where

-- Use rewriting to simplify the goals a bit, so that our life is a bit easier.
-- These two rewriting rules normalize sums of natural numbers, such that we don't have to introduce
-- special handling for cases such as n + 0 and n + succ m.
{-# REWRITE +-identityʳ +-suc ⌊n/2⌋+⌈n/2⌉≡n #-}

open DecTotalOrder dto

-- Use `C` as a shorthand for the type underlying the total order
C : Set
C = Carrier

module Helper where
  open import Induction.WellFounded public

  P : Pred ℕ 0ℓ
  P n = Vec C n → Vec C n

module Implementation where
  -- Helpers for splitting a vector into halves
  left-half : {n : ℕ} → Vec C n → Vec C ⌊ n /2⌋
  left-half {n} xs with splitAt ⌊ n /2⌋ {⌈ n /2⌉} xs
  ... | (left , _ , _) = left

  right-half : {n : ℕ} → Vec C n → Vec C ⌈ n /2⌉
  right-half {n} xs with splitAt ⌊ n /2⌋ {⌈ n /2⌉} xs
  ... | (_ , right , _) = right

  concat-halves : {n : ℕ} → (xs : Vec C n) → xs ≡ left-half xs ++ right-half xs
  concat-halves {n} xs with splitAt ⌊ n /2⌋ {⌈ n /2⌉} xs
  ... | (_ , _ , p) = p

  -- Merge two sorted vectors into a sorted combination of both input vectors
  merge : {m n : ℕ} → Vec C m → Vec C n → Vec C (m + n)
  merge                 []         vs                = vs
  merge {suc m}         us@(_ ∷ _) []                = us
  merge {suc m} {suc n} (u ∷ us) (v ∷ vs) with u ≤? v
  ...                                        | yes _ = u ∷ merge us (v ∷ vs)
  ...                                        | no  _ = v ∷ merge (u ∷ us) vs

  -- Sort by splitting the vector into two pieces, sorting those recursively and merging the sorted halves
  <-step : (x : ℕ) → x ∈ (Helper.WfRec _<ₙ_ Helper.P) → x ∈ Helper.P
  <-step zero            _   _  = []
  <-step (suc zero)      _   xs = xs
  <-step n@(suc (suc m)) rec xs = merge (rec ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) (left-half  xs))
                                        (rec ⌈ n /2⌉ (⌈n/2⌉<n m)       (right-half xs))

  -- To define it, we use the standard library's well-founded recursion.
  -- To be able to use <-rec, define a variant that takes the length as an explicit argument:
  mergesort-int : (n : ℕ) → Vec C n → Vec C n
  mergesort-int = <-rec _ <-step

  mergesort : {n : ℕ} → Vec C n → Vec C n
  mergesort {n} us = mergesort-int n us

open Implementation public hiding (mergesort-int ; <-step)


module Verification where
  open ≡-Reasoning

  private
    variable
      m n : ℕ

  -- **************
  -- **  HELPER  **
  -- **************
  open Helper

  module _ where
    open import Relation.Binary.Core

    module CoolerFixPoint
      {a ℓ r : Level} {A : Set a} {_<_ : Rel A r} (wf : WellFounded _<_)
      (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P) (_≣_ : {a : A} → Rel (P a) ℓ)
      (f-ext : (x : A) {IH IH′ : WfRec _<_ P x} → (∀ {y} y<x → (IH y y<x) ≣ (IH′ y y<x)) → (f x IH) ≣ (f x IH′))
      where
        some-wfRec-irrelevant : ∀ x → (q q′ : Acc _<_ x) → Some.wfRec P f x q ≣ Some.wfRec P f x q′
        some-wfRec-irrelevant = All.wfRec wf _
                                          (λ x → (q q′ : Acc _<_ x) → Some.wfRec P f x q ≣ Some.wfRec P f x q′)
                                          (λ { x IH (acc rs) (acc rs′) → f-ext x (λ y<x → IH _ y<x (rs _ y<x) (rs′ _ y<x)) })

        open Helper.All wf ℓ
        wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder P f x y y<x ≣ wfRec P f y
        wfRecBuilder-wfRec {x} {y} y<x with wf x
        ... | acc rs = some-wfRec-irrelevant y (rs y y<x) (wf y)

        unfold-wfRec : ∀ {x} → wfRec P f x ≣ f x (λ y _ → wfRec P f y)
        unfold-wfRec {x} = f-ext x wfRecBuilder-wfRec

    -- Pointwise equality of Functions
    _≐_ : {A B : Set} → (A → B) → (A → B) → Set
    _≐_ {A} f g = ∀ (x : A) → f x ≡ g x

    elementwise-eq : (x : ℕ) {IH IH' : WfRec _<ₙ_ P x} → ({y : ℕ} (y<x : y <ₙ x) → IH y y<x ≐ IH' y y<x) → Implementation.<-step x IH ≐ Implementation.<-step x IH'
    elementwise-eq zero            {IH} {IH'} rec [] = ≡-refl
    elementwise-eq (suc zero)      {IH} {IH'} rec xs = ≡-refl
    elementwise-eq n@(suc (suc m)) {IH} {IH'} rec xs = proof
      where
        proof : merge (IH  ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) (left-half xs))
                      (IH  ⌈ n /2⌉ (⌈n/2⌉<n      m ) (right-half xs))
              ≡
                merge (IH' ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) (left-half xs))
                      (IH' ⌈ n /2⌉ (⌈n/2⌉<n      m ) (right-half xs))
        proof = cong₂ merge eqₗ eqᵣ
          where
            -- Split the proof into two parts, showing equality of the left and right arguments separately
            eqₗ : IH ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) (left-half xs)  ≡ IH' ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) (left-half xs)
            eqₗ = rec (⌊n/2⌋<n (suc m)) (left-half xs)

            eqᵣ : IH ⌈ n /2⌉ (⌈n/2⌉<n      m ) (right-half xs) ≡ IH' ⌈ n /2⌉ (⌈n/2⌉<n      m ) (right-half xs)
            eqᵣ = rec (⌈n/2⌉<n      m ) (right-half xs)

  open CoolerFixPoint <-wellFounded P Implementation.<-step _≐_ elementwise-eq

  def-eq : {n : ℕ} → mergesort {n} ≐ Implementation.<-step n (λ m _ → mergesort {m})
  def-eq = unfold-wfRec

  def-eq₂ : {n : ℕ} → (xs : Vec C (suc (suc n))) → mergesort xs ≡ merge (mergesort (left-half xs)) (mergesort (right-half xs))
  def-eq₂ {n} xs = def-eq xs

  -- ******************************
  -- **  ORDEREDNESS PROPERTIES  **
  -- ******************************
  -- The predicate _≤ₕ_ states that the first argument is no larger than the head of the list (second argument), if the list is non-empty
  infix 4 _≤ₕ_
  data _≤ₕ_ : C → Vec C n → Set where
    ≤ₕ-nil  : {x : C}                            → x ≤ₕ []
    ≤ₕ-cons : {x y : C} → {ys : Vec C n} → x ≤ y → x ≤ₕ (y ∷ ys)

  -- Predicate that states that a given vector is sorted using _≤ₕ_
  data IsSorted  : Vec C n → Set where
    nil-sorted  : IsSorted []
    cons-sorted : {x : C} {ys : Vec C m} → x ≤ₕ ys → IsSorted (ys) → IsSorted (x ∷ ys)

  private
    ≤ₕ-list-head : {x : C} {xs : Vec C n} → x ≤ₕ (x ∷ xs)
    ≤ₕ-list-head = ≤ₕ-cons refl

    ≤ₕ-merge : {x : C} → (us : Vec C m) → (vs : Vec C n) → x ≤ₕ us → x ≤ₕ vs → x ≤ₕ merge us vs
    ≤ₕ-merge []       vs       p q = q
    ≤ₕ-merge (u ∷ us) []       p q = p
    ≤ₕ-merge (u ∷ us) (v ∷ vs) p q with u ≤? v
    ≤ₕ-merge (u ∷ us) (v ∷ vs) (≤ₕ-cons p) q | yes _ = ≤ₕ-cons p
    ≤ₕ-merge (u ∷ us) (v ∷ vs) p (≤ₕ-cons q) | no  _ = ≤ₕ-cons q

  merge-keeps-sorted : (us : Vec C n) → (vs : Vec C m) → IsSorted us → IsSorted vs → IsSorted (merge us vs)
  merge-keeps-sorted []       vs       _ q = q
  merge-keeps-sorted (u ∷ us) []       p _ = p
  merge-keeps-sorted (u ∷ us) (v ∷ vs) _ _ with u ≤? v
  merge-keeps-sorted (u ∷ us) (v ∷ vs) (cons-sorted u≤ₕus p) q | yes u≤v = cons-sorted (≤ₕ-merge us (v ∷ vs) u≤ₕus (≤ₕ-cons u≤v)) (merge-keeps-sorted us (v ∷ vs) p q)
  merge-keeps-sorted (u ∷ us) (v ∷ vs) p (cons-sorted v≤ₕvs q) | no  u≰v = cons-sorted (≤ₕ-merge (u ∷ us) vs (≤ₕ-cons v≤u) v≤ₕvs) (merge-keeps-sorted (u ∷ us) vs p q)
    where
      v≤u : v ≤ u
      v≤u = ≰⇒≥ dto u≰v -- somehow, this didn't work inline. Maybe it needed some type hinting?

  mergesort-sorts : (us : Vec C n) → IsSorted (mergesort us)
  mergesort-sorts {n} us = mergesort-sorts-int n us
    where
      mergesort-sorts-int : (n : ℕ) → (us : Vec C n) → IsSorted (mergesort us)
      mergesort-sorts-int = <-rec _ <-stepₛ
        where
          <-stepₛ : _
          <-stepₛ zero            _   _        = nil-sorted
          <-stepₛ (suc zero)      _   (x ∷ []) = cons-sorted ≤ₕ-nil nil-sorted
          <-stepₛ n@(suc (suc m)) rec xs       rewrite def-eq₂ xs =
                                                       merge-keeps-sorted (mergesort (left-half xs))                     (mergesort (right-half xs))
                                                                          (rec ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) (left-half xs)) (rec ⌈ n /2⌉ (⌈n/2⌉<n m) (right-half xs))

  -- ******************************
  -- **  PERMUTATION PROPERTIES  **
  -- ******************************
  -- Proofs that merge and mergesort produce permutations of the inputs as a result
  countₑ : C → Vec C n → ℕ
  countₑ x []       = 0
  countₑ x (u ∷ us) with x ≟ u
  ...                  | yes _ = ℕ.suc (countₑ x us)
  ...                  | no  _ = countₑ x us

  -- Dependent type for bag equivalence:
  -- u and v are equivalent; u ≅ v ⇔ for all elements x of type C, the number of occurrances
  --                                 of x in u is equal to the number of occurances of x in v.
  infix 4 _≅_
  _≅_ : (u : Vec C n) → (v : Vec C n) → Set
  u ≅ v = ∀ {x : C} → countₑ x u ≡ countₑ x v

  private
    -- First show that ≅ is a equivalence relation
    ≅-refl : (us : Vec C m) → us ≅ us
    ≅-refl us = ≡-refl

    ≅-sym : {us vs : Vec C m} → us ≅ vs → vs ≅ us
    ≅-sym {us} {vs} p {x} = sym p

    ≅-trans : {us vs ws : Vec C m} → us ≅ vs → vs ≅ ws → us ≅ ws
    ≅-trans {us} {vs} {ws} p q {x} = ≡-trans p q

    -- Some helper lemmas
    ≡⇒≅ : {us vs : Vec C m} → us ≡ vs → us ≅ vs
    ≡⇒≅ p {x} = cong (λ v → countₑ x v) p

    ++-count : (us : Vec C m) → (vs : Vec C n) → (x : C) → countₑ x (us ++ vs) ≡ countₑ x us + countₑ x vs
    ++-count []       vs x            = ≡-refl
    ++-count (u ∷ us) vs x with x ≟ u | ++-count us vs x
    ...                            | yes _ | p = cong ℕ.suc p
    ...                            | no  _ | p = p

    ∷-count : (u : C) → (us : Vec C m) → (x : C) → countₑ x (u ∷ us) ≡ countₑ x (u ∷ []) + countₑ x us
    ∷-count u us x with x ≟ u
    ...               | yes _ = ≡-refl
    ...               | no  _ = ≡-refl

    ∷-perm : (u : C) → {us vs : Vec C m} → us ≅ vs → (u ∷ us) ≅ (u ∷ vs)
    ∷-perm u {us} {vs} p {x} with x ≟ u
    ...                         | yes _ = cong ℕ.suc p
    ...                         | no  _ = p

    vec++[] : (us : Vec C m) → us ++ [] ≡ us
    vec++[] []       = ≡-refl
    vec++[] (u ∷ us) = cong (_∷_ u) (vec++[] us)

    ≅-insert-between : (us : Vec C m) → (vs : Vec C n) → (x : C) → x ∷ us ++ vs ≅ us ++ x ∷ vs
    ≅-insert-between us vs x {z} = begin
      countₑ z (x ∷ us ++ vs)                         ≡⟨ ++-count (x ∷ us) vs z ⟩
      countₑ z (x ∷ us) + countₑ z vs                 ≡⟨ cong (λ v → v + countₑ z vs) (∷-count x us z) ⟩
      countₑ z (x ∷ []) + countₑ z us + countₑ z vs   ≡⟨ cong (λ v → v + countₑ z vs) (+-comm (countₑ z (x ∷ [])) (countₑ z us)) ⟩
      countₑ z us +  countₑ z (x ∷ []) + countₑ z vs  ≡⟨ +-assoc (countₑ z us) (countₑ z (x ∷ [])) (countₑ z vs) ⟩
      countₑ z us + (countₑ z (x ∷ []) + countₑ z vs) ≡˘⟨ cong (λ v → countₑ z us + v) (∷-count x vs z) ⟩
      countₑ z us +  countₑ z (x ∷ vs)                ≡˘⟨ ++-count us (x ∷ vs) z ⟩
      countₑ z (us ++ x ∷ vs)                         ∎

    ≅-combine : {us vs : Vec C m} → {ws xs : Vec C n} → (p : us ≅ vs) → (q : ws ≅ xs) → us ++ ws ≅ vs ++ xs
    ≅-combine {_} {_} {us} {vs} {ws} {xs} p q {x} = begin
          countₑ x (us ++ ws)       ≡⟨ ++-count us ws x ⟩
          countₑ x us + countₑ x ws ≡⟨ cong (λ v → countₑ x us + v) (q {x}) ⟩
          countₑ x us + countₑ x xs ≡⟨ cong (λ v → v + countₑ x xs) (p {x}) ⟩
          countₑ x vs + countₑ x xs ≡˘⟨ ++-count vs xs x ⟩
          countₑ x (vs ++ xs)       ∎

  -- Merging vectors `us` and `vs` results in a permutation of the combined inputs, i.e. of `us ++ vs`
  merge-permutes : (us : Vec C m) → (vs : Vec C n) → (us ++ vs) ≅ (merge us vs)
  merge-permutes []          vs                          = ≅-refl vs
  merge-permutes us@(_ ∷ xs) []       rewrite vec++[] xs = ≅-refl us
  merge-permutes (u ∷ us)    (v ∷ vs) with u ≤? v
  ...                                    | yes u≤v = ∷-perm u (merge-permutes us (v ∷ vs))
  ...                                    | no  u≰v = ≅-trans (≅-sym (≅-insert-between (u ∷ us) vs v)) (∷-perm v (merge-permutes (u ∷ us) vs))

  mergesort-permutes : (xs : Vec C n) → xs ≅ (mergesort xs)
  mergesort-permutes {n} xs = mergesort-permutes-int n xs
    where
      mergesort-permutes-int : (n : ℕ) → (xs : Vec C n) → xs ≅ (mergesort xs)
      mergesort-permutes-int = <-rec _ <-stepₚ
        where
          <-stepₚ : _
          <-stepₚ zero            _   []             = ≡-refl
          <-stepₚ (suc n)         _   (x ∷ [])       = ≡-refl
          <-stepₚ n@(suc (suc m)) rec xs@(_ ∷ _ ∷ _) rewrite def-eq₂ xs with splitAt ⌊ n /2⌋ {⌈ n /2⌉} xs
          ... | (left , right , xs≡left++right) = ≅-trans {n} {xs} {left ++ right}
                                                    {merge (mergesort left) (mergesort right)}
                                                      (≡⇒≅ xs≡left++right)
                                                      (≅-trans {n} {left ++ right} {mergesort left ++ mergesort right} {merge (mergesort left) (mergesort right)}
                                                        (≅-combine {_} {_} {left} {mergesort left} {right} {mergesort right}
                                                          (rec ⌊ n /2⌋ (⌊n/2⌋<n (suc m)) left) (rec ⌈ n /2⌉ (⌈n/2⌉<n m) right))
                                                        (merge-permutes (mergesort left) (mergesort right)))


open Verification public
