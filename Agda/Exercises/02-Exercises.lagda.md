# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (x , y) = f x y

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = (inl a) , (inl b)
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[ii] (inl (a , b)) = (inl a) , (inl b)
[ii] (inr c) = (inr c) , (inr c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] p = (λ a → p (inl a)) , (λ a → p (inr a))

-- [iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
-- [iv] p = {!!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f x a = x (f a)

-- [vi] : {A B : Type} → (¬ A → ¬ B) → B → A
-- [vi] = {!!}

-- [vii] : {A B : Type} → ((A → B) → A) → A
-- [vii] f = f λ a → {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] p a x = p (a , x)

-- [ix] : {A : Type} {B : A → Type}
--    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
-- [ix] p = {!p ?!} , {!!}

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] p = (λ a → p a .pr₁) , λ a → p a .pr₂
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne p a = p λ a' → a' a
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f x b = x λ a → b (f a)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f ¬¬a b = ¬¬a λ a → (f a) b
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ true .true (refl .true) = (λ x → x) , (λ x → x)
bool-≡-char₁ false .false (refl .false) = (λ x → x) , (λ x → x)
```


### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false p = pr₁ (bool-≡-char₁ true false p) ⋆

true≢false₂ : ¬ (true ≡ false)
true≢false₂ ()

true≠false₃ : ¬ (true ≡ false)
true≠false₃ p = transport bool-as-type p ⋆
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (l , r) = refl true
bool-≡-char₂ true false (l , r) = 𝟘-nondep-elim (l ⋆)
bool-≡-char₂ false true (l , r) = 𝟘-nondep-elim (r ⋆)
bool-≡-char₂ false false (l , r) = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```
Prove that
```agda
is-decidable→Bool : {A : Type} → is-decidable A → Bool
is-decidable→Bool (inl x) = true
is-decidable→Bool (inr x) = false

is-decideableTrue : {A : Type} (a : A) (x : is-decidable A) → is-decidable→Bool x ≡ true
is-decideableTrue a (inl x) = refl true
is-decideableTrue a (inr x) = 𝟘-nondep-elim (x a)

is-decideableProj : {A : Type} (x : is-decidable A) → is-decidable→Bool x ≡ true → A
is-decideableProj (inl x) p = x

decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A = (λ {p → (λ x y → is-decidable→Bool (p x y)) , help p})
                          , λ { (f , p) y z → main f y z p (charac (f y z))}
  where
  main : (f : A → A → Bool) (y z : A) → ((x y₁ : A) → x ≡ y₁ ⇔ f x y₁ ≡ true)
    → is-decidable (f y z ≡ true) → is-decidable (y ≡ z)
  main f y z p (inl x) = inl (p y z .pr₂ x)
  main f y z p (inr x) = inr λ q → x (p y z .pr₁ q)

  charac : (x : Bool) → is-decidable (x ≡ true)
  charac true = inl (refl true)
  charac false = inr λ ()

  help : (p : has-decidable-equality A) → (x y : A) → x ≡ y ⇔ is-decidable→Bool (p x y) ≡ true
  pr₁ (help p x .x) (refl .x) = is-decideableTrue (refl x) (p x x)
  pr₂ (help p x y) l = is-decideableProj (p x y) l

```
