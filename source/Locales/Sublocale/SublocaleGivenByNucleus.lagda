---
title:        Sublocale given by a nucleus
author:       ["Ian Ray", "Ayberk Tosun"]
date-started: 2024-06-20
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.Sublocale.SublocaleGivenByNucleus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext) where

open import Locales.Frame pt fe hiding (𝟚)
open import Locales.Nucleus pt fe
open import Slice.Family

open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open Locale

\end{code}

\section{Preliminaries}

Given a locale `X` and endofunction `j : 𝒪X → 𝒪X`, we say that an open
`U : 𝒪 X` is `j`-stable if it is a fixed point of `j`.

\begin{code}

module Fixsets (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 is-[_]-stable : (j : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → ⟨ 𝒪 X ⟩ → 𝓤 ⁺  ̇
 is-[ j ]-stable U = j U ＝ U

\end{code}

The type of `j`-stable opens of `X` is denoted `Fixset`.

\begin{code}

 Fixset : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → 𝓤 ⁺  ̇
 Fixset j = Σ U ꞉ ⟨ 𝒪 X ⟩ , is-[ j ]-stable U

\end{code}

We work in a module parameterized by a locale `X` and nucleus `j` on it.

\begin{code}

module Construction-Of-Sublocale (X : Locale (𝓤 ⁺) 𝓤 𝓤) (𝒿 : Nucleus (𝒪 X)) where

 private
  j = pr₁ 𝒿

 open Fixsets X

\end{code}

The ordering on `j`-stable opens is the same as the one from `𝒪 X`.

\begin{code}

 _≤∙_ : Fixset j → Fixset j → Ω 𝓤
 (U , _) ≤∙ (V , _) = U ≤[ poset-of (𝒪 X) ] V

\end{code}

The top open is the top open of `X`, which is always `j`-stable.

\begin{code}

 open Properties-Of-Nuclei (𝒪 X)

 𝟏∙ : Fixset j
 𝟏∙ = 𝟏[ 𝒪 X ] , nucleus-preserves-top 𝒿

\end{code}

The binary meet of two `j`-stable opens.

\begin{code}

 _∧∙_ : Fixset j → Fixset j → Fixset j
 (U , p) ∧∙ (V , q) = (U ∧[ 𝒪 X ] V) , †
  where
   † : is-[ j ]-stable (U ∧[ 𝒪 X ] V)
   † = j (U ∧[ 𝒪 X ] V)   ＝⟨ Ⅰ ⟩
       j U ∧[ 𝒪 X ] j V   ＝⟨ Ⅱ ⟩
       U ∧[ 𝒪 X ] j V     ＝⟨ Ⅲ ⟩
       U ∧[ 𝒪 X ] V       ∎
        where
         Ⅰ = 𝓃₃ (𝒪 X) 𝒿 U V
         Ⅱ = ap (λ - → - ∧[ 𝒪 X ] j V) p
         Ⅲ = ap (λ - → U ∧[ 𝒪 X ] -) q

\end{code}

\begin{code}

 fixset-frame-structure : frame-structure 𝓤 𝓤 (Fixset j)
 fixset-frame-structure = (_≤∙_ , 𝟏∙ , {!!}) , {!!}

 sublocale : Locale (𝓤 ⁺) 𝓤 𝓤
 sublocale =
  record { ⟨_⟩ₗ = Fixset j ; frame-str-of = fixset-frame-structure }

\end{code}
