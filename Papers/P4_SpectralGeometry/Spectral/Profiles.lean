/-
Copyright (c) 2025 Paul Chun-Kit Lee. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Paul Chun-Kit Lee
-/

/-!
# Paper 4: Quantum Spectra — Profiles / Height mini-algebra

We keep a tiny height lattice with {0, 1, ω} and a componentwise
"max" on 3-axis profiles (WLPO, FT, DCω). This mirrors the paper's
height/product law at a purely structural level.
-/

namespace Papers.P4_SpectralGeometry.Spectral

inductive Height : Type
| h0  -- constructive core
| h1  -- next step on an axis (e.g., needs Token)
| hω  -- limit placeholder (e.g., at ω or beyond)
deriving DecidableEq, Repr

namespace Height

/-- Partial order as a relation; enough for our use (no full `LE` instance needed). -/
def le : Height → Height → Prop
| h0, _  => True
| h1, h0 => False
| h1, _  => True
| hω, hω => True
| hω, _  => False

@[simp] theorem le_refl (h : Height) : le h h := by
  cases h <;> simp [le]

@[simp] theorem le_h0 (h : Height) : le h h0 ↔ h = h0 := by
  cases h <;> simp [le]

@[simp] theorem h0_le (h : Height) : le h0 h := by
  cases h <;> simp [le]

/-- Max for our 3-values lattice. -/
def max : Height → Height → Height
| h0, b  => b
| h1, h0 => h1
| h1, h1 => h1
| h1, hω => hω
| hω, _  => hω

@[simp] theorem max_h0 (h : Height) : max h0 h = h := by cases h <;> rfl
@[simp] theorem h0_max (h : Height) : max h h0 = h := by cases h <;> rfl
@[simp] theorem max_self (h : Height) : max h h = h := by cases h <;> rfl

theorem max_comm (a b : Height) : max a b = max b a := by
  cases a <;> cases b <;> rfl

theorem max_assoc (a b c : Height) :
  max (max a b) c = max a (max b c) := by
  cases a <;> cases b <;> cases c <;> rfl

end Height

/-- 3-axis profile: (WLPO, FT, DCω). -/
structure Profile where
  hWLPO : Height
  hFT   : Height
  hDCω  : Height
deriving Repr

namespace Profile

/-- Componentwise max (product law skeleton). -/
def max (p q : Profile) : Profile where
  hWLPO := Height.max p.hWLPO q.hWLPO
  hFT   := Height.max p.hFT   q.hFT
  hDCω  := Height.max p.hDCω  q.hDCω

theorem max_comm (p q : Profile) : max p q = max q p := by
  cases p; cases q; simp [max, Height.max_comm]

theorem max_assoc (p q r : Profile) :
  max (max p q) r = max p (max q r) := by
  cases p; cases q; cases r; simp [max, Height.max_assoc]

/-- Shorthands for the paper's canonical calibrators. -/
def WLPO_only : Profile := ⟨Height.h1, Height.h0, Height.h0⟩
def FT_only   : Profile := ⟨Height.h0, Height.h1, Height.h0⟩
def DCω_only  : Profile := ⟨Height.h0, Height.h0, Height.h1⟩
def all_zero  : Profile := ⟨Height.h0, Height.h0, Height.h0⟩

@[simp] theorem max_all_zero_left  (p : Profile) : max all_zero p = p := by
  cases p with
  | mk hW hF hD => simp [max, all_zero, Height.max_h0]
@[simp] theorem max_all_zero_right (p : Profile) : max p all_zero = p := by
  cases p with
  | mk hW hF hD => simp [max, all_zero, Height.h0_max]

end Profile

end Papers.P4_SpectralGeometry.Spectral