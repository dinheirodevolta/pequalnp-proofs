/-
SPDX-License-Identifier: Apache-2.0
Adapted from the pequalnp-proofs circuit extraction and rectangle arguments.
This version adds arbitrary sample domains, a graph criterion, and a sharp infinite family.
The repository LICENSE applies. Sources are cited in research/one-hot-rectangles/note.pdf.
-/
import PEqualNP.Defs.Represents

/-!
# Forced inputs and rectangle lower bounds

A monotone circuit of size `s` can leave at most `s+1` distinct input
signatures live when its gates are traced backwards from the output. At
equality the live signatures admit a Karchmer–Wigderson rectangle protocol.
Two forced rectangles that collide disprove equality.

The lemmas about live signatures and protocols adapt the argument for mask
301 in L_meta_5522 and the frontier argument in L_meta_3885.
-/

namespace PEqualNP.RectangleBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical
noncomputable section

variable {R : Type}
abbrev Signature (R : Type) := R → Bool

/-- The first sample is positive and the second negative for this signature. -/
def Separates (w : Signature R) (p q : R) := w p = true ∧ w q = false

/-- Every available input signature separating this pair has the specified value. -/
def Forced (T : Signature R) (inputs : List (Signature R)) (w : Signature R) (p q : R) :=
  T p = true ∧ T q = false ∧ ∀ v ∈ inputs, Separates v p q → v = w

/-- Two pairs force each of two distinct labels, with a common rectangle corner. -/
def Clash (T : Signature R) (inputs : List (Signature R)) :=
  ∃ (a b : Signature R) (p u v q r s : R), a ≠ b ∧ Forced T inputs a p u ∧
    Forced T inputs b p v ∧ Forced T inputs a r q ∧ Forced T inputs b s q

private def combine (isOr : Bool) (a b : Signature R) : Signature R :=
  fun p => if isOr then a p || b p else a p && b p

private def Available (inputs : List (Signature R)) (w : Signature R) :=
  w ∈ inputs ∨ ∃ b : Bool, w = fun _ => b

private def wire (w : List (Signature R)) (i : ℕ) : Signature R :=
  w.getD i (fun _ => false)

private def gateSig (w : List (Signature R)) (g : Gate) : Signature R :=
  fun p => g.op.eval (g.inputs.map (fun i => wire w i p))

private def run (gs : List Gate) (w : List (Signature R)) : List (Signature R) :=
  gs.foldl (fun l g => l ++ [gateSig l g]) w

private lemma get_available (w : List (Signature R)) (i : ℕ) : Available w (wire w i) := by
  unfold wire
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr ⟨false, rfl⟩
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma gate_cases (w : List (Signature R)) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Available w (gateSig w g) ∨ ∃ d a b, Available w a ∧ Available w b ∧
      gateSig w g = combine d a b := by
  obtain ⟨op,l⟩ := g
  obtain ⟨ho,hlen⟩ := hg
  change op ∈ ({GateOp.and,GateOp.or} : Set GateOp) at ho
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho
  change l.length ≤ 2 at hlen
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl (Or.inr ⟨true, rfl⟩)
    · exact Or.inl (Or.inr ⟨false, rfl⟩)
  | cons i t =>
    cases t with
    | nil =>
      have e : gateSig w ⟨op,[i]⟩ = wire w i := by
        rcases ho with rfl | rfl <;> funext p <;> simp [gateSig,GateOp.eval]
      exact Or.inl (e ▸ get_available w i)
    | cons j t =>
      cases t with
      | cons a l => simp at hlen
      | nil =>
        apply Or.inr
        rcases ho with rfl | rfl
        · refine ⟨false, _, _, get_available w i, get_available w j, ?_⟩
          funext p
          simp [gateSig,GateOp.eval,combine]
        · refine ⟨true, _, _, get_available w i, get_available w j, ?_⟩
          funext p
          simp [gateSig,GateOp.eval,combine]

private inductive Live (T : Signature R) : ℕ → Finset (Signature R) → Prop where
  | stop : Live T 0 {T}
  | step {k U a b d} (fresh : combine d a b ∉ insert a (insert b U))
      (next : Live T k (insert (combine d a b) U)) : Live T (k+1) (insert a (insert b U))

private lemma live_size {T : Signature R} {k S} (h : Live T k S) : S.card ≤ k+1 := by
  induction h with
  | stop => simp
  | @step k U a b d fresh _ ih =>
    have hu : combine d a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have := Finset.card_insert_le a (insert b U)
    have := Finset.card_insert_le b U
    omega

private lemma available_snoc {z v : Signature R} {w : List (Signature R)}
    (h : Available (w ++ [z]) v) : Available w v ∨ v = z := by
  unfold Available at h ⊢
  simpa only [List.mem_append, List.mem_singleton] using
    (show ((v ∈ w ∨ v = z) ∨ ∃ c : Bool, v = fun _ => c) →
       ((v ∈ w ∨ ∃ c : Bool, v = fun _ => c) ∨ v = z) from
       fun hh => hh.elim (fun hh => hh.elim (fun e => Or.inl (Or.inl e)) Or.inr)
         (fun e => Or.inl (Or.inr e))) (by simpa using h)

private lemma pull {T z : Signature R} {k S} {w : List (Signature R)} (run' : Live T k S)
    (hc : Available w z ∨ ∃ d a b, Available w a ∧ Available w b ∧ z = combine d a b)
    (supply : ∀ v ∈ S, Available (w ++ [z]) v) :
    ∃ k' S', k' ≤ k+1 ∧ Live T k' S' ∧ ∀ v ∈ S', Available w v := by
  by_cases hz : z ∈ S
  · by_cases hav : Available w z
    · refine ⟨k,S,by omega,run',?_⟩
      intro v hv
      exact (available_snoc (supply v hv)).elim id (fun e => e ▸ hav)
    · obtain ⟨d,a,b,ha,hb,rfl⟩ := hc.resolve_left hav
      let U := S.erase (combine d a b)
      have tail : Live T k (insert (combine d a b) U) := by simpa [U,Finset.insert_erase hz] using run'
      have old (v : Signature R) (hv : v ∈ U) : Available w v := by
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hv
        exact (available_snoc (supply v mem)).resolve_right ne
      have fresh : combine d a b ∉ insert a (insert b U) := by
        intro hm
        rcases Finset.mem_insert.mp hm with e | hm
        · exact hav (e.symm ▸ ha)
        rcases Finset.mem_insert.mp hm with e | hm
        · exact hav (e.symm ▸ hb)
        · exact hav (old _ hm)
      refine ⟨k+1,insert a (insert b U),by omega,Live.step fresh tail,?_⟩
      simpa only [Finset.forall_mem_insert] using And.intro ha (And.intro hb old)
  · refine ⟨k,S,by omega,run',?_⟩
    intro v hv
    exact (available_snoc (supply v hv)).resolve_right (fun e => hz (e ▸ hv))

private lemma extract {T : Signature R} (gs : List Gate) (w : List (Signature R))
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (found : Available (run gs w) T) :
    ∃ k S, k ≤ gs.length ∧ Live T k S ∧ ∀ v ∈ S, Available w v := by
  induction gs generalizing w with
  | nil => exact ⟨0,{T},by simp,Live.stop,by simpa [run] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,hl,hs⟩ := ih (w ++ [gateSig w g]) (fun x hx => legal x (by simp [hx])) found
    obtain ⟨l,Z,hb,hz,hw⟩ := pull hl (gate_cases w g (legal g (by simp))) hs
    exact ⟨l,Z,by simp; omega,hz,hw⟩

private lemma read_wire (p : R) (w : List (Signature R)) (j : ℕ) :
    (w.map (fun f => f p)).getD j false = wire w j p := by
  simp only [wire,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> rfl

private lemma run_values (gs : List Gate) (p : R) (w : List (Signature R)) :
    (run gs w).map (fun f => f p) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (fun f => f p)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [gateSig w g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,gateSig,read_wire]

private lemma distinguishing {T : Signature R} {k S} (h : Live T k S) {p q : R}
    (ht : Separates T p q) : ∃ v ∈ S, Separates v p q := by
  induction h with
  | stop => exact ⟨_, by simp, ht⟩
  | @step k U a b d _ _ ih =>
    obtain ⟨v,hv,sp⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | mem
    · rcases sp with ⟨hp,hq⟩
      cases d <;> cases h1 : a p <;> cases h2 : a q <;> cases h3 : b p <;> cases h4 : b q <;>
        simp_all [combine,Separates]
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),sp⟩

private def Protocol (T : Signature R) (S : Finset (Signature R)) : Prop :=
  ∃ f : R → R → Signature R, (∀ p q, f p q ∈ S) ∧
    (∀ p q, Separates T p q → Separates (f p q) p q) ∧
    ∀ p q r s, f p q = f r s → f p s = f p q

private def pick (d : Bool) (a b : Signature R) (p q : R) :=
  if (if d then a p else !(a q)) then a else b

private lemma pick_mem (d : Bool) (a b : Signature R) (p q : R) :
    pick d a b p q = a ∨ pick d a b p q = b := by
  cases d <;> cases hp : a p <;> cases hq : a q <;> simp [pick, hp, hq]

private lemma pick_sep {a b : Signature R} {d p q} (h : Separates (combine d a b) p q) :
    Separates (pick d a b p q) p q := by
  cases d <;> cases hp : a p <;> cases hq : a q <;> simp_all [pick,Separates,combine]

private lemma refine_protocol {T a b : Signature R} {U d} (an : a ∉ U) (bn : b ∉ U)
    (h : Protocol T (insert (combine d a b) U)) : Protocol T (insert a (insert b U)) := by
  obtain ⟨f,mem,sep,rect⟩ := h
  let z := combine d a b
  let g := fun p q => if f p q=z then pick d a b p q else f p q
  have undo (p q) : (if g p q=a ∨ g p q=b then z else g p q) = f p q := by
    by_cases hz : f p q=z
    · simp only [g,hz,ite_true,if_pos (pick_mem d a b p q)]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have ha : f p q ≠ a := fun e => an (e ▸ hu)
      have hb : f p q ≠ b := fun e => bn (e ▸ hu)
      simp [g,hz,ha,hb]
  refine ⟨g,?_,?_,?_⟩
  · intro p q
    by_cases hz : f p q=z
    · rcases pick_mem d a b p q with e | e <;> simp [g,hz,e]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      simp only [g, hz, ite_false]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
  · intro p q st
    by_cases hz : f p q=z
    · have hh : Separates z p q := by rw [←hz]; exact sep p q st
      simpa [g,hz] using pick_sep (d:=d) (a:=a) (b:=b) hh
    · simpa [g,hz] using sep p q st
  · intro p q r s e
    have eo : f p q=f r s := by rw [← undo p q,← undo r s,e]
    have ec := rect p q r s eo
    by_cases hz : f p q=z
    · have ht : f r s=z := eo.symm.trans hz
      have ep : pick d a b p q=pick d a b r s := by simpa only [g,hz,ht,ite_true] using e
      simp only [g,ec,hz,ite_true]
      cases d
      · exact ep.symm
      · rfl
    · simp [g,ec,hz]

private lemma tight_protocol {T : Signature R} {k S} (hl : Live T k S)
    (tight : k+1 ≤ S.card) : Protocol T S := by
  induction hl with
  | stop => exact ⟨fun _ _ => T,fun _ _ => Finset.mem_singleton_self _,fun _ _ => id,fun _ _ _ _ _ => rfl⟩
  | @step k U a b d fresh next ih =>
    have zu : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have sz := live_size next
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le a (insert b U)
    have y := Finset.card_insert_le b U
    have an : a ∉ U := by
      intro am
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at tight
      omega
    have bn : b ∉ U := by
      intro bm
      rw [Finset.insert_eq_of_mem bm] at tight x
      omega
    apply refine_protocol an bn
    apply ih
    rw [Finset.card_insert_of_notMem zu]
    omega

private lemma input_of_sep {w : Signature R} {inputs p q}
    (h : Available inputs w) (s : Separates w p q) : w ∈ inputs := by
  rcases h with mem | ⟨c,rfl⟩
  · exact mem
  · exact Bool.noConfusion (s.1.symm.trans s.2)

/-- A certificate consisting of forced inputs and a rectangle collision proves a gate lower bound
    for a monotone circuit on an arbitrary promise domain. Each element of `inputs` is one input
    wire's Boolean signature on this domain. -/
theorem lower_of_clash (T : Signature R) (inputs : List (Signature R))
    (C : Circuit) (required : Finset (Signature R)) (mono : Monotone2 C)
    (correct : ∀ p, C.eval (inputs.map (fun w => w p)) = T p)
    (pins : ∀ w ∈ required, ∃ p q, Forced T inputs w p q) (collision : Clash T inputs) :
    required.card ≤ C.size := by
  have table : wire (run C.gates inputs) C.output = T := by
    funext p
    rw [←read_wire,run_values]
    exact correct p
  obtain ⟨k,S,hk,hl,hs⟩ := extract C.gates inputs mono (table ▸ get_available _ _)
  have sub : required ⊆ S := by
    intro w hw
    obtain ⟨p,q,f⟩ := pins w hw
    obtain ⟨v,hv,sp⟩ := distinguishing hl (show Separates T p q from ⟨f.1,f.2.1⟩)
    exact (f.2.2 v (input_of_sep (hs v hv) sp) sp) ▸ hv
  by_contra! small
  change C.gates.length < required.card at small
  have size := Finset.card_le_card sub
  obtain ⟨f,mem,sep,rect⟩ := tight_protocol hl (by omega)
  obtain ⟨a,b,p,u,v,q,r,s,ne,w1,w2,w3,w4⟩ := collision
  have forcedChoice {z x y} (w : Forced T inputs z x y) : f x y = z := by
    have sp := sep x y ⟨w.1,w.2.1⟩
    exact w.2.2 _ (input_of_sep (hs _ (mem x y)) sp) sp
  have A := rect p u r q ((forcedChoice w1).trans (forcedChoice w3).symm)
  have B := rect p v s q ((forcedChoice w2).trans (forcedChoice w4).symm)
  exact ne ((A.trans (forcedChoice w1)).symm.trans (B.trans (forcedChoice w2)))

abbrev Cell (n m : ℕ) := Fin n × Fin m

def graphTable {n m : ℕ} (A : Fin n → Fin m → Bool) : Signature (Cell n m) :=
  fun p => A p.1 p.2

def inputTables (n m : ℕ) : List (Signature (Cell n m)) :=
  List.ofFn (fun u : Fin n => fun p : Cell n m => decide (u = p.1)) ++
  List.ofFn (fun v : Fin m => fun p : Cell n m => decide (v = p.2))

lemma inputTables_eval {n m : ℕ} (p : Cell n m) :
    (inputTables n m).map (fun w => w p) = oneEach p.1 p.2 := by
  simp only [inputTables,oneEach,List.map_append,List.map_ofFn,Function.comp_def]

/-- Rectangle certificate for an arbitrary finite bipartite graph under the one-hot promise. -/
theorem graph_lower_of_clash {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit)
    (required : Finset (Signature (Cell n m))) (mono : Monotone2 C) (rep : Represents A C)
    (pins : ∀ w ∈ required, ∃ p q, Forced (graphTable A) (inputTables n m) w p q)
    (collision : Clash (graphTable A) (inputTables n m)) :
    required.card ≤ C.size := by
  apply lower_of_clash (graphTable A) (inputTables n m) C required mono _ pins collision
  intro p
  rw [inputTables_eval]
  exact rep p.1 p.2

end
end PEqualNP.RectangleBound



namespace PEqualNP.RectangleBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical
noncomputable section

variable {n m : ℕ}

def rowSig (i : Fin n) : Signature (Cell n m) := fun p => decide (i = p.1)
def colSig (j : Fin m) : Signature (Cell n m) := fun p => decide (j = p.2)
def vertexSig : Fin n ⊕ Fin m → Signature (Cell n m) := Sum.elim rowSig colSig

/-- A row has a one in a column containing a zero, or the transposed condition holds. -/
def IsForcedVertex (A : Fin n → Fin m → Bool) : Fin n ⊕ Fin m → Prop
  | .inl i => ∃ j k, A i j = true ∧ A k j = false
  | .inr j => ∃ i l, A i j = true ∧ A i l = false

private instance vertexDecidable (A : Fin n → Fin m → Bool) (v : Fin n ⊕ Fin m) :
    Decidable (IsForcedVertex A v) := by
  cases v <;> unfold IsForcedVertex <;> infer_instance

def forcedVertices (A : Fin n → Fin m → Bool) : Finset (Fin n ⊕ Fin m) :=
  Finset.univ.filter (IsForcedVertex A)

/-- Three ones around a zero, with an additional zero in the central row and column.
    This is an induced four-vertex path after deleting globally universal vertices. -/
def HasResidualPath (A : Fin n → Fin m → Bool) : Prop :=
  ∃ i k z : Fin n, ∃ j l t : Fin m,
    A i j = true ∧ A i l = true ∧ A k j = true ∧ A k l = false ∧
    A z j = false ∧ A i t = false

private theorem row_forced (A : Fin n → Fin m → Bool) {i k j}
    (hi : A i j = true) (hk : A k j = false) :
    Forced (graphTable A) (inputTables n m) (rowSig i) (i,j) (k,j) := by
  refine ⟨hi, hk, ?_⟩
  intro w hw sep
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hw
    have e : u = i := of_decide_eq_true sep.1
    subst u
    rfl
  · obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hw
    exact Bool.noConfusion (sep.1.symm.trans sep.2)

private theorem col_forced (A : Fin n → Fin m → Bool) {i j l}
    (hj : A i j = true) (hl : A i l = false) :
    Forced (graphTable A) (inputTables n m) (colSig j) (i,j) (i,l) := by
  refine ⟨hj, hl, ?_⟩
  intro w hw sep
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hw
    exact Bool.noConfusion (sep.1.symm.trans sep.2)
  · obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hw
    have e : v = j := of_decide_eq_true sep.1
    subst v
    rfl

private theorem row_ne_col (i : Fin n) (j : Fin m) {c d : Fin m} (hcd : c ≠ d) :
    (rowSig i : Signature (Cell n m)) ≠ colSig j := by
  intro h
  have hc : j = c := by simpa [rowSig, colSig] using (congrFun h (i,c)).symm
  have hd : j = d := by simpa [rowSig, colSig] using (congrFun h (i,d)).symm
  exact hcd (hc.symm.trans hd)

private theorem vertexSig_injective (i : Fin n) {c d : Fin m} (hcd : c ≠ d) :
    Function.Injective (@vertexSig n m) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have eq : b = a := by simpa [vertexSig, rowSig] using (congrFun h (a,c)).symm
      exact congrArg Sum.inl eq.symm
    | inr b => exact (row_ne_col a b hcd h).elim
  | inr a =>
    cases y with
    | inl b => exact (row_ne_col b a hcd h.symm).elim
    | inr b =>
      have eq : b = a := by simpa [vertexSig, colSig] using (congrFun h (i,a)).symm
      exact congrArg Sum.inr eq.symm

/-- The adjacency pattern yields a collision of forced communication rectangles. -/
theorem clash_of_residual_path (A : Fin n → Fin m → Bool) (path : HasResidualPath A) :
    Clash (graphTable A) (inputTables n m) := by
  obtain ⟨i,k,z,j,l,t,hij,hil,hkj,hkl,hzj,hit⟩ := path
  have hjl : j ≠ l := by
    rintro rfl
    exact Bool.noConfusion (hkj.symm.trans hkl)
  exact ⟨rowSig i, colSig j, (i,j), (z,j), (i,t), (k,l), (i,l), (k,j),
    row_ne_col i j hjl, row_forced A hij hzj, col_forced A hij hit,
    row_forced A hil hkl, col_forced A hkj hkl⟩

/-- A graph-only lower bound. The right side counts gates of an arbitrary monotone binary circuit
    representing the table on every one-hot input pair. -/
theorem graph_lower_of_residual_path (A : Fin n → Fin m → Bool) (path : HasResidualPath A)
    (C : Circuit) (mono : Monotone2 C) (rep : Represents A C) :
    (forcedVertices A).card ≤ C.size := by
  have collision := clash_of_residual_path A path
  obtain ⟨i,k,z,j,l,t,hij,hil,hkj,hkl,hzj,hit⟩ := path
  have hjl : j ≠ l := by
    rintro rfl
    exact Bool.noConfusion (hkj.symm.trans hkl)
  let required := (forcedVertices A).image vertexSig
  have bound : required.card ≤ C.size := by
    apply graph_lower_of_clash A C required mono rep _ collision
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    have forced := (Finset.mem_filter.mp hv).2
    cases v with
    | inl u =>
      obtain ⟨c,b,hu,hb⟩ := forced
      exact ⟨(u,c), (b,c), row_forced A hu hb⟩
    | inr c =>
      obtain ⟨u,b,hc,hb⟩ := forced
      exact ⟨(u,c), (u,b), col_forced A hc hb⟩
  simpa only [required, Finset.card_image_of_injective _ (vertexSig_injective i hjl)] using bound

end
end PEqualNP.RectangleBound

namespace PEqualNP.RectangleBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- The original table follows from the graph criterion by six cell checks and a vertex count. -/
def mask301 (i j : Fin 4) : Bool := (301 : ℕ).testBit (4 * i.val + j.val)

theorem mask301_lower (C : Circuit) (mono : Monotone2 C) (rep : Represents mask301 C) :
    7 ≤ C.size := by
  have path : HasResidualPath mask301 :=
    ⟨0, 2, 1, 0, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have count : (forcedVertices mask301).card = 7 := by decide +kernel
  exact count ▸ graph_lower_of_residual_path mask301 path C mono rep

end PEqualNP.RectangleBound

namespace PEqualNP.RectangleBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- A four-vertex path and a matching of size t, joined by one extra row adjacent to every column. -/
def hubIncidence (t : ℕ) (i : Fin (t + 3)) (j : Fin (t + 2)) : Bool :=
  decide (i.val = t + 2 ∨ (i.val = 0 ∧ j.val ≤ 1) ∨
    (i.val = 1 ∧ j.val = 0) ∨ (2 ≤ i.val ∧ i.val = j.val))

theorem hubIncidence_path (t : ℕ) (ht : 1 ≤ t) : HasResidualPath (hubIncidence t) := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
    ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hubIncidence, decide_eq_true_eq, decide_eq_false_iff_not, true_and, and_true, or_true, true_or] <;> omega

theorem hubIncidence_forced (t : ℕ) (ht : 1 ≤ t) :
    ∀ v, IsForcedVertex (hubIncidence t) v := by
  intro v
  cases v with
  | inl i =>
    by_cases h : i.val ≤ 1 ∨ i.val = t + 2
    · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_⟩ <;>
        simp only [hubIncidence, decide_eq_true_eq, decide_eq_false_iff_not, true_and, and_true, or_true, true_or] <;> omega
    · have hi := i.isLt
      refine ⟨⟨i.val, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩ <;>
        simp only [hubIncidence, decide_eq_true_eq, decide_eq_false_iff_not, true_and, and_true, or_true, true_or] <;> omega
  | inr j =>
    by_cases h : j.val ≤ 1
    · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_⟩ <;>
        simp only [hubIncidence, decide_eq_true_eq, decide_eq_false_iff_not, true_and, and_true, or_true, true_or] <;> omega
    · have hj := j.isLt
      refine ⟨⟨j.val, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩ <;>
        simp only [hubIncidence, decide_eq_true_eq, decide_eq_false_iff_not, true_and, and_true, or_true, true_or] <;> omega

theorem hubIncidence_lower (t : ℕ) (ht : 1 ≤ t) (C : Circuit)
    (hm : Monotone2 C) (hr : Represents (hubIncidence t) C) :
    2 * t + 5 ≤ C.size := by
  classical
  have hall : forcedVertices (hubIncidence t) = Finset.univ := by
    ext v
    simp [forcedVertices, hubIncidence_forced t ht v]
  have bound := graph_lower_of_residual_path (hubIncidence t) (hubIncidence_path t ht) C hm hr
  rw [hall, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at bound
  omega

end PEqualNP.RectangleBound
namespace PEqualNP.RectangleBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private inductive HubExpr where
  | input (i : ℕ)
  | node (isOr : Bool) (a b : HubExpr)

private def HubExpr.cost : HubExpr → ℕ
  | .input _ => 0
  | .node _ a b => a.cost + b.cost + 1

private def HubExpr.within (n : ℕ) : HubExpr → Prop
  | .input i => i < n
  | .node _ a b => a.within n ∧ b.within n

private def HubExpr.value (x : List Bool) : HubExpr → Bool
  | .input i => x.getD i false
  | .node op a b => if op then a.value x || b.value x else a.value x && b.value x

private def HubExpr.compile (start : ℕ) : HubExpr → Circuit
  | .input i => ⟨[],i⟩
  | .node op a b =>
    let d := a.compile start
    let e := b.compile (start + a.cost)
    ⟨d.gates ++ e.gates ++ [⟨if op then .or else .and,[d.output,e.output]⟩],
      start + a.cost + b.cost⟩

private lemma HubExpr.compiled_size (f : HubExpr) (n : ℕ) :
    (f.compile n).size = f.cost := by
  induction f generalizing n with
  | input => rfl
  | node op a b ha hb =>
    change ((a.compile n).gates ++ (b.compile (n+a.cost)).gates ++ [_]).length = _
    simp only [List.length_append,List.length_singleton,HubExpr.cost]
    change (a.compile n).size + (b.compile (n+a.cost)).size + 1 = _
    rw [ha,hb]

private lemma HubExpr.compiled_mono (f : HubExpr) (n : ℕ) : Monotone2 (f.compile n) := by
  induction f generalizing n with
  | input i => simp [Monotone2,HubExpr.compile]
  | node op a b ha hb =>
    intro g hg
    change g ∈ (a.compile n).gates ++ (b.compile (n+a.cost)).gates ++ [_] at hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with (h | h) | rfl
    · exact ha n _ h
    · exact hb _ _ h
    · cases op <;> simp

private def hubRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map (fun i => a.getD i false))]) w

private lemma hubRun_extension (gs : List Gate) (w : List Bool) :
    ∃ u, hubRun gs w = w ++ u ∧ u.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [hubRun]⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => w.getD i false))
    obtain ⟨u,e,len⟩ := ih (w++[v])
    refine ⟨v::u,?_,by simp [len]⟩
    simpa [hubRun,v,List.append_assoc] using e

private lemma hubRun_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (hubRun gs w).getD i false = w.getD i false := by
  obtain ⟨u,e,_⟩ := hubRun_extension gs w
  rw [e,List.getD_append _ _ _ _ hi]

private lemma HubExpr.output_bound (f : HubExpr) {n : ℕ} (h : f.within n) {start : ℕ}
    (hs : n ≤ start) : (f.compile start).output < start + f.cost := by
  cases f with
  | input i => change i < start + 0; change i < n at h; omega
  | node op a b => change start + a.cost + b.cost < start + (a.cost + b.cost + 1); omega

private lemma HubExpr.eval_compile (f : HubExpr) (x w : List Bool)
    (h : f.within x.length) (hp : x.length ≤ w.length)
    (agrees : ∀ i < x.length, w.getD i false = x.getD i false) :
    let d := f.compile w.length
    (hubRun d.gates w).getD d.output false = f.value x := by
  induction f generalizing w with
  | input i => exact agrees i h
  | node op a b ha hb =>
    let d := a.compile w.length
    let v := hubRun d.gates w
    have hlen : v.length = w.length + a.cost := by
      obtain ⟨u,eu,lu⟩ := hubRun_extension d.gates w
      change (hubRun d.gates w).length = _
      rw [eu,List.length_append,lu]
      exact congrArg (w.length + ·) (a.compiled_size _)
    have hold (i : ℕ) (hi : i < x.length) : v.getD i false = x.getD i false :=
      (hubRun_old _ _ _ (by omega)).trans (agrees i hi)
    have left := ha w h.1 hp agrees
    have right := hb v h.2 (by omega) hold
    let e := b.compile (w.length+a.cost)
    let v' := hubRun e.gates v
    have hlen' : v'.length = w.length + a.cost + b.cost := by
      obtain ⟨u,eu,lu⟩ := hubRun_extension e.gates v
      change (hubRun e.gates v).length = _
      rw [eu,List.length_append,hlen,lu]
      exact congrArg ((w.length+a.cost) + ·) (b.compiled_size _)
    have lval : v'.getD d.output false = a.value x := by
      apply Eq.trans (hubRun_old e.gates v d.output ?_) left
      rw [hlen]
      exact a.output_bound h.1 hp
    have rval : v'.getD e.output false = b.value x := by
      change (hubRun (b.compile v.length).gates v).getD (b.compile v.length).output false = _ at right
      rw [hlen] at right
      exact right
    let g : Gate := ⟨if op then .or else .and,[d.output,e.output]⟩
    have exp : hubRun ((a.node op b).compile w.length).gates w =
        v' ++ [g.op.eval (g.inputs.map (fun i => v'.getD i false))] := by
      simp only [HubExpr.compile,hubRun,List.foldl_append,List.foldl_cons,List.foldl_nil,v',v,e,d,g]
    change (hubRun ((HubExpr.node op a b).compile w.length).gates w).getD
      (w.length + a.cost + b.cost) false = _
    rw [exp,←hlen', List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    simp only [List.getD_eq_getElem?_getD] at lval rval
    cases op <;> simp [g,GateOp.eval,lval,rval,HubExpr.value]

private def hubCoreExpr (t : ℕ) : HubExpr :=
  .node true (.input (t+2))
    (.node true (.node false (.input 0) (.node true (.input (t+3)) (.input (t+4))))
      (.node false (.input 1) (.input (t+3))))

private def hubExpr (t : ℕ) : ℕ → HubExpr
  | 0 => hubCoreExpr t
  | k+1 => .node true (hubExpr t k) (.node false (.input (k+2)) (.input (t+3+(k+2))))

private lemma hub_cost (t k : ℕ) : (hubExpr t k).cost = 2*k+5 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [hubExpr,HubExpr.cost,ih]; omega

private lemma hub_valid (t k : ℕ) (h : k ≤ t) : (hubExpr t k).within ((t+3)+(t+2)) := by
  induction k with
  | zero => simp only [hubExpr,hubCoreExpr,HubExpr.within]; omega
  | succ k ih =>
    exact ⟨ih (by omega),by change k+2 < _; omega,by change t+3+(k+2) < _; omega⟩

private lemma read_left {n m : ℕ} (u : Fin n) (v : Fin m) {a : ℕ} (ha : a < n) :
    (oneEach u v).getD a false = decide (a = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simpa using ha)]
  rw [List.getD_eq_getElem _ _ (by simpa using ha)]
  simp [Fin.ext_iff]

private lemma read_right {n m : ℕ} (u : Fin n) (v : Fin m) {a : ℕ} (ha : a < m) :
    (oneEach u v).getD (n+a) false = decide (a = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using ha)]
  simp [Fin.ext_iff]

private lemma hub_value (t k : ℕ) (h : k ≤ t) (u : Fin (t+3)) (v : Fin (t+2)) :
    (hubExpr t k).value (oneEach u v) = true ↔
      u.val = t+2 ∨ (u.val = 0 ∧ v.val ≤ 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
        (2 ≤ u.val ∧ u.val < k+2 ∧ u.val = v.val) := by
  induction k with
  | zero =>
    simp only [hubExpr,hubCoreExpr,HubExpr.value,Bool.false_eq_true,ite_false,ite_true,Bool.or_eq_true,Bool.and_eq_true]
    have c0 := read_right u v (a:=0) (by omega)
    have c1 := read_right u v (a:=1) (by omega)
    simp only [Nat.add_zero] at c0
    rw [read_left u v (a:=t+2) (by omega), read_left u v (a:=0) (by omega),
        read_left u v (a:=1) (by omega),c0,c1]
    simp only [decide_eq_true_eq]
    omega
  | succ k ih =>
    simp only [hubExpr,HubExpr.value,Bool.false_eq_true,ite_false,ite_true,Bool.or_eq_true,Bool.and_eq_true]
    rw [ih (by omega), read_left u v (a:=k+2) (by omega), read_right u v (a:=k+2) (by omega)]
    simp only [decide_eq_true_eq]
    omega

/-- A formula with five gates for the path and hub and two more per matching edge. -/
theorem hubIncidence_upper (t : ℕ) : RepSizeAtMost (hubIncidence t) (2*t+5) := by
  let n := (t+3)+(t+2)
  let f := hubExpr t t
  let c := f.compile n
  refine ⟨c, f.compiled_mono n, ?_, ?_⟩
  · exact (f.compiled_size n).le.trans (hub_cost t t).le
  · intro u v
    let x := oneEach u v
    have len : x.length = n := by simp only [x,oneEach,n,List.length_append,List.length_ofFn]
    have hval := f.eval_compile x x (by rw [len]; exact hub_valid t t le_rfl) le_rfl (fun _ _ => rfl)
    rw [len] at hval
    change (hubRun (f.compile n).gates x).getD (f.compile n).output false = _
    rw [hval]
    apply Bool.eq_iff_iff.mpr
    rw [hub_value t t le_rfl u v]
    simp only [hubIncidence,decide_eq_true_eq]
    have hv := v.isLt
    omega

end PEqualNP.RectangleBound


namespace PEqualNP.RectangleBound

open PEqualNP.Represents

/-- Every member of the connected family with at least one matching edge has exact cost 2t + 5. -/
theorem hubIncidence_exact (t : ℕ) (ht : 1 ≤ t) :
    RepSizeAtMost (hubIncidence t) (2*t+5) ∧ ¬ RepSizeAtMost (hubIncidence t) (2*t+4) := by
  refine ⟨hubIncidence_upper t, ?_⟩
  rintro ⟨C, mono, cap, rep⟩
  have lower := hubIncidence_lower t ht C mono rep
  omega

end PEqualNP.RectangleBound
