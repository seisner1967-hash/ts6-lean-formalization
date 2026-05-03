# Session bilan — 2026-05-03

**Cible :** clôture des sorrys structurels du dossier `TS6/` à partir d'un snapshot
initial Git (commit `828e60e`, 4 sorrys dans `RankinSelbergDecomp.lean` + 1 dans
`FiniteCharacterVariance.lean`).

**Outil :** [horizon-proof-agent](../goldbach-horizon/.claude/worktrees/beautiful-chaplygin-d3d0c4/horizon-proof-agent)
v0.1.4 (audit Lean read-only, profil `ts6`).

**Toolchain :** Lean v4.16.0, Mathlib v4.16.0 (`a6276f4c…`).

---

## 1. Sorrys fermés cette session

| # | Sorry (snapshot) | Phase | Commit | Lignes ajoutées |
|---|---|---|---|---|
| 1 | `RSD:155` — schur_orthogonality_dual AUX1 | 2A bis | `655908b` | +16 |
| 2 | `RSD:161` — schur_orthogonality_dual AUX2 | 2B | `afaae39` | +22 |
| 3 | `RSD:282` — diag_offdiag_split | 2C | `80ab482` | +69 |
| 4 | `RSD:349` — rankin_selberg_decomposition | 2D | `a5e2b84` | +48 |
| 5 | `FCV:215` — parseval_identity (split en 2 commits) | 2E + suite | `8ac750f` + `4f2000d` | +41 + +141 |

**Total Lean ajouté :** ~337 lignes (sub-lemmes privés + assemblages).

Tous les commits sur la branche `main` du dépôt `goldbach_lean_v2/` (initialisé en
début de session, snapshot initial = `828e60e`).

## 2. Statut TS6 module par module

| Module | Cible TS6 | Avant session | **Après session** | Note |
|---|---|---|---|---|
| `Exact/FiniteCharacterVariance.lean` | TS6-A (kernel Parseval) | YELLOW | **GREEN ✓** | parseval_identity fermé en Phase 2E |
| `Exact/DirichletVariance.lean` | TS6-B (TS2 Thm 2.1) | déjà GREEN | **GREEN ✓** | non touché cette session (bijection_step était fermé avant) |
| `Exact/CenteringShift.lean` | TS6-C (TS2 Prop 2.2) | déjà GREEN (header obsolète) | **GREEN ✓** | **investigation Phase 2F : les 2 sorrys mentionnés dans le `## Status` header n'existent pas — fichier déjà entièrement fermé**. Le header est OUTDATED |
| `Structure/RankinSelbergDecomp.lean` | TS6-D (TS5 Prop 3.7) | YELLOW | **GREEN ✓** | 4 sorrys fermés (Phases 2A→2D) |
| `Effective/AveragedBounds.lean` | TS6-E/F/G (effective bounds) | YELLOW BY-DESIGN | YELLOW BY-DESIGN | 3 sorrys intentionnels marqués `-- BY-DESIGN` (interfaces hypothétiques `ChebyshevThetaBound` et `LargeSieveInequality`, conformes au paper TS6 §Status) |

**Verdict global :** TS6-A, TS6-B, TS6-C, TS6-D sont tous GREEN. TS6-E/F/G restent
YELLOW comme prévu par le paper (« YELLOW (by design) »).

### Note sur CenteringShift.lean (Phase 2F)

Le `## Status` header de [`CenteringShift.lean`](TS6/Exact/CenteringShift.lean#L43-L46)
annonce :

> YELLOW — statement typed, proof plan documented, two `sorry` markers
> (one on the generic shift lemma, one on the specialization).

L'inspection L83-129 (`variance_shift_of_origin`) et L147-215 (`TS2_centering_shift`)
montre que **les deux théorèmes sont entièrement prouvés**, sans `sorry` dans le
corps du `by`. Les commentaires `-- NOTE: HUYGENS_STEP` (L66) et
`-- NOTE: CASCADE of variance_shift_of_origin` (L133) sont aussi obsolètes :
le HUYGENS_STEP est complet (cross-term cancellation via `h_sum_zero`),
TS2_centering_shift assemble effectivement via `variance_shift_of_origin` +
`TS2_exact_identity` puis `field_simp; ring`.

**Action recommandée pour une session ultérieure :** mettre à jour le header de
CenteringShift.lean (`YELLOW → GREEN`) et retirer les NOTE obsolètes. Aucune
modification du code de preuve n'est requise.

## 3. Trajectoire primary REAL sorry sur la session

```
8 sorrys (snapshot 828e60e)
↓ AUX1 closed (2A bis, commit 655908b)
7
↓ AUX2 closed (2B, commit afaae39)
6
↓ diag_offdiag_split closed (2C, commit 80ab482)
5
↓ rankin_selberg_decomposition closed (2D, commit a5e2b84)
4
↓ Steps 1+3 partial integration (2E partial, commit 8ac750f)
4 (no change, parseval still has its sorry)
↓ parseval_identity full close (2E suite, commit 4f2000d)
3 ← état final = les 3 BY-DESIGN d'AveragedBounds
```

Trajectoire confirmée par 11 rapports `report_20260503T*.md` archivés.

## 4. Artefacts produits

### Code Lean (intégré au build)

- 4 nouvelles `private lemma` ou `private theorem` dans `Structure/RankinSelbergDecomp.lean` :
  AUX1 inline + AUX2 inline + `diag_part_eq_DW` + `offdiag_part_eq_SW` + assemblages.
- 4 nouvelles `private lemma` ou `private theorem` dans `Exact/FiniteCharacterVariance.lean` :
  `variance_eq_sum_sq_minus_card_meanSq` (Step 1), `fourierCoeff_one_normSq` (Step 3),
  `schur_orthogonality_dual` (dual Schur, copie de RSD), `sum_fourierCoeff_normSq_eq_card_mul_sum_normSq` (Step 2),
  `sum_filter_ne_one_eq_total_sub_real` (helper).
- 2 nouveaux imports dans chaque fichier (`Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`,
  `Mathlib.Analysis.Complex.Polynomial.Basic`).

### Code Lean (archive méthodologique, hors build)

- 18 fichiers `TS6_scratch/*.lean` documentant la méthode scratch → in-context →
  intégration phase par phase. Conservés sur disque pour archive, retirés du
  `lean_lib TS6Scratch` du lakefile en Phase 2F.

### Rapports d'audit

- 11 rapports Markdown (`report_20260503T*.md`) + 11 index JSON (`index_20260503T*.json`)
  dans `horizon-proof-agent/reports/`, archivés également dans
  `~/Documents/Maths/TS6_audit_2026-05-03/` (22 fichiers total).

### Commits Git dans `goldbach_lean_v2/`

```
4f2000d Close parseval_identity: full Plancherel via Step 1+2+3 + filter ne 1 helper
8ac750f Add private lemmas for parseval_identity: variance Huygens identity and fourierCoeff at principal char
a5e2b84 Close rankin_selberg_decomposition: assembly via TS2 + RS_L1/L2/L3
80ab482 Close diag_offdiag_split: diagonal/off-diagonal decomposition
afaae39 Close AUX2 in schur_orthogonality_dual: dual Schur orthogonality via MulChar.Duality
655908b Close AUX1 in schur_orthogonality_dual: star (χ b) = (χ b)⁻¹ via root of unity
828e60e Snapshot initial avant fermeture des sorry RankinSelbergDecomp — 2026-05-03
```

(+ commit Phase 2F bilan/cleanup à venir)

## 5. Questions ouvertes pour la prochaine session

1. **Refactor `schur_orthogonality_dual`** : actuellement dupliqué entre
   `Structure/RankinSelbergDecomp.lean` (`TS6.Structure`) et
   `Exact/FiniteCharacterVariance.lean` (`TS6.Exact`). FCV étant en amont, le
   déplacement de RSD vers FCV permettrait à RSD d'utiliser la version de FCV
   et d'éliminer la duplication. ~5 minutes de travail (refactor + suppression
   + vérification du build).

2. **Header de `CenteringShift.lean`** : mettre à jour `## Status` de YELLOW à
   GREEN (les sorrys mentionnés sont déjà fermés). Retirer les NOTE obsolètes
   `HUYGENS_STEP` et `CASCADE`. ~2 minutes.

3. **Headers `## Status` des fichiers TS6** : aligner sur l'état réel après
   cette session :
   - FCV : YELLOW → GREEN
   - RSD : YELLOW → GREEN
   - CS : YELLOW → GREEN (déjà l'état réel)
   - DV : déjà GREEN, header peut-être à actualiser
   - AB : reste YELLOW BY-DESIGN

4. **Publication TS6 v4** : si envisagée, le manifeste `TS6_FROZEN.txt` peut
   être mis à jour avec les SHA-256 des nouveaux fichiers post-session. La
   `## Reproducibility` du paper ([`TS6_paper.tex`](TS6/TS6_paper.tex)) peut
   ajouter une note sur la version GREEN du kernel formel
   (TS6-A à TS6-D, avec TS6-E/F/G restant YELLOW comme dans v3).

5. **Linter warnings** : 3 warnings `unused section variable [DecidableEq G]`
   apparaissent dans FCV (lignes ~205, ~232, ~326) sur des lemmes qui n'utilisent
   pas explicitement la décidabilité. Solution mineure : `omit [DecidableEq G] in`
   devant chaque déclaration concernée. Cosmétique.

## 6. Honnêteté épistémique

- Aucun théorème prouvé cette session n'utilise de `sorry`, `admit`, ou `axiom`.
- Aucune source non-TS6 n'a été modifiée dans `goldbach_lean_v2/`.
- Aucune modification de `goldbach-horizon/`.
- La machinerie `IsAlgClosed.hasEnoughRootsOfUnity` (utilisée pour AUX2 et
  Step 2 de Parseval) repose sur `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
  qui dépend de `Mathlib.NumberTheory.Cyclotomic.Basic` — ces dépendances Mathlib
  v4.16 sont bien fermées (pas de sorry transitifs introduits).
- L'heuristique de l'agent d'audit (`horizon-proof-agent`) compte `sorry` après
  strip des commentaires/strings, donc les chiffres « 3 REAL sorry primary »
  reflètent du code Lean actif, pas des `sorry` documentaires.

## 7. Phase 2H — Renforcement documentation + Freeze TS6 v4

Décision (option 1 renforcée) : **aucune fermeture artificielle** des 3 sorrys
by-design d'AveragedBounds. À la place, renforcement de la documentation pour
que le statut épistémique soit cristallin, suivi d'un gel formel via manifeste
SHA-256.

### Actions Phase 2H

- **A.** [`TS6/Effective/AveragedBounds.lean`](TS6/Effective/AveragedBounds.lean) :
  remplacement du paragraphe `**Status: YELLOW by design.**` par une section
  `## Status: YELLOW BY-DESIGN` détaillant le rôle des 3 sorrys, la cause
  racine commune (`LargeSieveInequality.bound : True` placeholder), et le
  chemin de promotion vers GREEN si Mathlib expose un jour l'API requise.
- **B.** [`TS6/Exact/CenteringShift.lean`](TS6/Exact/CenteringShift.lean) :
  remplacement du `## Status` YELLOW par `## Status: GREEN` (les deux
  théorèmes étaient déjà prouvés sans sorry — header obsolète corrigé).
- **C.** Audit `horizon-proof-agent --full --profile ts6 --build-timeout 300` :
  Build SUCCESS, REAL sorry primary = 3 (inchangé, les 3 BY-DESIGN d'AB),
  rapport `report_20260503T081636Z.md`.
- **D.** Création de [`TS6_FROZEN_v4_2026-05-03.txt`](TS6_FROZEN_v4_2026-05-03.txt)
  avec SHA-256 des 7 fichiers du build closure (5 sources TS6 + lakefile +
  lean-toolchain), HEAD commit, Mathlib rev, statut par module, conditions
  YELLOW, instructions de reproductibilité.
- **E.** Ce paragraphe dans le bilan.
- **F.** Commit final `Freeze TS6 v4`.

### État final TS6 v4 (2026-05-03)

| Module | TS6 layer | Statut | Sorrys |
|---|---|---|---|
| `Exact/FiniteCharacterVariance.lean` | TS6-A | **GREEN** | 0 |
| `Exact/DirichletVariance.lean` | TS6-B | **GREEN** | 0 |
| `Exact/CenteringShift.lean` | TS6-C | **GREEN** | 0 |
| `Structure/RankinSelbergDecomp.lean` | TS6-D | **GREEN** | 0 |
| `Effective/AveragedBounds.lean` | TS6-E/F/G | **YELLOW BY-DESIGN** | 3 (tous tracés vers `LargeSieveInequality.bound : True`) |

**Bilan global :** 5 sorrys fermés (4 RSD + 1 FCV), 0 axiome ajouté par TS6,
3 sorrys restants tous documentés comme YELLOW BY-DESIGN dans le paper et
dans le code source. Couches exact (A, B, C) et spectrale (D) entièrement
formalisées. Couche effective (E, F, G) conditionnelle à un ajout futur dans
Mathlib (interface `LargeSieveInequality`).

## Phase 3 (extension de session) — TS6 v4.1 atteint

Branche dédiée : `close/averaged-bounds-green-conditional` (mergée fast-forward
dans `main`).

Travail accompli :
- **Session 1** : positivités élémentaires + `AWstar_nonneg` + skeleton TS3
  (3 scratchs validés, pas de commit).
- **Session 2** : interface `LargeSieveInequality` typée, définition
  `coeffEnergy`, helpers `W_sq_le_WsupNormSq` + `norm_weightCoeffs_sq_le` +
  `coeffEnergy_weightCoeffs_le`, cascade `TS4_weighted` →
  `TS4_unweighted` → `TS3_first`.

Résultat : **5 modules GREEN**. `AveragedBounds.lean` passe de YELLOW BY-DESIGN
(3 sorry) à GREEN CONDITIONAL (0 sorry, typed structure argument).

Manifeste : [`TS6_FROZEN_v4.1_2026-05-03.txt`](TS6_FROZEN_v4.1_2026-05-03.txt).
Commit freeze : `806acad`.

Statut épistémique :
- TS6 v4.1 ne prouve **PAS** le grand crible.
- TS6 v4.1 prouve la cascade TS4/TS3 conditionnellement à une interface typée
  non-vide.
- `#print axioms` : que les 3 axiomes du noyau Lean (`propext`,
  `Classical.choice`, `Quot.sound`). Aucun `sorryAx`.

**PDF v4.1 : à rédiger dans une session séparée.**
