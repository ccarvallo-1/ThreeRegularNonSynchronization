/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Basic
public import Kuramoto.Certificate
public import Kuramoto.Gadget
public import Kuramoto.Kantorovich
public import Kuramoto.Transplant
public import Kuramoto.Correction
public import Kuramoto.RandomGraph
public import Kuramoto.Extension
public import Kuramoto.ConfigModel
public import Kuramoto.GadgetCount
public import Kuramoto.Main

/-!
# Random 3-regular graphs are not globally synchronizing — Lean formalization

Companion formalization of C. Carvallo, P. Groisman, D. Mitsche, *Random 3-regular graphs are
not globally synchronizing*, [arXiv:2610.09135](https://arxiv.org/abs/2610.09135). The main
result is `Kuramoto.main_theorem` (Theorem 1.2); see `README.md` for an overview, the list of
assumed results and the correspondence with the paper.
-/

