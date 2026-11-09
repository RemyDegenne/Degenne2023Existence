/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
-- One import per file proving a headline result of formalization.yaml.
import Degenne2023Existence.D2023.Corollary4
import Degenne2023Existence.D2023.Corollary14
import Degenne2023Existence.D2023.Lemma9
import Degenne2023Existence.D2023.Lemma11
import Degenne2023Existence.D2023.Lemma15
import Degenne2023Existence.D2023.Lemma16
import Degenne2023Existence.D2023.Lemma19
import Degenne2023Existence.D2023.Lemma20
import Degenne2023Existence.D2023.Theorem1
import Degenne2023Existence.D2023.Theorem2
import Degenne2023Existence.D2023.Theorem3
import Degenne2023Existence.D2023.Theorem5
import Degenne2023Existence.D2023.Theorem6
import Degenne2023Existence.D2023.Theorem7
import Degenne2023Existence.D2023.Theorem8
import Degenne2023Existence.D2023.Theorem10
import Degenne2023Existence.D2023.Theorem12
import Degenne2023Existence.D2023.Theorem13

/-! # Comparator solution module

The solution side of the [comparator](https://github.com/leanprover/comparator) setup in
`comparator/`: this module imports the project files proving the headline results listed in
`formalization.yaml`, so its environment contains, at the exact names stated (with `sorry`) in
the `comparator/Challenge_*.lean` files, the headline theorems of the paper (see
`comparator/README.md`). -/
