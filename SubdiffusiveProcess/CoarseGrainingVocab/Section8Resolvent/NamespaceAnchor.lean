module

@[expose] public section

/-!
# Namespace anchor for the Section 8 frozen declarations

Support declaration: the frozen Section 8
files carry fully qualified names and `open SubdiffusiveProcess.Section8`, which
requires the namespace to exist before the first frozen declaration.
-/

/-- The Section 8 frozen namespace anchor. -/
def SubdiffusiveProcess.Section8.namespaceAnchor : Unit := ()
