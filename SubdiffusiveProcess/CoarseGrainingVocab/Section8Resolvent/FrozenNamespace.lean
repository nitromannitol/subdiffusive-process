/-!
# Namespace anchor for the Section 8 frozen declarations

Support declaration for freeze package 06 (D-087): the frozen Section 8
files carry fully qualified names and `open SubdiffusiveProcess.Frozen.Section8`, which
requires the namespace to exist before the first frozen declaration.
-/

/-- The Section 8 frozen namespace anchor (freeze package 06, D-087). -/
def SubdiffusiveProcess.Frozen.Section8.frozenNamespaceAnchor : Unit := ()
