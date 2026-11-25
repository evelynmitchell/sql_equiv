-- This module serves as the root of the `SqlEquiv` library.
-- Import modules here that should be built as part of the library.
-- Since #466 (decision D7) `SqlEquiv`'s evaluator is a labelled reference oracle: the project's
-- semantics, rewriter and checker are the typed core's (`SqlCore`); `SqlBridge` connects the two.
import SqlEquiv.Basic
import SqlEquiv.Tactics
