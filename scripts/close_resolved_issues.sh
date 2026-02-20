#!/usr/bin/env bash
# close_resolved_issues.sh — Bulk-close GitHub issues whose axioms are proved or resolved.
#
# Usage:
#   gh auth login                          # if not already authenticated
#   bash scripts/close_resolved_issues.sh  # dry-run (prints commands)
#   bash scripts/close_resolved_issues.sh --execute  # actually close issues
#
# Generated 2026-02-20. Current axiom state: 7 remaining (531 theorems, 98.7%).
# The 7 remaining axioms map to issues #66, #68, #73, #77 (kept open).

set -euo pipefail

REPO="evelynmitchell/sql_equiv"
DRY_RUN=true

if [[ "${1:-}" == "--execute" ]]; then
  DRY_RUN=false
  echo "=== EXECUTING: closing issues for real ==="
else
  echo "=== DRY RUN: pass --execute to actually close issues ==="
fi

close_issue() {
  local number="$1"
  local comment="$2"

  if $DRY_RUN; then
    echo "[DRY RUN] Would close #${number}"
    echo "  Comment: ${comment:0:120}..."
    echo
  else
    echo "Closing #${number}..."
    gh issue close "$number" -R "$REPO" --comment "$comment"
    # Rate-limit: GitHub API allows 30 mutations/min for authenticated users
    sleep 2
  fi
}

# ─────────────────────────────────────────────────────────────────────
# Wave 1 — Expression-level boolean/arithmetic/comparison
# ─────────────────────────────────────────────────────────────────────

close_issue 11 "Closing: the original optimizer target axioms (\`pushdown_preserves_semantics\`, \`join_reorder_preserves_forward/backward\`) were removed along with the entire optimizer module in PR #156. The optimizer was the only major module with zero formal proofs. All 531 theorems in \`Equiv/\` are proved."

close_issue 46 "Closing: \`not_not\` (double negation) proved as a theorem in PR #104 with \`isBoolValued\` precondition."

close_issue 47 "Closing: \`and_absorb_or\` and \`or_absorb_and\` (absorption laws) proved as theorems in PR #104 with \`isBoolValued\` precondition."

close_issue 48 "Closing: \`and_true\` and \`or_false\` (identity laws) proved as theorems in PR #104 with \`isBoolValued\` precondition."

close_issue 49 "Closing: \`and_self\` and \`or_self\` (idempotent laws) proved as theorems in PR #104 with \`isBoolValued\` precondition."

close_issue 50 "Closing: \`and_not_self\` and \`or_not_self\` (complement laws) proved as theorems in PR #104 with \`isBoolValued\` precondition."

close_issue 54 "Closing: all 6 comparison negation rules (\`not_eq_is_ne\`, \`not_ne_is_eq\`, \`not_lt_is_ge\`, \`not_le_is_gt\`, \`not_gt_is_le\`, \`not_ge_is_lt\`) proved as theorems in PR #85."

close_issue 55 "Closing: all 4 comparison flip rules (\`lt_flip\`, \`le_flip\`, \`gt_flip\`, \`ge_flip\`) proved as theorems in PR #85."

close_issue 56 "Closing: \`eq_reflexive\` and \`ne_irreflexive\` proved as theorems in PR #92 with \`Expr.evaluable\` precondition (after null semantics fix)."

close_issue 57 "Closing: all 7 arithmetic identities (\`expr_add_zero\`, \`expr_zero_add\`, \`expr_mul_one\`, \`expr_one_mul\`, \`expr_mul_zero\`, \`expr_zero_mul\`, \`expr_sub_zero\`) proved as theorems in PR #93 with \`isIntValued\` precondition."

close_issue 61 "Closing: all 5 CASE/WHEN simplification axioms (\`case_when_true\`, \`case_when_false\`, \`case_when_false_no_else\`, \`case_empty_else\`, \`case_empty_no_else\`) proved as theorems in PR #85."

# ─────────────────────────────────────────────────────────────────────
# Wave 2 — IN/BETWEEN/LIKE/String
# ─────────────────────────────────────────────────────────────────────

close_issue 58 "Closing: all 8 IN list expansion axioms proved as theorems. \`in_empty_false\`/\`not_in_empty_true\` (PR #112, reproved #125), \`in_singleton\`/\`not_in_singleton\`/\`in_pair\`/\`not_in_pair\` (PR #126), \`in_list_or_expansion\`/\`not_in_list_and_expansion\` (PR #126)."

close_issue 59 "Closing: all 3 BETWEEN axioms proved as theorems. \`between_reflexive\` (PR #86, restored #102), \`between_expansion\`/\`not_between_expansion\` (PR #109)."

close_issue 60 "Closing: all 3 LIKE axioms proved as theorems. \`like_empty_pattern\` (PR #86, restored #102), \`like_match_all\` (PR #111), \`like_self\` (PR #134)."

close_issue 62 "Closing: all 8 string function axioms proved as theorems. \`length_empty\` (PR #86, restored #102), \`upper_idempotent\`/\`lower_idempotent\`/\`upper_lower_upper\`/\`lower_upper_lower\` (PR #105), \`concat_empty_left\`/\`concat_empty_right\` (PR #107), \`length_concat\` (PR #109)."

# ─────────────────────────────────────────────────────────────────────
# Wave 3 — Statement-level (no join dependency)
# ─────────────────────────────────────────────────────────────────────

close_issue 51 "Closing: \`where_true_elim\` and \`where_false_empty\` proved as theorems in PR #116. \`where_false_empty\` required adding \`h_no_agg : selectHasAggregate items = false\` precondition (aggregate queries like \`SELECT COUNT(*) WHERE FALSE\` return 1 row, not 0)."

close_issue 72 "Closing: all 4 filter composition axioms proved as theorems. \`filter_false_empty'\` (PR #116), \`filter_and\`/\`filter_commute\`/\`filter_idempotent\` (PR #147). Also proved \`predicate_pushdown\` for single tables (PR #147)."

close_issue 79 "Closing: ORDER BY properties resolved. 3 axioms proved as theorems in PR #115 (\`order_by_preserves_count\`, \`order_by_length_invariant\`, \`order_limit_deterministic\`). 2 axioms (\`order_by_idempotent\`, \`order_by_reverse\`) removed as unsound in PR #136 — they required sort stability guarantees not present in the evaluation model."

close_issue 80 "Closing: all 5 LIMIT axioms proved as theorems in PR #115 (\`limit_zero_empty\`, \`limit_upper_bound\`, \`limit_none_all_rows\`, \`limit_monotonic\`, \`limit_one_singleton\`)."

close_issue 81 "Closing: all 5 OFFSET/pagination axioms proved as theorems in PR #115 (\`offset_zero_identity\`, \`offset_too_large_empty\`, \`offset_reduces_count\`, \`offset_monotonic\`, \`limit_offset_compose\`). Additional pagination theorems also proved: \`offset_limit_zero_empty\`, \`pagination_upper_bound\`, \`pagination_identity\`, \`consecutive_pages\`."

close_issue 82 "Closing: aggregate property axioms proved as theorems. \`min_le_elem\`, \`max_ge_elem\`, \`distinct_count_le\`, \`distinct_idempotent\` all proved in \`Equiv/Comparison.lean\`."

close_issue 63 "Closing: all 3 set operation commutativity axioms proved as theorems. \`union_all_comm\` (bag equiv via \`List.perm_append_comm\`), \`union_comm\` (bag equiv via \`Perm_eraseDups\`), \`intersect_comm\` (set equiv via \`mem_filter_contains\`)."

close_issue 64 "Closing: all 4 set operation associativity/distributivity axioms proved as theorems. \`union_assoc\` (bag equiv), \`intersect_assoc\` (exact equality), \`union_intersect_distrib\`/\`intersect_union_distrib\` (set equiv)."

close_issue 65 "Closing: all 5 set operation edge case axioms proved as theorems. \`union_all_length\`, \`except_self_empty\`, \`intersect_empty_right\`, \`intersect_idempotent\`, \`union_idempotent\`, \`union_empty_right\`."

# ─────────────────────────────────────────────────────────────────────
# Wave 4 — Helper lemmas
# ─────────────────────────────────────────────────────────────────────

close_issue 52 "Closing: both normalization equivalence axioms proved as theorems. \`normalizeExpr_equiv\` (PR #162, via WFR conversion + strong induction on sizeOf), \`syntacticEquiv_implies_equiv\` (PR #163, via opaque + @[implemented_by] DecidableEq)."

close_issue 53 "Closing: both ground expression independence axioms proved as theorems. \`ground_expr_eval_independent\` (PR #150, via isGroundCore WFR mirror + bridge axioms), \`isGround_eq_isGroundCore\` (PR #151, via converting isGround mutual block from partial to WFR)."

# ─────────────────────────────────────────────────────────────────────
# Wave 5 — Joins (proved axioms only; #66, #68 kept open)
# ─────────────────────────────────────────────────────────────────────

close_issue 67 "Closing: \`cross_join_comm\` and \`cross_join_assoc\` proved as theorems in PR #140 via membership-based equivalence on flat row concatenation."

close_issue 69 "Closing: all join cardinality axioms proved as theorems. \`cross_join_cardinality\`, \`cross_join_cardinality_comm\`, \`cross_join_assoc_cardinality\`, \`inner_join_cardinality_le\`, \`left_join_cardinality_ge\`, \`right_join_cardinality_ge\` — all in \`Equiv/StatementAxioms.lean\`."

close_issue 70 "Closing: all 7 join edge case axioms proved as theorems. \`inner_join_empty_left\`/\`inner_join_empty_right\`, \`cross_join_empty_left\`/\`cross_join_empty_right\`, \`inner_join_true_is_cross\`, \`inner_join_false_empty\`, \`inner_join_to_where\` — all in \`Equiv/StatementAxioms.lean\`."

close_issue 71 "Closing: all outer join preservation axioms proved as theorems. \`left_join_preserves_left\`, \`right_join_preserves_right\`, \`inner_subset_cross\`, \`left_join_filter_null_is_inner\`, \`left_join_false_all_left\` — all in \`Equiv/StatementAxioms.lean\`."

close_issue 75 "Closing: all 5 EXISTS/NOT EXISTS basic axioms proved as theorems. \`exists_empty_false\`/\`not_exists_empty_true\`/\`exists_nonempty_true\`/\`not_exists_nonempty_false\` (PR #135), \`not_not_exists\` (PR #137)."

close_issue 76 "Closing: all 5 IN subquery axioms proved as theorems. \`in_empty_subquery_false\`/\`not_in_empty_subquery_true\`/\`in_singleton_subquery\` (PR #139), \`in_subquery_as_exists\`/\`not_in_subquery_as_not_exists\` (PR #157 — fixed 3 soundness issues, added qualified col + eval preconditions)."

close_issue 78 "Closing: scalar/correlated subquery axioms resolved. \`exists_as_count_gt_zero\`/\`not_exists_as_count_eq_zero\`/\`exists_monotonic\` proved (PR #137), \`scalar_subquery_is_first\`/\`subquery_limit_one\` proved (PR #139), \`scalar_subquery_empty_null\`/\`subquery_where_true\`/\`subquery_where_false\` proved (PR #138). \`uncorrelated_subquery_independent\` removed as unsound (PR #137)."

close_issue 74 "Closing: optimizer \`predicate_pushdown\` axiom removed along with the entire optimizer module in PR #156. The single-table \`filter_pushdown_table\` equivalence was proved as a theorem in PR #147 (in \`Equiv/\`)."

# ─────────────────────────────────────────────────────────────────────
# Summary
# ─────────────────────────────────────────────────────────────────────

echo ""
echo "================================================================"
echo " Summary"
echo "================================================================"
echo " Issues closed: 34"
echo "   Wave 1 (expr-level):  #11 #46 #47 #48 #49 #50 #54 #55 #56 #57 #61"
echo "   Wave 2 (IN/LIKE/str): #58 #59 #60 #62"
echo "   Wave 3 (stmt-level):  #51 #63 #64 #65 #72 #79 #80 #81 #82"
echo "   Wave 4 (helpers):     #52 #53"
echo "   Wave 5 (joins/sub):   #67 #69 #70 #71 #74 #75 #76 #78"
echo ""
echo " Issues kept open: 4 (mapping to 6 non-bridge remaining axioms)"
echo "   #66  join_comm           — blocked (row list structure)"
echo "   #68  join_assoc          — blocked (ON predicate scope)"
echo "   #73  filter_join_left/right — blocked (partial def)"
echo "   #77  subquery unnesting  — blocked (hard transform + NULL)"
echo ""
echo " Axiom ratchet: 7 (6 SQL equivalence + 1 infrastructure bridge)"
echo " Proof completion: 531/538 = 98.7%"
echo "================================================================"
