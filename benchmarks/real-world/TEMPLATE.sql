-- =============================================================================
-- Real-World Query Template
-- =============================================================================
-- Source: [company type, e.g., "e-commerce SaaS"]
-- Dialect: [PostgreSQL | MySQL | SQLite | SQL Server | Oracle]
-- Category: [analytics | transactional | etl | reporting]
-- Features: [JOIN, CTE, window function, subquery, aggregate, etc.]
-- Complexity: [simple | medium | complex]
-- Anonymized: yes
-- Date: YYYY-MM-DD
-- Description: [Brief description of what this query does]
-- =============================================================================

-- Your anonymized query here
SELECT
  c_1,
  c_2,
  COUNT(*) AS c_3
FROM t_1
JOIN t_2 ON t_1.c_4 = t_2.c_5
WHERE c_6 > 123
GROUP BY c_1, c_2
ORDER BY c_3 DESC
LIMIT 100;
