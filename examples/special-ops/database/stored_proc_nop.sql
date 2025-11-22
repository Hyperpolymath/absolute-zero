-- ============================================================================
-- STORED_PROC_NOP.SQL - Stored Procedures with CNO Characteristics
-- ============================================================================
-- Demonstrates stored procedures, functions, and routines that execute
-- successfully but produce zero persistent state change. These are
-- "Absolute Zero" operations at the procedural level: complex logic,
-- control flow, computations, but no observable database mutation.
--
-- Key Concepts:
-- - Procedure execution without side effects
-- - Functions that return values without modifying state
-- - Transaction control within procedures
-- - Exception handling with rollback
-- - Temporary tables that disappear
-- - Computational overhead without persistence
-- ============================================================================

-- ----------------------------------------------------------------------------
-- POSTGRESQL: PL/pgSQL PROCEDURES AND FUNCTIONS
-- ----------------------------------------------------------------------------

-- PROC NOP 1: Read-Only Analytical Procedure
-- Performs complex analysis but makes no changes
CREATE OR REPLACE PROCEDURE proc_analyze_data(
    p_date_from DATE,
    p_date_to DATE,
    OUT result_json JSONB
)
LANGUAGE plpgsql
AS $$
DECLARE
    v_total_revenue NUMERIC;
    v_avg_order_value NUMERIC;
    v_customer_count INTEGER;
    v_top_products JSONB;
BEGIN
    -- Complex aggregation queries (read-only)
    SELECT
        COALESCE(SUM(total), 0),
        COALESCE(AVG(total), 0),
        COUNT(DISTINCT customer_id)
    INTO
        v_total_revenue,
        v_avg_order_value,
        v_customer_count
    FROM orders
    WHERE order_date BETWEEN p_date_from AND p_date_to;

    -- Subquery for top products
    SELECT jsonb_agg(product_data)
    INTO v_top_products
    FROM (
        SELECT
            product_id,
            SUM(quantity) as total_sold
        FROM order_items oi
        JOIN orders o ON oi.order_id = o.order_id
        WHERE o.order_date BETWEEN p_date_from AND p_date_to
        GROUP BY product_id
        ORDER BY total_sold DESC
        LIMIT 10
    ) product_data;

    -- Construct result JSON
    result_json := jsonb_build_object(
        'total_revenue', v_total_revenue,
        'avg_order_value', v_avg_order_value,
        'customer_count', v_customer_count,
        'top_products', v_top_products,
        'generated_at', CURRENT_TIMESTAMP
    );

    /*
    CNO CHARACTERISTICS:
    - Procedure executes complex queries
    - Multiple table scans, aggregations, sorts
    - CPU, memory, I/O consumed
    - No INSERT, UPDATE, DELETE operations
    - No persistent state change
    - Return value: Computed data, not stored

    OVERHEAD:
    - Query planning: Multiple query plans generated
    - Execution: Full table scans, hash aggregates
    - Memory: Work_mem for sorts and aggregates
    - I/O: Disk reads if data not in cache
    - Result: Pure computation, zero persistence
    */
END;
$$;

-- Usage: Execute procedure (no data modified)
CALL proc_analyze_data('2024-01-01', '2024-12-31', NULL::JSONB);

-- PROC NOP 2: Transaction Control with Guaranteed Rollback
CREATE OR REPLACE PROCEDURE proc_dry_run_migration(
    p_batch_size INTEGER DEFAULT 1000
)
LANGUAGE plpgsql
AS $$
DECLARE
    v_processed INTEGER := 0;
    v_batch_count INTEGER := 0;
BEGIN
    -- Begin transaction for dry run
    -- Note: PostgreSQL procedures can manage transactions
    COMMIT;  -- Ensure no active transaction

    BEGIN
        -- Start migration transaction
        -- Process in batches
        LOOP
            -- Update batch of records
            UPDATE legacy_data
            SET
                migrated = true,
                migrated_at = CURRENT_TIMESTAMP
            WHERE id IN (
                SELECT id
                FROM legacy_data
                WHERE migrated = false
                LIMIT p_batch_size
            );

            GET DIAGNOSTICS v_processed = ROW_COUNT;

            EXIT WHEN v_processed = 0;

            v_batch_count := v_batch_count + 1;

            -- Simulate processing
            PERFORM pg_sleep(0.01);  -- 10ms delay
        END LOOP;

        RAISE NOTICE 'Dry run: % batches processed', v_batch_count;

        -- Always rollback (dry run)
        RAISE EXCEPTION 'Dry run complete - rolling back changes';

    EXCEPTION
        WHEN OTHERS THEN
            RAISE NOTICE 'Rollback: %', SQLERRM;
            ROLLBACK;
    END;

    /*
    CNO CHARACTERISTICS:
    - Full migration logic executed
    - All updates performed
    - Transaction log written
    - Locks acquired and released
    - Exception raised → guaranteed rollback
    - Result: Zero persistent changes (dry run complete)

    USE CASE:
    - Test migration logic without committing
    - Verify performance and timing
    - Detect errors before production run
    */
END;
$$;

-- PROC NOP 3: Computational Function (Pure Function)
CREATE OR REPLACE FUNCTION func_calculate_score(
    p_user_id INTEGER,
    p_weight_factor NUMERIC DEFAULT 1.0
)
RETURNS NUMERIC
LANGUAGE plpgsql
IMMUTABLE  -- Indicates no database modification
AS $$
DECLARE
    v_activity_score NUMERIC;
    v_engagement_score NUMERIC;
    v_final_score NUMERIC;
BEGIN
    -- Calculate activity score
    SELECT
        COUNT(*) * p_weight_factor
    INTO v_activity_score
    FROM user_actions
    WHERE user_id = p_user_id
        AND created_at > CURRENT_DATE - INTERVAL '30 days';

    -- Calculate engagement score
    SELECT
        AVG(engagement_value) * p_weight_factor
    INTO v_engagement_score
    FROM user_engagement
    WHERE user_id = p_user_id;

    -- Weighted sum
    v_final_score := (v_activity_score * 0.6) + (v_engagement_score * 0.4);

    RETURN v_final_score;

    /*
    CNO CHARACTERISTICS:
    - Pure function: Same inputs → same outputs
    - IMMUTABLE: Compiler knows no side effects
    - Read-only queries
    - No transaction required
    - Can be inlined by query planner
    - Result: Computation only, no state change

    QUERY OPTIMIZATION:
    - Function can be cached
    - Results memoized within query
    - No locking required
    */
END;
$$;

-- PROC NOP 4: Procedure with Temporary Table
CREATE OR REPLACE PROCEDURE proc_temp_analysis(
    OUT summary_count INTEGER
)
LANGUAGE plpgsql
AS $$
BEGIN
    -- Create temporary table (session-scoped)
    CREATE TEMP TABLE IF NOT EXISTS temp_results (
        category TEXT,
        total NUMERIC,
        average NUMERIC
    ) ON COMMIT DROP;  -- Auto-drop on commit

    -- Populate temporary table
    INSERT INTO temp_results
    SELECT
        category,
        SUM(amount) as total,
        AVG(amount) as average
    FROM transactions
    GROUP BY category;

    -- Process temporary data
    SELECT COUNT(*) INTO summary_count FROM temp_results;

    -- Temporary table automatically dropped at end of transaction
    COMMIT;

    /*
    CNO CHARACTERISTICS:
    - Temporary table created in session's temp schema
    - Data inserted into temp table
    - Complex processing on temp data
    - ON COMMIT DROP: Auto-cleanup
    - Result: No permanent tables or data

    OVERHEAD:
    - Temp table creation: Catalog entries
    - Data insertion: Disk I/O (if large)
    - Cleanup: Automatic on commit
    - Session impact: Temp table visible only to session
    */
END;
$$;

-- PROC NOP 5: Exception Handling Cascade
CREATE OR REPLACE FUNCTION func_safe_division(
    p_numerator NUMERIC,
    p_denominator NUMERIC
)
RETURNS NUMERIC
LANGUAGE plpgsql
AS $$
DECLARE
    v_result NUMERIC;
BEGIN
    -- Attempt division
    v_result := p_numerator / p_denominator;
    RETURN v_result;

EXCEPTION
    WHEN division_by_zero THEN
        RAISE NOTICE 'Division by zero detected, returning NULL';
        RETURN NULL;
    WHEN OTHERS THEN
        RAISE NOTICE 'Unexpected error: %', SQLERRM;
        RETURN NULL;
END;
$$;

-- Usage: Call with zero denominator (exception handled, no crash)
SELECT func_safe_division(10, 0);
-- Result: NULL (exception caught, no error propagated)

/*
CNO CHARACTERISTIC:
- Exception raised during execution
- Exception handler catches error
- No state modification before or after exception
- Result: Graceful handling, zero state change
*/

-- PROC NOP 6: Cursor-Based Processing Without Commit
CREATE OR REPLACE PROCEDURE proc_cursor_scan(
    p_category TEXT
)
LANGUAGE plpgsql
AS $$
DECLARE
    cur_products CURSOR FOR
        SELECT id, name, price
        FROM products
        WHERE category = p_category;
    rec_product RECORD;
    v_count INTEGER := 0;
BEGIN
    -- Open cursor
    OPEN cur_products;

    LOOP
        FETCH cur_products INTO rec_product;
        EXIT WHEN NOT FOUND;

        -- Process record (no modification)
        v_count := v_count + 1;

        -- Could perform calculations, logging, etc.
        -- But we're doing nothing with the data
    END LOOP;

    CLOSE cur_products;

    RAISE NOTICE 'Scanned % products', v_count;

    /*
    CNO CHARACTERISTICS:
    - Cursor declared and opened
    - All matching rows fetched
    - Processing loop executes
    - No data modification
    - Cursor closed
    - Result: Read-only scan, zero persistence

    OVERHEAD:
    - Cursor state maintained in memory
    - Rows fetched in batches
    - Memory allocation for record variables
    - No disk writes
    */
END;
$$;

-- ----------------------------------------------------------------------------
-- MYSQL: STORED PROCEDURES
-- ----------------------------------------------------------------------------

-- PROC NOP 7: MySQL Procedure with Transaction Rollback
DELIMITER $$

CREATE PROCEDURE proc_mysql_dry_run(
    IN p_user_id INT,
    OUT result_message VARCHAR(255)
)
BEGIN
    DECLARE EXIT HANDLER FOR SQLEXCEPTION
    BEGIN
        ROLLBACK;
        SET result_message = 'Transaction rolled back';
    END;

    START TRANSACTION;

    -- Perform operations
    UPDATE user_profile
    SET last_login = NOW()
    WHERE user_id = p_user_id;

    INSERT INTO login_log (user_id, login_time)
    VALUES (p_user_id, NOW());

    -- Intentionally rollback
    ROLLBACK;

    SET result_message = 'Dry run completed - no changes persisted';

    /*
    CNO CHARACTERISTICS:
    - Transaction started
    - Multiple DML operations
    - Explicit ROLLBACK
    - No data persisted
    - OUT parameter: Returns status without state change
    */
END$$

DELIMITER ;

-- PROC NOP 8: MySQL Function - Pure Computation
DELIMITER $$

CREATE FUNCTION func_mysql_calculate_discount(
    p_price DECIMAL(10,2),
    p_tier VARCHAR(20)
)
RETURNS DECIMAL(10,2)
DETERMINISTIC
READS SQL DATA
BEGIN
    DECLARE v_discount_rate DECIMAL(5,4);
    DECLARE v_discounted_price DECIMAL(10,2);

    -- Lookup discount rate (read-only)
    SELECT discount_rate INTO v_discount_rate
    FROM discount_tiers
    WHERE tier_name = p_tier
    LIMIT 1;

    -- Calculate
    SET v_discounted_price = p_price * (1 - COALESCE(v_discount_rate, 0));

    RETURN v_discounted_price;

    /*
    CNO CHARACTERISTICS:
    - DETERMINISTIC: Same inputs → same outputs
    - READS SQL DATA: Read-only access
    - No data modification
    - Return value: Computed, not stored
    */
END$$

DELIMITER ;

-- PROC NOP 9: MySQL Procedure with Prepared Statement
DELIMITER $$

CREATE PROCEDURE proc_mysql_dynamic_query(
    IN p_table_name VARCHAR(64),
    IN p_column_name VARCHAR(64),
    OUT row_count INT
)
BEGIN
    SET @sql = CONCAT('SELECT COUNT(*) INTO @result FROM ', p_table_name,
                      ' WHERE ', p_column_name, ' IS NOT NULL');

    PREPARE stmt FROM @sql;
    EXECUTE stmt;
    DEALLOCATE PREPARE stmt;

    SET row_count = @result;

    /*
    CNO CHARACTERISTICS:
    - Dynamic SQL constructed
    - Prepared statement created
    - Query executed (read-only)
    - Statement deallocated
    - No persistent state change

    OVERHEAD:
    - SQL parsing at runtime
    - Statement preparation
    - Execution
    - Cleanup
    */
END$$

DELIMITER ;

-- ----------------------------------------------------------------------------
-- SQLITE: SIMPLER PROCEDURE-LIKE PATTERNS
-- ----------------------------------------------------------------------------

-- Note: SQLite doesn't have stored procedures, but we can demonstrate
-- similar patterns using application-defined functions or scripts

-- PROC NOP 10: SQLite Transaction Script (pseudo-procedure)
/*
In SQLite, procedures are typically implemented in application code.
Here's a transaction script pattern:
*/

BEGIN TRANSACTION;

-- Create temporary table
CREATE TEMP TABLE temp_aggregates AS
SELECT
    category,
    SUM(amount) as total
FROM transactions
GROUP BY category;

-- Query temporary table
SELECT * FROM temp_aggregates;

-- Rollback to discard everything
ROLLBACK;

/*
CNO CHARACTERISTICS:
- Temp table created (in temp database file)
- Data aggregated
- Results queried
- ROLLBACK: Temp table dropped, data discarded
- Result: Zero persistent state change

SQLITE TEMP TABLE BEHAVIOR:
- Stored in separate temp database file
- Automatically cleaned up on connection close
- Not visible to other connections
- Disk I/O if data exceeds memory threshold
*/

-- PROC NOP 11: SQLite CTE-Based "Function"
WITH RECURSIVE fibonacci(n, a, b) AS (
    SELECT 1, 0, 1
    UNION ALL
    SELECT n+1, b, a+b FROM fibonacci WHERE n < 20
)
SELECT n, a as fibonacci_number FROM fibonacci;

/*
CNO CHARACTERISTICS:
- Recursive CTE computes Fibonacci sequence
- Complex computation
- No tables accessed (except CTE)
- No data modification
- Result: Pure computation, zero persistence
*/

-- ----------------------------------------------------------------------------
-- CROSS-DATABASE: PERFORMANCE ANALYSIS
-- ----------------------------------------------------------------------------

/*
STORED PROCEDURE OVERHEAD COMPARISON:

PostgreSQL PL/pgSQL:
- Compilation: First execution compiles, cached afterward
- Execution: Interpreted (slower than native)
- Optimization: Plan caching, function inlining
- Transaction control: Procedures can COMMIT/ROLLBACK
- Overhead: ~100-500 microseconds per call (simple proc)

MySQL Stored Procedures:
- Compilation: Compiled to native format, cached
- Execution: Faster than PL/pgSQL
- Optimization: Limited compared to PostgreSQL
- Transaction control: Can manage transactions
- Overhead: ~50-200 microseconds per call

SQLite:
- No native stored procedures
- Application-defined functions: C/C++ code (fast)
- Scripts: Executed as batch SQL
- Overhead: Depends on implementation (C functions: ~10μs)

CACHING EFFECTS:
- First call: Compilation + execution
- Subsequent calls: Execution only (plan cached)
- Cache invalidation: DDL changes, statistics updates

MEMORY OVERHEAD:
- Local variables: Stack allocation per call
- Cursors: Memory for result sets
- Temporary tables: Memory or disk (depends on size)
- Plan cache: Shared memory for compiled procedures
*/

-- ----------------------------------------------------------------------------
-- ADVANCED PROC NOPS
-- ----------------------------------------------------------------------------

-- PROC NOP 12: Nested Procedure Calls (PostgreSQL)
CREATE OR REPLACE FUNCTION func_level_3()
RETURNS INTEGER
LANGUAGE plpgsql
AS $$
BEGIN
    RETURN 42;
END;
$$;

CREATE OR REPLACE FUNCTION func_level_2()
RETURNS INTEGER
LANGUAGE plpgsql
AS $$
DECLARE
    v_result INTEGER;
BEGIN
    v_result := func_level_3();
    RETURN v_result * 2;
END;
$$;

CREATE OR REPLACE FUNCTION func_level_1()
RETURNS INTEGER
LANGUAGE plpgsql
AS $$
DECLARE
    v_result INTEGER;
BEGIN
    v_result := func_level_2();
    RETURN v_result + 10;
END;
$$;

-- Usage: Nested function calls
SELECT func_level_1();
-- Result: ((42 * 2) + 10) = 94

/*
CNO CHARACTERISTICS:
- Call stack depth: 3 levels
- Each function allocates stack frame
- No data modification at any level
- Pure computation cascade
- Result: Nested execution overhead, zero persistence

CALL STACK OVERHEAD:
- Stack frame allocation per call
- Local variable storage
- Return address tracking
- Total overhead: Linear with depth
*/

-- PROC NOP 13: Autonomous Transaction Simulation
-- PostgreSQL doesn't have true autonomous transactions, but dblink can simulate
CREATE EXTENSION IF NOT EXISTS dblink;

CREATE OR REPLACE FUNCTION func_autonomous_log(
    p_message TEXT
)
RETURNS VOID
LANGUAGE plpgsql
AS $$
BEGIN
    -- Use dblink to create "autonomous" transaction
    PERFORM dblink_connect('autonomous', 'dbname=' || current_database());

    PERFORM dblink_exec('autonomous',
        'INSERT INTO autonomous_log (message, logged_at) VALUES (' ||
        quote_literal(p_message) || ', CURRENT_TIMESTAMP)'
    );

    PERFORM dblink_disconnect('autonomous');

    -- If outer transaction rolls back, this log entry persists
    -- But for CNO: Don't call this in a transaction, or use temp table

    /*
    CNO SCENARIO:
    - Function creates separate connection
    - Executes INSERT in separate transaction
    - Inner transaction commits independently
    - Outer transaction can rollback without affecting log

    NOT A TRUE CNO:
    - Log entry persists even if caller rolls back
    - Use case: Audit trail that survives rollback

    MAKE IT A CNO:
    - Log to temp table instead
    - Or: Don't commit dblink transaction
    */
END;
$$;

-- PROC NOP 14: Conditional Execution with Early Return
CREATE OR REPLACE FUNCTION func_conditional_nop(
    p_condition BOOLEAN
)
RETURNS TEXT
LANGUAGE plpgsql
AS $$
BEGIN
    -- Early return on condition
    IF NOT p_condition THEN
        RETURN 'Condition not met - no operation performed';
    END IF;

    -- Complex logic here (never executes if condition false)
    UPDATE some_table SET value = value + 1 WHERE id = 1;

    RETURN 'Operation completed';

    /*
    CNO SCENARIO:
    - Call with p_condition = false
    - Function executes, checks condition
    - Early return (no UPDATE executed)
    - Result: Minimal overhead, zero state change
    */
END;
$$;

-- Usage: Call with false condition
SELECT func_conditional_nop(false);
-- Result: 'Condition not met - no operation performed'

-- ----------------------------------------------------------------------------
-- STORED PROCEDURE CNO USE CASES
-- ----------------------------------------------------------------------------

/*
LEGITIMATE USES:

1. Dry-Run Operations:
   - Test complex procedures without committing
   - Validate migration logic
   - Performance testing

2. Read-Only Analytics:
   - Complex aggregations and calculations
   - Report generation
   - Data quality checks

3. Pure Functions:
   - Computations without side effects
   - Business logic calculations
   - Data transformations

4. Testing and Development:
   - Procedure logic validation
   - Performance profiling
   - Debugging with RAISE NOTICE

5. Temporary Data Processing:
   - Session-scoped temp tables
   - In-memory computations
   - Intermediate result caching

ANTI-PATTERNS:

- Procedures with hidden side effects (triggers, audit logs)
- Relying on autonomous transactions for CNOs
- Complex nested procedures (hard to debug)
- Using procedures for simple queries (overhead not justified)

PERFORMANCE CONSIDERATIONS:

- Compilation overhead on first call
- Plan caching benefits repeated calls
- Nested calls: Stack depth overhead
- Transaction control: Extra commit/rollback cost
- Temporary tables: Memory/disk overhead

ACID PROPERTIES:

- Atomicity: Procedures execute in transaction context
- Consistency: Can enforce business rules
- Isolation: See transaction's snapshot
- Durability: Controlled by transaction commit/rollback

For CNOs: Procedures leverage full transaction machinery,
execute complex logic, but ensure zero persistent state change
through rollback, temp tables, or read-only operations.
*/

-- ============================================================================
-- CLEANUP (Optional)
-- ============================================================================

/*
DROP PROCEDURE IF EXISTS proc_analyze_data(DATE, DATE);
DROP PROCEDURE IF EXISTS proc_dry_run_migration(INTEGER);
DROP FUNCTION IF EXISTS func_calculate_score(INTEGER, NUMERIC);
DROP PROCEDURE IF EXISTS proc_temp_analysis();
DROP FUNCTION IF EXISTS func_safe_division(NUMERIC, NUMERIC);
DROP PROCEDURE IF EXISTS proc_cursor_scan(TEXT);
DROP FUNCTION IF EXISTS func_level_1();
DROP FUNCTION IF EXISTS func_level_2();
DROP FUNCTION IF EXISTS func_level_3();
DROP FUNCTION IF EXISTS func_autonomous_log(TEXT);
DROP FUNCTION IF EXISTS func_conditional_nop(BOOLEAN);
*/

-- ============================================================================
-- END STORED_PROC_NOP.SQL
-- ============================================================================
