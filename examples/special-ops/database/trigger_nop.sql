-- ============================================================================
-- TRIGGER_NOP.SQL - Database Triggers That Do Nothing
-- ============================================================================
-- Demonstrates triggers that execute successfully but produce no observable
-- state change. These are "Absolute Zero" operations at the trigger level:
-- event detection, condition evaluation, trigger body execution, but zero
-- net effect on database state.
--
-- Key Concepts:
-- - Trigger execution overhead without side effects
-- - Conditional triggers that short-circuit
-- - BEFORE triggers that prevent modifications
-- - AFTER triggers with null operations
-- - Cascading trigger chains that cancel out
-- - Recursive trigger termination
-- ============================================================================

-- ----------------------------------------------------------------------------
-- POSTGRESQL: TRIGGER PROCEDURES
-- ----------------------------------------------------------------------------

-- Setup: Create test table
CREATE TABLE IF NOT EXISTS trigger_test (
    id SERIAL PRIMARY KEY,
    value INTEGER,
    modified_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- TRIGGER NOP 1: Conditional No-Op Trigger
-- Trigger fires but immediately returns NULL (cancels operation)
CREATE OR REPLACE FUNCTION trig_conditional_nop()
RETURNS TRIGGER AS $$
BEGIN
    -- Condition that's always false
    IF 1 = 0 THEN
        RETURN NEW;
    END IF;

    -- Always returns NULL, preventing the operation
    RETURN NULL;

    /*
    OVERHEAD:
    - Trigger fired: Yes
    - Function executed: Yes
    - Condition evaluated: Yes
    - Row modified: No (NULL return cancels operation)
    - Result: Trigger overhead without data modification
    */
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_conditional_nop
    BEFORE INSERT OR UPDATE ON trigger_test
    FOR EACH ROW
    EXECUTE FUNCTION trig_conditional_nop();

-- Test: Attempt insert (will be canceled by trigger)
INSERT INTO trigger_test (value) VALUES (42);
-- Result: 0 rows inserted, trigger executed, operation canceled
-- Query result: INSERT 0 0

-- TRIGGER NOP 2: Self-Canceling UPDATE Trigger
-- BEFORE trigger that resets NEW to OLD (no net change)
CREATE OR REPLACE FUNCTION trig_reset_changes()
RETURNS TRIGGER AS $$
BEGIN
    -- Copy OLD values to NEW, canceling any changes
    NEW.value := OLD.value;
    NEW.modified_at := OLD.modified_at;

    RETURN NEW;

    /*
    CHARACTERISTIC:
    - Trigger fires on UPDATE
    - NEW record modified, but to identical values as OLD
    - Database perceives "update" but no values change
    - Indexes: Checked but not modified (values identical)
    - MVCC: New tuple version created, but identical to old
    - Result: Perfect CNO - execution without change
    */
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_reset_changes
    BEFORE UPDATE ON trigger_test
    FOR EACH ROW
    EXECUTE FUNCTION trig_reset_changes();

-- Test: Update will execute but produce no change
UPDATE trigger_test SET value = 999 WHERE id = 1;
-- Result: Row "updated" to same values, no net change

-- TRIGGER NOP 3: Tautological Condition Trigger
-- Trigger with WHEN clause that's always false
CREATE OR REPLACE FUNCTION trig_never_fires()
RETURNS TRIGGER AS $$
BEGIN
    -- This code never executes due to WHEN clause
    INSERT INTO audit_log (message) VALUES ('Trigger fired!');
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_never_fires
    AFTER INSERT ON trigger_test
    FOR EACH ROW
    WHEN (NEW.value IS NULL AND NEW.value IS NOT NULL)  -- Always false
    EXECUTE FUNCTION trig_never_fires();

-- Test: Insert executes, trigger condition evaluated but body not executed
INSERT INTO trigger_test (value) VALUES (100);
-- Result: Row inserted, trigger condition evaluated (false), function not called
-- Overhead: Condition evaluation only, no function call

/*
TRIGGER OVERHEAD ANALYSIS:
- Trigger lookup: O(1) hash lookup in trigger registry
- Condition evaluation: SQL expression evaluation
- Function call: Zero (condition false)
- Total overhead: ~10-50 microseconds per operation
*/

-- TRIGGER NOP 4: Recursive Trigger with Base Case
-- Trigger that can call itself but terminates immediately
CREATE OR REPLACE FUNCTION trig_recursive_nop()
RETURNS TRIGGER AS $$
BEGIN
    -- Base case: Check recursion depth
    IF pg_trigger_depth() > 0 THEN
        RETURN NEW;  -- Already in trigger, exit immediately
    END IF;

    -- Attempt to trigger recursion (will hit base case)
    UPDATE trigger_test SET value = value WHERE id = NEW.id;

    RETURN NEW;

    /*
    EXECUTION FLOW:
    1. Initial INSERT fires trigger (depth=0)
    2. Trigger UPDATE fires nested trigger (depth=1)
    3. Nested trigger checks depth > 0, returns immediately
    4. Original trigger completes

    RESULT: Recursive call structure, but immediate termination
    CNO: Complex control flow, no net state change
    */
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_recursive_nop
    AFTER INSERT ON trigger_test
    FOR EACH ROW
    EXECUTE FUNCTION trig_recursive_nop();

-- TRIGGER NOP 5: Multi-Trigger Cancellation Chain
-- Multiple triggers that cancel each other out

CREATE OR REPLACE FUNCTION trig_increment()
RETURNS TRIGGER AS $$
BEGIN
    NEW.value := NEW.value + 1;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION trig_decrement()
RETURNS TRIGGER AS $$
BEGIN
    NEW.value := NEW.value - 1;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_increment
    BEFORE UPDATE ON trigger_test
    FOR EACH ROW
    EXECUTE FUNCTION trig_increment();

CREATE TRIGGER trg_decrement
    BEFORE UPDATE ON trigger_test
    FOR EACH ROW
    EXECUTE FUNCTION trig_decrement();

-- Test: Update value, triggers increment then decrement (net zero)
UPDATE trigger_test SET value = value WHERE id = 1;
-- Result: value unchanged (+1 then -1 = 0 net change)
-- Overhead: Two trigger executions, arithmetic operations, no data change

/*
TRIGGER EXECUTION ORDER:
PostgreSQL: Triggers fire in alphabetical order by trigger name
- trg_decrement fires first (alphabetically)
- trg_increment fires second
- Net effect depends on execution order
- With these names: decrement then increment = no net change
*/

-- TRIGGER NOP 6: Statement-Level Trigger with Empty Transition Table
CREATE OR REPLACE FUNCTION trig_statement_nop()
RETURNS TRIGGER AS $$
DECLARE
    row_count INTEGER;
BEGIN
    -- Count affected rows
    SELECT COUNT(*) INTO row_count FROM new_table;

    IF row_count = 0 THEN
        -- No rows affected, nothing to do
        RETURN NULL;
    END IF;

    -- Process rows (this code never runs if 0 rows affected)
    INSERT INTO summary_table (total_value)
    SELECT SUM(value) FROM new_table;

    RETURN NULL;

    /*
    CNO SCENARIO:
    - UPDATE with WHERE clause that matches 0 rows
    - Trigger fires at statement level
    - new_table transition table is empty
    - Function executes, detects 0 rows, exits early
    - Result: Statement-level trigger overhead, no processing
    */
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_statement_nop
    AFTER UPDATE ON trigger_test
    REFERENCING NEW TABLE AS new_table
    FOR EACH STATEMENT
    EXECUTE FUNCTION trig_statement_nop();

-- Test: Update 0 rows
UPDATE trigger_test SET value = 42 WHERE id < 0;
-- Result: 0 rows updated, trigger fires, processes empty set

-- ----------------------------------------------------------------------------
-- MYSQL: TRIGGER VARIATIONS
-- ----------------------------------------------------------------------------

-- TRIGGER NOP 7: MySQL BEFORE INSERT Null Return (via SIGNAL)
DELIMITER $$

CREATE TRIGGER trig_mysql_prevent_insert
BEFORE INSERT ON trigger_test
FOR EACH ROW
BEGIN
    DECLARE do_nothing INT;

    -- Condition that's always true
    IF 1 = 1 THEN
        -- Signal error to prevent insert (then handle in application)
        -- OR: Simply don't modify anything, allowing insert to proceed
        -- For true NOP: Let it proceed but set values to reject later
        SET NEW.value = NULL;  -- If value has NOT NULL constraint, insert fails
    END IF;

    /*
    MYSQL LIMITATION:
    - Cannot return NULL to cancel operation (like PostgreSQL)
    - Must use SIGNAL to raise error, or let operation proceed
    - For CNO: Use SIGNAL in transaction, then ROLLBACK
    */
END$$

DELIMITER ;

-- TRIGGER NOP 8: MySQL Self-Referential Update Prevention
DELIMITER $$

CREATE TRIGGER trig_mysql_self_reference
BEFORE UPDATE ON trigger_test
FOR EACH ROW
BEGIN
    -- Reset NEW to OLD values (no net change)
    SET NEW.value = OLD.value;
    SET NEW.modified_at = OLD.modified_at;

    /*
    MYSQL BEHAVIOR:
    - Trigger executes, modifies NEW
    - MySQL compares NEW to OLD
    - If identical, may skip actual row update (optimization)
    - Result: Trigger overhead, potential query cache impact, no data change
    */
END$$

DELIMITER ;

-- TRIGGER NOP 9: MySQL Multi-Table Update with Rollback
DELIMITER $$

CREATE TRIGGER trig_mysql_cascade_nop
AFTER INSERT ON trigger_test
FOR EACH ROW
BEGIN
    -- Insert into related table
    INSERT INTO trigger_log (message, related_id)
    VALUES ('Inserted row', NEW.id);

    -- If this trigger fires in a transaction that rolls back,
    -- both the original insert and this log entry disappear

    /*
    CNO SCENARIO:
    - BEGIN TRANSACTION
    - INSERT into trigger_test (fires trigger)
    - Trigger inserts into trigger_log
    - ROLLBACK
    - Result: Both inserts rolled back, trigger executed, zero net effect
    */
END$$

DELIMITER ;

-- Test with rollback:
START TRANSACTION;
INSERT INTO trigger_test (value) VALUES (200);
-- Trigger fires, inserts into trigger_log
ROLLBACK;
-- Both inserts rolled back, trigger executed for nothing

-- ----------------------------------------------------------------------------
-- SQLITE: TRIGGER SIMPLICITY
-- ----------------------------------------------------------------------------

-- TRIGGER NOP 10: SQLite WHEN Clause Optimization
CREATE TRIGGER IF NOT EXISTS trig_sqlite_conditional
AFTER INSERT ON trigger_test
WHEN (NEW.value < 0)  -- Condition rarely true
BEGIN
    -- Update statistics table
    UPDATE stats SET insert_count = insert_count + 1;
END;

-- Test: Insert positive value (trigger condition false, body not executed)
INSERT INTO trigger_test (value) VALUES (500);
-- Result: Row inserted, trigger condition evaluated, body skipped
-- SQLite optimization: WHEN clause evaluated before trigger body

-- TRIGGER NOP 11: SQLite Trigger Raising Exceptions
CREATE TRIGGER IF NOT EXISTS trig_sqlite_abort
BEFORE DELETE ON trigger_test
BEGIN
    -- Raise error to prevent deletion
    SELECT RAISE(ABORT, 'Deletion not allowed');
END;

-- Test: Attempt delete (trigger aborts operation)
DELETE FROM trigger_test WHERE id = 1;
-- Result: Error raised, deletion prevented, no state change
-- Note: In transaction, can ROLLBACK to handle gracefully

-- TRIGGER NOP 12: SQLite Self-Modifying Trigger Guard
CREATE TRIGGER IF NOT EXISTS trig_sqlite_guard
BEFORE UPDATE ON trigger_test
WHEN (NEW.value = OLD.value)
BEGIN
    -- This trigger only fires if value is unchanged
    -- Do nothing (or could update timestamp, but we won't)
    SELECT 1;  -- No-op statement
END;

-- Test: Update to same value
UPDATE trigger_test SET value = value WHERE id = 1;
-- Result: Trigger fires (condition true), executes SELECT 1, no side effects

-- ----------------------------------------------------------------------------
-- CROSS-DATABASE: TRIGGER PERFORMANCE ANALYSIS
-- ----------------------------------------------------------------------------

/*
TRIGGER OVERHEAD COMPARISON:

PostgreSQL:
- Trigger lookup: Hash table O(1)
- Function call: PL/pgSQL interpreter overhead
- WHEN clause: Evaluated before function call (optimization)
- Return NULL: Cancels operation cleanly
- Overhead: ~20-100 microseconds per trigger

MySQL:
- Trigger lookup: Linked list traversal O(n) triggers
- Native code: Compiled trigger body (faster than PL/pgSQL)
- WHEN clause: Not supported (conditional logic in body)
- Cannot cancel: Must use SIGNAL or complete operation
- Overhead: ~10-50 microseconds per trigger

SQLite:
- Trigger lookup: Simple array scan
- WHEN clause: Evaluated in bytecode (efficient)
- Single-threaded: No concurrency overhead
- Overhead: ~5-20 microseconds per trigger

CONCLUSION:
All databases have trigger overhead even for no-op operations.
Overhead includes: lookup, condition evaluation, function call.
For CNOs: Trigger executes successfully but produces zero state change.
*/

-- ----------------------------------------------------------------------------
-- ADVANCED TRIGGER NOPS
-- ----------------------------------------------------------------------------

-- TRIGGER NOP 13: Cascading Trigger Chain that Circles Back (PostgreSQL)
CREATE TABLE IF NOT EXISTS trigger_cascade_a (
    id SERIAL PRIMARY KEY,
    value INTEGER
);

CREATE TABLE IF NOT EXISTS trigger_cascade_b (
    id SERIAL PRIMARY KEY,
    value INTEGER
);

CREATE OR REPLACE FUNCTION trig_a_to_b()
RETURNS TRIGGER AS $$
BEGIN
    IF pg_trigger_depth() = 0 THEN
        UPDATE trigger_cascade_b SET value = NEW.value WHERE id = NEW.id;
    END IF;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION trig_b_to_a()
RETURNS TRIGGER AS $$
BEGIN
    IF pg_trigger_depth() <= 1 THEN
        UPDATE trigger_cascade_a SET value = NEW.value WHERE id = NEW.id;
    END IF;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_a_to_b
    AFTER UPDATE ON trigger_cascade_a
    FOR EACH ROW
    EXECUTE FUNCTION trig_a_to_b();

CREATE TRIGGER trg_b_to_a
    AFTER UPDATE ON trigger_cascade_b
    FOR EACH ROW
    EXECUTE FUNCTION trig_b_to_a();

/*
EXECUTION FLOW:
1. UPDATE trigger_cascade_a (depth=0)
   - Fires trig_a_to_b
   - Updates trigger_cascade_b (depth=1)
     - Fires trig_b_to_a
     - Attempts UPDATE trigger_cascade_a (depth=2)
     - Depth check: depth > 1, skips update
   - Returns
2. Cascade terminates

RESULT: Trigger chain executes, but terminates via depth guard
CNO: Multiple triggers fire, no infinite loop, controlled termination
*/

-- TRIGGER NOP 14: Audit Trail Trigger with Conditional Logging
CREATE TABLE IF NOT EXISTS audit_trail (
    id SERIAL PRIMARY KEY,
    table_name TEXT,
    operation TEXT,
    old_value JSONB,
    new_value JSONB,
    changed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE OR REPLACE FUNCTION trig_audit_selective()
RETURNS TRIGGER AS $$
BEGIN
    -- Only log if values actually changed
    IF NEW IS DISTINCT FROM OLD THEN
        INSERT INTO audit_trail (table_name, operation, old_value, new_value)
        VALUES (
            TG_TABLE_NAME,
            TG_OP,
            to_jsonb(OLD),
            to_jsonb(NEW)
        );
    END IF;

    RETURN NEW;

    /*
    CNO SCENARIO:
    - UPDATE with no actual value changes
    - Trigger fires, compares NEW and OLD
    - NEW IS DISTINCT FROM OLD evaluates to FALSE
    - Audit insert skipped
    - Result: Audit trigger overhead, no audit record created
    */
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER trg_audit_selective
    AFTER UPDATE ON trigger_test
    FOR EACH ROW
    EXECUTE FUNCTION trig_audit_selective();

-- Test: Update to same values (no audit entry)
UPDATE trigger_test SET value = value WHERE id = 1;
-- Result: Trigger fires, detects no change, skips audit

-- ----------------------------------------------------------------------------
-- TRIGGER NOP OPERATIONAL CHARACTERISTICS
-- ----------------------------------------------------------------------------

/*
TRIGGER-LEVEL CNO CHARACTERISTICS:

1. EVENT DETECTION: Database detects triggering event (INSERT/UPDATE/DELETE)
2. CONDITION EVALUATION: WHEN clause or conditional logic evaluated
3. FUNCTION EXECUTION: Trigger body executes (partially or fully)
4. ZERO STATE CHANGE: No persistent data modification
5. OVERHEAD: Trigger lookup, evaluation, execution time consumed
6. OBSERVABILITY: Trigger execution logged in query logs

USE CASES:

- Testing trigger logic without side effects
- Conditional triggers with edge cases (0 rows affected)
- Trigger guards that prevent operations
- Audit trail triggers that skip no-change updates
- Cascading triggers with termination conditions
- Deadlock prevention (triggers that detect and abort)

ANTI-PATTERNS:

- Overly complex trigger logic (hard to debug)
- Triggers with side effects in rolled-back transactions
- Infinite recursion without proper guards
- Using triggers for business logic (should be in application)

PERFORMANCE IMPACT:

- Row-level triggers: Overhead per row (can be significant for bulk operations)
- Statement-level triggers: Overhead per statement (amortized)
- WHEN clauses: Early termination optimization (use when possible)
- Trigger depth: Stack overhead for nested triggers

ACID PROPERTIES:

- Atomicity: Trigger is part of triggering transaction
- Consistency: Triggers can enforce constraints
- Isolation: Triggers see same snapshot as triggering statement
- Durability: Trigger effects rolled back if transaction rolls back

CONCLUSION:
Triggers are powerful but heavyweight. Even no-op triggers have measurable
overhead. For CNOs, triggers demonstrate that execution ≠ state change.
*/

-- ============================================================================
-- CLEANUP (Optional - uncomment to remove test objects)
-- ============================================================================

/*
DROP TRIGGER IF EXISTS trg_conditional_nop ON trigger_test;
DROP TRIGGER IF EXISTS trg_reset_changes ON trigger_test;
DROP TRIGGER IF EXISTS trg_never_fires ON trigger_test;
DROP TRIGGER IF EXISTS trg_recursive_nop ON trigger_test;
DROP TRIGGER IF EXISTS trg_increment ON trigger_test;
DROP TRIGGER IF EXISTS trg_decrement ON trigger_test;
DROP TRIGGER IF EXISTS trg_statement_nop ON trigger_test;
DROP TRIGGER IF EXISTS trg_audit_selective ON trigger_test;

DROP FUNCTION IF EXISTS trig_conditional_nop();
DROP FUNCTION IF EXISTS trig_reset_changes();
DROP FUNCTION IF EXISTS trig_never_fires();
DROP FUNCTION IF EXISTS trig_recursive_nop();
DROP FUNCTION IF EXISTS trig_increment();
DROP FUNCTION IF EXISTS trig_decrement();
DROP FUNCTION IF EXISTS trig_statement_nop();
DROP FUNCTION IF EXISTS trig_audit_selective();

DROP TABLE IF EXISTS trigger_test CASCADE;
DROP TABLE IF EXISTS trigger_cascade_a CASCADE;
DROP TABLE IF EXISTS trigger_cascade_b CASCADE;
DROP TABLE IF EXISTS audit_trail CASCADE;
*/

-- ============================================================================
-- END TRIGGER_NOP.SQL
-- ============================================================================
