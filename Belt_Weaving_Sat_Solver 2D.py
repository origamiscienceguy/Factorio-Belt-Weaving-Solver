# -*- coding: utf-8 -*-
import json
import os
import time
import math
import sys
import select

# Try to import msvcrt for Windows-specific key polling
try:
    import msvcrt
    OPERATING_SYSTEM = "windows"
except ImportError:
    OPERATING_SYSTEM = "linux"

from pysat.solvers import Cadical153
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc

# =============================================================================
# GLOBAL SEARCH PARAMETERS & GRID DIMENSIONS
# =============================================================================
GRID_WIDTH              = 24
GRID_HEIGHT             = 23
REPORT_INTERVAL_MINUTES = 1    
CHECK_IN_CONFLICT_LIMIT = 100000 
BRAID_DATA_FILE         = "braid_results.json"
TIER_ONE_BATCH_SIZE     = 100

# Visual map for the final ASCII weave output
COLOR_MAP = {0: ".", 1: "Y", 2: "R", 3: "B", 4: "G"}

# =============================================================================
# UTILITY FUNCTIONS: INPUT POLLING & STATISTICS
# =============================================================================

def format_seconds_to_hms(seconds_count):
    """Converts a raw float of seconds into a HH:MM:SS string."""
    hours_value, remainder = divmod(int(seconds_count), 3600)
    minutes_value, seconds_value = divmod(remainder, 60)
    return f"{hours_value:02d}:{minutes_value:02d}:{seconds_value:02d}"

def check_for_pause_signal():
    """
    Checks if the 'p' key has been pressed.
    Returns True only if 'p' is found in the buffer.
    """
    if OPERATING_SYSTEM == "windows":
        if msvcrt.kbhit():
            character = msvcrt.getch().decode('utf-8').lower()
            return character == 'p'
    else:
        # Non-blocking check for Linux/macOS
        input_list, _, _ = select.select([sys.stdin], [], [], 0)
        if input_list:
            character = sys.stdin.read(1).lower()
            return character == 'p'
    return False

def enter_pause_menu(current_context_label):
    """Halts execution and waits for user command (Resume/Terminate/Quit)."""
    print(f"\n{'!'*20} SEARCH PAUSED: {current_context_label} {'!'*20}")
    while True:
        user_command = input("Options: (r) Resume | (t) Terminate Density | (q) Quit Script: ").lower().strip()
        if user_command == 'r':
            print("[*] Resuming search...")
            return "RESUME"
        elif user_command == 't':
            print("[!] Terminating current permutation. Moving to next...")
            return "TERMINATE"
        elif user_command == 'q':
            print("[!] Exiting script.")
            sys.exit(0)

def print_braid_stats(braid_json_data, length):
    """Displays a breakdown of available braids by surfacing points (k)."""
    length_string = str(length)
    if length_string not in braid_json_data:
        return
    print(f"\n--- Braid Statistics for Length {length} ---")
    print(f"{'Occ %':<8} | {'Len':<4} | {'k':<4} | {'Count (Pure/Hybrid)':<15}")
    print("-" * 50)
    
    stats_list = []
    for belts in ["2", "3"]:
        belt_data = braid_json_data[length_string].get(belts, {})
        for k_value, content in belt_data.items():
            total_patterns = len(content.get("pure", [])) + len(content.get("hybrid", []))
            percentage = content.get("occupation_percentage", 0)
            stats_list.append((percentage, length, k_value, total_patterns))
            
    stats_list.sort(key=lambda x: x[0])
    for percentage, length_val, k, count in stats_list:
        print(f"{percentage:<8.2f} | {length_val:<4} | {k:<4} | {count:<15}")

# =============================================================================
# BRAID LIBRARY GENERATION
# =============================================================================

def get_braid_library_by_tier(braid_json_data, target_length, belt_count, min_k, target_tier):
    """Generates unique rotated/mirrored patterns for a specific k-value tier."""
    raw_patterns = []
    target_k = min_k + target_tier
    pattern_data = braid_json_data.get(str(target_length), {}).get(str(belt_count), {})
    
    tier_data = pattern_data.get(str(target_k), {})
    combined_raw_list = tier_data.get("pure", []) + tier_data.get("hybrid", [])
    
    for base_braid in combined_raw_list:
        mirrored_braid = [[p[1], p[0]] for p in base_braid[::-1]]
        for rotation_offset in range(target_length):
            for variant in [base_braid, mirrored_braid]:
                rotated = (variant + variant)[rotation_offset : rotation_offset + target_length]
                # Bitmask determines which tiles the braid surfaces on
                bitmask = tuple(1 if (p[0] > 0 or p[1] > 0) else 0 for p in rotated)
                raw_patterns.append({
                    "mask": bitmask, 
                    "data": rotated, 
                    "belts": belt_count, 
                    "cost": target_tier
                })
    
    unique_library = []
    seen_masks = set()
    for item in raw_patterns:
        if item["mask"] not in seen_masks:
            unique_library.append(item)
            seen_masks.add(item["mask"])
    return unique_library

# =============================================================================
# SAT SOLVER CORE LOGIC
# =============================================================================

def solve_weave_permutation(grid_width, grid_height, target_w3, target_h3, base_empty_limit, braid_json):
    """Main solver loop with non-blocking reporting and dynamic batching."""
    permutation_start_time = time.time()
    
    # Calculate k-value baselines
    row_stats, col_stats = braid_json[str(grid_width)], braid_json[str(grid_height)]
    row_min_k = {"2": min(int(k) for k in row_stats["2"]), "3": min(int(k) for k in row_stats["3"])}
    col_min_k = {"2": min(int(k) for k in col_stats["2"]), "3": min(int(k) for k in col_stats["3"])}

    # Fetch Base Libraries
    row_t0_lib = get_braid_library_by_tier(braid_json, grid_width, 2, row_min_k["2"], 0) + \
                 get_braid_library_by_tier(braid_json, grid_width, 3, row_min_k["3"], 0)
    col_t0_lib = get_braid_library_by_tier(braid_json, grid_height, 2, col_min_k["2"], 0) + \
                 get_braid_library_by_tier(braid_json, grid_height, 3, col_min_k["3"], 0)

    # Prepare Tier 1 categories for slicing
    r2_tier1 = get_braid_library_by_tier(braid_json, grid_width, 2, row_min_k["2"], 1)
    r3_tier1 = get_braid_library_by_tier(braid_json, grid_width, 3, row_min_k["3"], 1)
    c2_tier1 = get_braid_library_by_tier(braid_json, grid_height, 2, col_min_k["2"], 1)
    c3_tier1 = get_braid_library_by_tier(braid_json, grid_height, 3, col_min_k["3"], 1)

    max_t1_length = max(len(r2_tier1), len(r3_tier1), len(c2_tier1), len(c3_tier1))
    total_batches = math.ceil(max_t1_length / TIER_ONE_BATCH_SIZE) if max_t1_length > 0 else 0

    current_batch = 0
    while current_batch <= total_batches:
        if current_batch > 0 and base_empty_limit == 0: break
            
        current_time_str = format_seconds_to_hms(time.time() - permutation_start_time)

        # Batch Selection Logic
        if current_batch == 0:
            batch_label = "TIER 0"
            active_row_t1, active_col_t1 = [], []
        else:
            batch_label = f"Batch {current_batch}/{total_batches} (Tier 1)"
            batch_offset = (current_batch - 1) * TIER_ONE_BATCH_SIZE
            active_row_t1 = (r2_tier1[batch_offset:batch_offset+TIER_ONE_BATCH_SIZE] or r2_tier1[:TIER_ONE_BATCH_SIZE]) + \
                             (r3_tier1[batch_offset:batch_offset+TIER_ONE_BATCH_SIZE] or r3_tier1[:TIER_ONE_BATCH_SIZE])
            active_col_t1 = (c2_tier1[batch_offset:batch_offset+TIER_ONE_BATCH_SIZE] or c2_tier1[:TIER_ONE_BATCH_SIZE]) + \
                             (c3_tier1[batch_offset:batch_offset+TIER_ONE_BATCH_SIZE] or c3_tier1[:TIER_ONE_BATCH_SIZE])

        print(f"\n[{current_time_str}] --- Constructing SAT Formula: {batch_label} ---")
        
        # Immediate check for pause before starting construction
        if check_for_pause_signal():
            if enter_pause_menu(batch_label) == "TERMINATE": return False, ""

        id_pool = IDPool()
        formula = CNF()
        row_lib = row_t0_lib + active_row_t1
        col_lib = col_t0_lib + active_col_t1

        # 1. Braid Selection
        row_vars = [[id_pool.id(f"r{r}_{i}") for i in range(len(row_lib))] for r in range(grid_height)]
        col_vars = [[id_pool.id(f"c{c}_{i}") for i in range(len(col_lib))] for c in range(grid_width)]
        for rv in row_vars: formula.extend(CardEnc.equals(lits=rv, bound=1, vpool=id_pool).clauses)
        for cv in col_vars: formula.extend(CardEnc.equals(lits=cv, bound=1, vpool=id_pool).clauses)
        print(f" [1/5] Selection: {len(formula.clauses)} clauses.")

        # 2. Tier 1 Force-Usage
        if current_batch > 0:
            t1_lits = [row_vars[r][i] for r in range(grid_height) for i, p in enumerate(row_lib) if p["cost"] == 1]
            t1_lits += [col_vars[c][i] for c in range(grid_width) for i, p in enumerate(col_lib) if p["cost"] == 1]
            if t1_lits: formula.append(t1_lits)
            print(f" [2/5] Tier 1 Force: {len(formula.clauses)} total clauses.")

        # 3. 3-Braid Anchoring
        r3_ind = [id_pool.id(f"r3i_{r}") for r in range(grid_height)]
        c3_ind = [id_pool.id(f"c3i_{c}") for c in range(grid_width)]
        for r in range(grid_height):
            lits = [row_vars[r][i] for i, p in enumerate(row_lib) if p["belts"] == 3]
            formula.append([-r3_ind[r]] + lits); [formula.append([-l, r3_ind[r]]) for l in lits]
        for c in range(grid_width):
            lits = [col_vars[c][i] for i, p in enumerate(col_lib) if p["belts"] == 3]
            formula.append([-c3_ind[c]] + lits); [formula.append([-l, c3_ind[c]]) for l in lits]
        formula.extend(CardEnc.equals(lits=r3_ind, bound=target_w3, vpool=id_pool).clauses)
        formula.extend(CardEnc.equals(lits=c3_ind, bound=target_h3, vpool=id_pool).clauses)
        if target_w3 > 0: formula.append([r3_ind[0]])
        if target_h3 > 0: formula.append([c3_ind[0]])
        print(f" [3/5] Anchors: {len(formula.clauses)} total clauses.")

        # 4. Intersections
        empty_vars = []
        rs_mask = [[id_pool.id(f"rs_{r}_{c}") for c in range(grid_width)] for r in range(grid_height)]
        cs_mask = [[id_pool.id(f"cs_{c}_{r}") for r in range(grid_height)] for c in range(grid_width)]
        for r in range(grid_height):
            for c in range(grid_width):
                r_lits = [row_vars[r][i] for i, p in enumerate(row_lib) if p["mask"][c] == 1]
                formula.append([-rs_mask[r][c]] + r_lits); [formula.append([-l, rs_mask[r][c]]) for l in r_lits]
                c_lits = [col_vars[c][i] for i, p in enumerate(col_lib) if p["mask"][r] == 1]
                formula.append([-cs_mask[c][r]] + c_lits); [formula.append([-l, cs_mask[c][r]]) for l in c_lits]
                formula.append([-rs_mask[r][c], -cs_mask[c][r]])
                ev = id_pool.id(f"e_{r}_{c}"); empty_vars.append(ev)
                formula.append([rs_mask[r][c], cs_mask[c][r], ev])
        formula.append([cs_mask[0][0]])
        print(f" [4/5] Intersections: {len(formula.clauses)} total clauses.")

        # 5. Budgeting
        cost_lits = []
        for r in range(grid_height):
            for i, p in enumerate(row_lib):
                if p["cost"] == 1: cost_lits.append(row_vars[r][i])
        for c in range(grid_width):
            for i, p in enumerate(col_lib):
                if p["cost"] == 1: cost_lits.append(col_vars[c][i])
        formula.extend(CardEnc.atmost(lits=empty_vars + cost_lits, bound=base_empty_limit, vpool=id_pool).clauses)
        print(f" [5/5] Solver starting. (Press 'p' anytime to pause)")

        # SOLVER LOOP
        active_solver = Cadical153(bootstrap_with=formula.clauses)
        last_report_timestamp = time.time()
        
        try:
            while True:
                active_solver.conf_budget(CHECK_IN_CONFLICT_LIMIT)
                status = active_solver.solve_limited()
                
                # Check if it's time for a report
                time_now = time.time()
                report_due = (time_now - last_report_timestamp) >= (REPORT_INTERVAL_MINUTES * 60)
                
                # Check for pause signal (Non-blocking)
                pause_triggered = check_for_pause_signal()

                if report_due or pause_triggered:
                    total_elapsed = time_now - permutation_start_time
                    stats = active_solver.accum_stats()
                    conflicts = stats.get('conflicts', 0)
                    
                    print(f"\n--- {batch_label} PROGRESS (Elapsed: {format_seconds_to_hms(total_elapsed)}) ---")
                    print(f" Conflicts: {conflicts:,} | Rate: {conflicts/max(1,total_elapsed):.1f}/s")
                    
                    # ONLY BLOCK IF 'p' WAS PRESSED
                    if pause_triggered:
                        if enter_pause_menu(batch_label) == "TERMINATE": return False, ""
                    
                    last_report_timestamp = time.time()

                if status is not None:
                    if status:
                        model_set = set(active_solver.get_model())
                        return True, construct_grid_visual(grid_width, grid_height, row_vars, col_vars, [row_lib]*grid_height, [col_lib]*grid_width, model_set)
                    print(f"[*] {batch_label} is UNSAT.")
                    break
        finally:
            active_solver.delete()
        current_batch += 1
    return False, ""

def construct_grid_visual(width, height, rv, cv, r_libs, c_libs, model):
    """Parses the model back into ASCII."""
    rows = {r: r_libs[r][i] for r in range(height) for i, v in enumerate(rv[r]) if v in model}
    cols = {c: c_libs[c][i] for c in range(width) for i, v in enumerate(cv[c]) if v in model}
    output_lines = []
    for r in range(height):
        cell_data = []
        for c in range(width):
            hp, vp = rows[r]["data"][c], cols[c]["data"][r]
            if hp[0] > 0 or hp[1] > 0: cell_data.append(f"H{COLOR_MAP[hp[0]]}{COLOR_MAP[hp[1]]}")
            elif vp[0] > 0 or vp[1] > 0: cell_data.append(f"V{COLOR_MAP[vp[0]]}{COLOR_MAP[vp[1]]}")
            else: cell_data.append("...")
        output_lines.append(" ".join(cell_data))
    return "\n".join(output_lines)

def main():
    print(f"\n{'='*80}\n INITIALIZING WEAVE SOLVER | DIMENSIONS: {GRID_WIDTH}x{GRID_HEIGHT}\n{'='*80}")
    if not os.path.exists(BRAID_DATA_FILE): return
    with open(BRAID_DATA_FILE, 'r') as f: braid_data = json.load(f).get("lengths", {})
    
    print_braid_stats(braid_data, GRID_WIDTH)
    if GRID_WIDTH != GRID_HEIGHT: print_braid_stats(braid_data, GRID_HEIGHT)

    # Queue Construction
    tasks = []
    for w3 in range(GRID_HEIGHT + 1):
        for h3 in range(GRID_WIDTH + 1):
            w2, h2 = GRID_HEIGHT - w3, GRID_WIDTH - h3
            rk2, rk3 = min(int(k) for k in braid_data[str(GRID_WIDTH)]["2"]), min(int(k) for k in braid_data[str(GRID_WIDTH)]["3"])
            ck2, ck3 = min(int(k) for k in braid_data[str(GRID_HEIGHT)]["2"]), min(int(k) for k in braid_data[str(GRID_HEIGHT)]["3"])
            surf = (w3 * rk3) + (w2 * rk2) + (h3 * ck3) + (h2 * ck2)
            empty = (GRID_WIDTH * GRID_HEIGHT) - surf
            if empty < 0: continue
            dens = (((w3 * 3) + (w2 * 2)) / GRID_HEIGHT) + (((h3 * 3) + (h2 * 2)) / GRID_WIDTH)
            tasks.append({"score": dens, "w3": w3, "h3": h3, "empty": int(empty)})
            
    tasks.sort(key=lambda x: x["score"], reverse=True)
    for i, t in enumerate(tasks): t["id"] = i

    print(f"\n{'ID':<4} | {'Density':<10} | {'W3/H3':<8} | {'Budget':<10}")
    print("-" * 45)
    for t in tasks[:15]: print(f"{t['id']:<4} | {t['score']:<10.4f} | {t['w3']:>2}/{t['h3']:<2} | {t['empty']:<10}")
    
    user_sel = input("\nEnter IDs (comma-sep) or Enter for auto: ").strip()
    queue = [tasks[int(x)] for x in user_sel.split(",")] if user_sel else tasks
    
    for task in queue:
        print(f"\n[*] Solving Density {task['score']:.4f} (W3:{task['w3']} H3:{task['h3']})")
        found, result = solve_weave_permutation(GRID_WIDTH, GRID_HEIGHT, task['w3'], task['h3'], task['empty'], braid_data)
        if found:
            print(f"\n{'#'*80}\n SUCCESSFUL WEAVE FOUND")
            print(f" DIMENSIONS: {GRID_WIDTH}x{GRID_HEIGHT} | DENSITY: {task['score']:.4f} | BUDGET: {task['empty']}")
            print(f"{'#'*80}\n{result}")
            break

if __name__ == "__main__":
    main()