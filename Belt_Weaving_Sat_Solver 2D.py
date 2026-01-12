# -*- coding: utf-8 -*-
import json
import os
import time
import math
from pysat.solvers import Cadical153
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc

# =============================================================================
# GLOBAL SEARCH PARAMETERS & GRID DIMENSIONS
# =============================================================================
GRID_WIDTH              = 20
GRID_HEIGHT             = 5
REPORT_INTERVAL_MINUTES = 1    
CHECK_IN_CONFLICT_LIMIT = 100000 
BRAID_DATA_FILE         = "braid_results.json"
TIER_ONE_BATCH_SIZE     = 100

# Visual map for the final ASCII weave output
# 0: Empty, 1: Yellow, 2: Red, 3: Blue, 4: Green
COLOR_MAP = {0: ".", 1: "Y", 2: "R", 3: "B", 4: "G"}

# =============================================================================
# PROGRESS TRACKING & STATISTICS
# =============================================================================

class ProgressTracker:
    """Provides a clean readout of solver throughput and performance metrics."""
    def __init__(self, batch_label):
        self.initial_timestamp = time.time()
        self.label = batch_label
        
    def format_duration(self, total_seconds):
        """Converts seconds into a readable D-H-M-S format."""
        days, remainder = divmod(total_seconds, 86400)
        hours, remainder = divmod(remainder, 3600)
        minutes, seconds = divmod(remainder, 60)
        segments = []
        if days > 0: segments.append(f"{int(days)}d")
        if hours > 0: segments.append(f"{int(hours)}h")
        if minutes > 0: segments.append(f"{int(minutes)}m")
        segments.append(f"{int(seconds)}s")
        return " ".join(segments)

    def print_progress_report(self, active_solver):
        """Calculates and prints performance metrics."""
        current_time = time.time()
        elapsed_seconds = max(current_time - self.initial_timestamp, 1)
        solver_statistics = active_solver.accum_stats()
        conflicts_count = solver_statistics.get('conflicts', 0)
        conflicts_per_second = conflicts_count / elapsed_seconds

        print(f"\n{'='*60}")
        print(f" [{self.label} PERFORMANCE REPORT]")
        print(f" Elapsed Time:           {self.format_duration(elapsed_seconds)}")
        print(f" Total Conflicts:        {conflicts_count:,}")
        print(f" Throughput:             {conflicts_per_second:,.2f} conflicts/sec")
        print(f"{'='*60}\n")

# =============================================================================
# BRAID LIBRARY GENERATION
# =============================================================================

def get_braid_library_by_tier(braid_json_data, target_length, belt_count, min_k, target_tier):
    """Fetches braids for a specific length/belt count that match a specific tier cost."""
    generated_patterns = []
    target_k = min_k + target_tier
    pattern_data = braid_json_data.get(str(target_length), {}).get(str(belt_count), {})
    
    content = pattern_data.get(str(target_k), {})
    category_patterns = content.get("pure", []) + content.get("hybrid", [])
    
    for base_pattern in category_patterns:
        mirrored_pattern = [[pair[1], pair[0]] for pair in base_pattern[::-1]]
        for shift_index in range(target_length):
            for variant in [base_pattern, mirrored_pattern]:
                rotated = (variant + variant)[shift_index : shift_index + target_length]
                mask = tuple(1 if (point[0] > 0 or point[1] > 0) else 0 for point in rotated)
                generated_patterns.append({
                    "mask": mask, 
                    "data": rotated, 
                    "belts": belt_count, 
                    "cost": target_tier,
                    "length": target_length
                })
    
    unique_library = []
    seen_bitmasks = set()
    for item in generated_patterns:
        if item["mask"] not in seen_bitmasks:
            unique_library.append(item)
            seen_bitmasks.add(item["mask"])
    return unique_library

# =============================================================================
# VISUALIZATION HELPERS
# =============================================================================

def construct_grid_visual(width, height, row_choice_vars, col_choice_vars, row_libraries, col_libraries, sat_model):
    """Translates the solver's boolean model into a readable ASCII weave."""
    chosen_rows = {r: row_libraries[r][v_idx] for r in range(height) for v_idx, var in enumerate(row_choice_vars[r]) if var in sat_model}
    chosen_cols = {c: col_libraries[c][v_idx] for c in range(width) for v_idx, var in enumerate(col_choice_vars[c]) if var in sat_model}
    
    lines = []
    for r_idx in range(height):
        row_str = []
        for c_idx in range(width):
            h_pair = chosen_rows[r_idx]["data"][c_idx]
            v_pair = chosen_cols[c_idx]["data"][r_idx]
            if h_pair[0] > 0 or h_pair[1] > 0: 
                row_str.append(f"H{COLOR_MAP[h_pair[0]]}{COLOR_MAP[h_pair[1]]}")
            elif v_pair[0] > 0 or v_pair[1] > 0: 
                row_str.append(f"V{COLOR_MAP[v_pair[0]]}{COLOR_MAP[v_pair[1]]}")
            else: 
                row_str.append("...")
        lines.append(" ".join(row_str))
    return "\n".join(lines)

# =============================================================================
# SAT SOLVER CORE LOGIC
# =============================================================================

def solve_weave_permutation(grid_width, grid_height, target_w3, target_h3, base_empty_limit, braid_json):
    """Orchestrates the search from Tier 0 through batched Tier 1 attempts."""
    
    # 1. ORGANIZE LIBRARIES
    row_stats, col_stats = braid_json[str(grid_width)], braid_json[str(grid_height)]
    row_min_k = {"2": min(int(k) for k in row_stats["2"]), "3": min(int(k) for k in row_stats["3"])}
    col_min_k = {"2": min(int(k) for k in col_stats["2"]), "3": min(int(k) for k in col_stats["3"])}

    # Base Tier 0 Library (Optimal)
    row_t0 = get_braid_library_by_tier(braid_json, grid_width, 2, row_min_k["2"], 0) + \
             get_braid_library_by_tier(braid_json, grid_width, 3, row_min_k["3"], 0)
    col_t0 = get_braid_library_by_tier(braid_json, grid_height, 2, col_min_k["2"], 0) + \
             get_braid_library_by_tier(braid_json, grid_height, 3, col_min_k["3"], 0)

    # Search Task List
    search_tasks = [(0, 0, [])] # (TierLevel, BatchID, T1_Subset)

    # 2. SANITY CHECK & TIER 1 BATCHING
    if base_empty_limit > 0:
        row_t1_all = get_braid_library_by_tier(braid_json, grid_width, 2, row_min_k["2"], 1) + \
                     get_braid_library_by_tier(braid_json, grid_width, 3, row_min_k["3"], 1)
        col_t1_all = get_braid_library_by_tier(braid_json, grid_height, 2, col_min_k["2"], 1) + \
                     get_braid_library_by_tier(braid_json, grid_height, 3, col_min_k["3"], 1)
        
        all_t1 = row_t1_all + col_t1_all
        num_batches = math.ceil(len(all_t1) / TIER_ONE_BATCH_SIZE)
        for i in range(num_batches):
            search_tasks.append((1, i + 1, all_t1[i * TIER_ONE_BATCH_SIZE : (i + 1) * TIER_ONE_BATCH_SIZE]))
    else:
        print("[*] Sanity Check: base_empty_limit is 0. Skipping Tier 1 batches.")
        num_batches = 0

    # 3. EXECUTE SEARCH
    for tier_level, batch_num, t1_subset in search_tasks:
        label = "TIER 0" if tier_level == 0 else f"TIER 1 (Batch {batch_num} of {num_batches})"
        print(f"\n[*] --- STARTING {label} ---")
        
        id_pool = IDPool()
        formula = CNF()
        
        # Merge T0 with current T1 subset
        current_row_lib = row_t0 + [p for p in t1_subset if p["length"] == grid_width]
        current_col_lib = col_t0 + [p for p in t1_subset if p["length"] == grid_height]

        print(f"    > Building Formula... (Rows: {len(current_row_lib)}, Cols: {len(current_col_lib)})")

        row_vars = [[id_pool.id(f"r{r}_{i}") for i in range(len(current_row_lib))] for r in range(grid_height)]
        col_vars = [[id_pool.id(f"c{c}_{i}") for i in range(len(current_col_lib))] for c in range(grid_width)]
        for r_v in row_vars: formula.extend(CardEnc.equals(lits=r_v, bound=1, vpool=id_pool).clauses)
        for c_v in col_vars: formula.extend(CardEnc.equals(lits=c_v, bound=1, vpool=id_pool).clauses)

        if tier_level == 1:
            t1_lits = [row_vars[r][i] for r in range(grid_height) for i, p in enumerate(current_row_lib) if p["cost"] == 1]
            t1_lits += [col_vars[c][i] for c in range(grid_width) for i, p in enumerate(current_col_lib) if p["cost"] == 1]
            if t1_lits: formula.append(t1_lits)

        empty_flags = []
        rs_mask = [[id_pool.id(f"rs_{r}_{c}") for c in range(grid_width)] for r in range(grid_height)]
        cs_mask = [[id_pool.id(f"cs_{c}_{r}") for r in range(grid_height)] for c in range(grid_width)]
        
        for r in range(grid_height):
            for c in range(grid_width):
                r_lits = [row_vars[r][i] for i, p in enumerate(current_row_lib) if p["mask"][c] == 1]
                formula.append([-rs_mask[r][c]] + r_lits); [formula.append([-l, rs_mask[r][c]]) for l in r_lits]
                c_lits = [col_vars[c][i] for i, p in enumerate(current_col_lib) if p["mask"][r] == 1]
                formula.append([-cs_mask[c][r]] + c_lits); [formula.append([-l, cs_mask[c][r]]) for l in c_lits]
                formula.append([-rs_mask[r][c], -cs_mask[c][r]])
                e_var = id_pool.id(f"e_{r}_{c}"); empty_flags.append(e_var)
                formula.append([rs_mask[r][c], cs_mask[c][r], e_var])

        r3_v = [id_pool.id(f"r3b_{r}") for r in range(grid_height)]
        c3_v = [id_pool.id(f"c3b_{c}") for c in range(grid_width)]
        for r in range(grid_height):
            lits = [row_vars[r][i] for i, p in enumerate(current_row_lib) if p["belts"] == 3]
            formula.append([-r3_v[r]] + lits); [formula.append([-l, r3_v[r]]) for l in lits]
        for c in range(grid_width):
            lits = [col_vars[c][i] for i, p in enumerate(current_col_lib) if p["belts"] == 3]
            formula.append([-c3_v[c]] + lits); [formula.append([-l, c3_v[c]]) for l in lits]
        formula.extend(CardEnc.equals(lits=r3_v, bound=target_w3, vpool=id_pool).clauses)
        formula.extend(CardEnc.equals(lits=c3_v, bound=target_h3, vpool=id_pool).clauses)
        if target_w3 > 0: formula.append([r3_v[0]])
        if target_h3 > 0: formula.append([c3_v[0]])
        formula.append([cs_mask[0][0]]) # Anchor: Vertical surface at 0,0

        cost_lits = []
        for r in range(grid_height):
            for i, p in enumerate(current_row_lib):
                if p["cost"] == 1: cost_lits.append(row_vars[r][i])
        for c in range(grid_width):
            for i, p in enumerate(current_col_lib):
                if p["cost"] == 1: cost_lits.append(col_vars[c][i])
        formula.extend(CardEnc.atmost(lits=empty_flags + cost_lits, bound=base_empty_limit, vpool=id_pool).clauses)

        tracker = ProgressTracker(label)
        solver = Cadical153(bootstrap_with=formula.clauses)
        last_rep = 0
        try:
            while True:
                solver.conf_budget(CHECK_IN_CONFLICT_LIMIT)
                status = solver.solve_limited()
                if time.time() - last_rep >= (REPORT_INTERVAL_MINUTES * 60):
                    tracker.print_progress_report(solver); last_rep = time.time()
                if status is not None:
                    if status:
                        return True, construct_grid_visual(grid_width, grid_height, row_vars, col_vars, [current_row_lib]*grid_height, [current_col_lib]*grid_width, set(solver.get_model()))
                    print(f"[*] {label} UNSAT.")
                    break
        finally:
            solver.delete()
    return False, ""

# =============================================================================
# MAIN & STATISTICS
# =============================================================================

def print_braid_stats(braid_data, length):
    """Generates the statistical report for a given length."""
    length_str = str(length)
    if length_str not in braid_data: return
    print(f"\n--- Braid Statistics for Length {length} ---")
    print(f"{'Occ %':<8} | {'Len':<4} | {'k':<4} | {'Count':<8}")
    print("-" * 35)
    stats_rows = []
    for belt_count in ["2", "3"]:
        if belt_count in braid_data[length_str]:
            for k_val, data in braid_data[length_str][belt_count].items():
                total_count = len(data.get("pure", [])) + len(data.get("hybrid", []))
                if total_count > 0:
                    stats_rows.append((data.get("occupation_percentage", 0), length, int(k_val), total_count))
    stats_rows.sort(key=lambda x: x[0])
    for row in stats_rows:
        print(f"{row[0]:<8.2f} | {row[1]:<4} | {row[2]:<4} | {row[3]:<8}")

def main():
    print(f"\n{'='*80}\n INITIALIZING WEAVE SOLVER | DIMENSIONS: {GRID_WIDTH}x{GRID_HEIGHT}\n{'='*80}")
    if not os.path.exists(BRAID_DATA_FILE):
        print(f"[!] Braid data file '{BRAID_DATA_FILE}' not found."); return
    with open(BRAID_DATA_FILE, 'r') as fh:
        raw_json = json.load(fh)
        braid_data = raw_json.get("lengths", {})
    
    print_braid_stats(braid_data, GRID_WIDTH)
    if GRID_WIDTH != GRID_HEIGHT: print_braid_stats(braid_data, GRID_HEIGHT)

    row_stats, col_stats = braid_data[str(GRID_WIDTH)], braid_data[str(GRID_HEIGHT)]
    row_min_k2, row_min_k3 = min(int(k) for k in row_stats["2"]), min(int(k) for k in row_stats["3"])
    col_min_k2, col_min_k3 = min(int(k) for k in col_stats["2"]), min(int(k) for k in col_stats["3"])

    permutation_queue = []
    for w3_count in range(GRID_HEIGHT + 1):
        for h3_count in range(GRID_WIDTH + 1):
            w2_count, h2_count = GRID_HEIGHT - w3_count, GRID_WIDTH - h3_count
            total_surfacing = (w3_count * row_min_k3) + (w2_count * row_min_k2) + \
                              (h3_count * col_min_k3) + (h2_count * col_min_k2)
            empty_tile_budget = (GRID_WIDTH * GRID_HEIGHT) - total_surfacing
            if empty_tile_budget < 0: continue
            density = (((w3_count * 3) + (w2_count * 2)) / GRID_HEIGHT) + \
                      (((h3_count * 3) + (h2_count * 2)) / GRID_WIDTH)
            permutation_queue.append({"score": density, "w3": w3_count, "h3": h3_count, "empty": int(empty_tile_budget)})
            
    permutation_queue.sort(key=lambda x: x["score"], reverse=True)
    for index, p_item in enumerate(permutation_queue): p_item["id"] = index

    print(f"\n{'ID':<4} | {'Density':<10} | {'W3/H3':<8} | {'Empty Budget':<12}")
    print("-" * 45)
    for p_item in permutation_queue[:15]:
        print(f"{p_item['id']:<4} | {p_item['score']:<10.4f} | {p_item['w3']:>2}/{p_item['h3']:<2} | {p_item['empty']:<12}")
    
    user_selection = input("\nEnter IDs to search or Enter for auto-priority: ").strip()
    active_queue = [permutation_queue[int(x)] for x in user_selection.split(",")] if user_selection else permutation_queue
    
    for task_item in active_queue:
        print(f"\n[*] Solving Density {task_item['score']:.4f} (W3:{task_item['w3']} H3:{task_item['h3']})")
        found, grid = solve_weave_permutation(GRID_WIDTH, GRID_HEIGHT, task_item['w3'], task_item['h3'], task_item['empty'], braid_data)
        if found:
            print(f"\n{'#'*80}\n SUCCESSFUL WEAVE FOUND\n{'#'*80}\n{grid}")
            print(f"\n Dimensions: {GRID_WIDTH}x{GRID_HEIGHT} | Density: {task_item['score']:.4f}"); break

if __name__ == "__main__":
    main()