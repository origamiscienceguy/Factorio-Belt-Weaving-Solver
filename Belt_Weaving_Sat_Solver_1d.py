# -*- coding: utf-8 -*-
import json
import math
import sys
import os
from pysat.solvers import Cadical153
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc

# =============================================================================
# USER CONFIGURATION
# =============================================================================
STARTING_LENGTH_DEFAULT = 4
ENDING_LENGTH           = 34  
VERBOSE_MODE            = 1  
JSON_OUTPUT_FILE        = "braid_results.json"

# Optimization Thresholds
RATIO_TWO_BELT   = 0.374
RATIO_THREE_BELT = 0.646

BELT_PROPERTIES = {
    1: {"name": "Yellow", "reach": 3, "label": "Y"},
    2: {"name": "Red",    "reach": 4, "label": "R"},
    3: {"name": "Blue",   "reach": 5, "label": "B"},
    4: {"name": "Green",  "reach": 6, "label": "G"}
}

# =============================================================================
# SYMMETRY UTILITIES
# =============================================================================

def generate_symmetry_masks(occupation_mask):
    """
    Creates all rotations and reflections of a binary occupation pattern.
    Used to prevent the solver from finding the same solution in a different orientation.
    """
    symmetries = set()
    length = len(occupation_mask)
    current_mask = list(occupation_mask)
    for _ in range(length):
        symmetries.add(tuple(current_mask))
        symmetries.add(tuple(current_mask[::-1]))
        current_mask = [current_mask[-1]] + current_mask[:-1]
    return symmetries

def forbid_architecture(solver, mask, tile_vars_dict, active_colors=None):
    """
    Adds a clause to the SAT solver to block a specific pattern of occupied/empty tiles.
    """
    blocking_clause = []
    for tile_index, is_occupied in enumerate(mask):
        if is_occupied == 1:
            # If the pattern expects a belt here, we add the 'Empty' literal to the clause
            # (Logic: To avoid this pattern, this tile must be Empty OR...)
            blocking_clause.append(tile_vars_dict[tile_index][0])
        else:
            # If the pattern expects Empty here, we add 'Occupied' literals
            if active_colors:
                for color in active_colors:
                    blocking_clause.append(tile_vars_dict[tile_index][color])
            else:
                for color in [2, 3, 4]:
                    blocking_clause.append(tile_vars_dict[tile_index][color])
    solver.add_clause(blocking_clause)

# =============================================================================
# SOLVER 1: PURE BRAIDS
# =============================================================================

def solve_pure_braids(belt_length, belt_count, k_value, blocked_patterns):
    variable_pool = IDPool()
    cnf_formula = CNF()
    
    # Pure braids only use specific tiers based on belt count
    allowed_colors = [2, 3, 4]
    required_colors = [3, 4] if belt_count == 2 else [2, 3, 4]
    labels = {0: ".", 2: "R", 3: "B", 4: "G"}

    # tile_vars[tile_index][color_code]
    tile_vars = {i: {c: variable_pool.id(f"t{i}_{c}") for c in [0] + allowed_colors} for i in range(belt_length)}

    # Constraint 1: Tile 0 is always Empty
    cnf_formula.append([tile_vars[0][0]])

    # Constraint 2: Each tile has exactly one state
    for i in range(belt_length):
        cnf_formula.extend(CardEnc.equals(lits=list(tile_vars[i].values()), bound=1, vpool=variable_pool).clauses)

    # Constraint 3: Exactly k tiles are non-empty
    empty_literals = [tile_vars[i][0] for i in range(belt_length)]
    cnf_formula.extend(CardEnc.equals(lits=empty_literals, bound=belt_length - k_value, vpool=variable_pool).clauses)

    # Constraint 4: Reach (If a color exists, another of same color must be within reach)
    for i in range(belt_length):
        for c in allowed_colors:
            reach = BELT_PROPERTIES[c]["reach"]
            targets = [tile_vars[(i + d) % belt_length][c] for d in range(1, reach + 1)]
            cnf_formula.append([-tile_vars[i][c]] + targets)
            
    # Constraint 5: Required colors must appear at least once
    for c in required_colors:
        cnf_formula.append([tile_vars[i][c] for i in range(belt_length)])

    # Execution
    solver = Cadical153(bootstrap_with=cnf_formula.clauses)
    for mask in blocked_patterns:
        forbid_architecture(solver, mask, tile_vars)

    while solver.solve():
        model = set(solver.get_model())
        visual_str, raw_pairs, occ_mask = [], [], []
        
        for i in range(belt_length):
            c = next(col for col in [0] + allowed_colors if tile_vars[i][col] in model)
            visual_str.append(f"{labels[c]}{labels[c]} ")
            raw_pairs.append([c, c])
            occ_mask.append(0 if c == 0 else 1)
        
        yield "".join(visual_str), raw_pairs
        
        for sym in generate_symmetry_masks(occ_mask):
            blocked_patterns.add(tuple(sym))
            forbid_architecture(solver, sym, tile_vars)
    solver.delete()

# =============================================================================
# SOLVER 2: HYBRID BRAIDS (Fixed Logic)
# =============================================================================

def solve_hybrid_braids(belt_length, belt_count, k_value, blocked_patterns):
    variable_pool = IDPool()
    cnf_formula = CNF()
    
    active_colors = [1, 2, 3, 4]
    all_options = [0] + active_colors
    labels = {0: ".", 1: "Y", 2: "R", 3: "B", 4: "G"}

    # --- Variables ---
    # asc_vars[i][c]: Color c ascends at tile i
    # dsc_vars[i][c]: Color c descends at tile i
    asc_vars = {i: {c: variable_pool.id(f"asc_{i}_{c}") for c in all_options} for i in range(belt_length)}
    dsc_vars = {i: {c: variable_pool.id(f"dsc_{i}_{c}") for c in all_options} for i in range(belt_length)}
    
    # under_vars[i][c]: Color c is "underground" in the gap AFTER tile i
    under_vars = {i: {c: variable_pool.id(f"u_{i}_{c}") for c in active_colors} for i in range(belt_length)}

    # --- Basic Structure ---
    cnf_formula.append([asc_vars[0][0]]) # Tile 0 Empty
    cnf_formula.append([dsc_vars[0][0]])

    # Global Density (k)
    empty_flags = [asc_vars[i][0] for i in range(belt_length)]
    cnf_formula.extend(CardEnc.equals(lits=empty_flags, bound=belt_length - k_value, vpool=variable_pool).clauses)

    for i in range(belt_length):
        # Unique state per tile
        cnf_formula.extend(CardEnc.equals(lits=list(asc_vars[i].values()), bound=1, vpool=variable_pool).clauses)
        cnf_formula.extend(CardEnc.equals(lits=list(dsc_vars[i].values()), bound=1, vpool=variable_pool).clauses)
        # Empty consistency (Asc and Dsc must match if Empty)
        cnf_formula.append([-asc_vars[i][0], dsc_vars[i][0]])
        cnf_formula.append([-dsc_vars[i][0], asc_vars[i][0]])

    # --- Reach Logic ---
    for i in range(belt_length):
        for c in active_colors:
            reach = BELT_PROPERTIES[c]["reach"]
            targets = [asc_vars[(i + d) % belt_length][c] for d in range(1, reach + 1)]
            cnf_formula.append([-dsc_vars[i][c]] + targets)

    # --- Flow & Belt Counting Logic ---
    for c in active_colors:
        
        # ** GHOST BELT PREVENTION **
        # A belt cannot be underground at the boundary if it NEVER descends in the entire loop.
        # u[last][c] -> (dsc[0][c] OR dsc[1][c] ... OR dsc[L][c])
        all_descents_for_color = [dsc_vars[i][c] for i in range(belt_length)]
        cnf_formula.append([-under_vars[belt_length - 1][c]] + all_descents_for_color)

        for i in range(belt_length):
            u_curr = under_vars[i][c]
            u_prev = under_vars[(i - 1) % belt_length][c]
            a_curr = asc_vars[i][c]
            d_curr = dsc_vars[i][c]

            # 1. Ascent needs Source: Cannot Ascend unless coming from Underground
            cnf_formula.append([-a_curr, u_prev])

            # 2. Descent needs Vacancy: Cannot Descend if already Underground (unless surfacing same tile)
            # Dsc -> (NOT u_prev OR Asc)
            cnf_formula.append([-d_curr, -u_prev, a_curr])

            # 3. Underground State Transition
            # Next is Underground IF (We Descended) OR (We were Underground AND didn't Ascend)
            # u_curr <-> d_curr OR (u_prev AND NOT a_curr)
            
            # Forward: d_curr -> u_curr
            cnf_formula.append([-d_curr, u_curr])
            # Forward: u_prev AND NOT a_curr -> u_curr
            cnf_formula.append([-u_prev, a_curr, u_curr])
            
            # Backward: u_curr -> d_curr OR u_prev
            cnf_formula.append([-u_curr, d_curr, u_prev])
            # Backward: u_curr -> d_curr OR NOT a_curr
            cnf_formula.append([-u_curr, d_curr, -a_curr])

    # Force Exact Belt Count at Boundary
    boundary_lits = [under_vars[belt_length - 1][c] for c in active_colors]
    cnf_formula.extend(CardEnc.equals(lits=boundary_lits, bound=belt_count, vpool=variable_pool).clauses)

    # --- Execution ---
    solver = Cadical153(bootstrap_with=cnf_formula.clauses)
    
    # Block patterns (Hybrid uses Asc vars to check occupation)
    for mask in blocked_patterns:
        forbid_architecture(solver, mask, asc_vars, active_colors)

    while solver.solve():
        model = set(solver.get_model())
        visual_str, raw_pairs, occ_mask = [], [], []
        
        for i in range(belt_length):
            a = next(c for c in all_options if asc_vars[i][c] in model)
            d = next(c for c in all_options if dsc_vars[i][c] in model)
            visual_str.append(f"{labels[a]}{labels[d]} ")
            raw_pairs.append([a, d])
            occ_mask.append(0 if a == 0 else 1)
            
        yield "".join(visual_str), raw_pairs
        
        for sym in generate_symmetry_masks(occ_mask):
            blocked_patterns.add(tuple(sym))
            forbid_architecture(solver, sym, asc_vars, active_colors)
            
    solver.delete()

# =============================================================================
# MAIN LOOP
# =============================================================================

def main():
    json_data = {"metadata": {"min_length": STARTING_LENGTH_DEFAULT, "max_length": ENDING_LENGTH}, "lengths": {}}
    
    start_at = STARTING_LENGTH_DEFAULT
    if os.path.exists(JSON_OUTPUT_FILE):
        try:
            with open(JSON_OUTPUT_FILE, 'r') as f:
                d = json.load(f)
                if "lengths" in d and d["lengths"]:
                    json_data = d
                    start_at = max([int(k) for k in d["lengths"].keys()]) + 1
                    print(f"[*] Resuming from Length {start_at}...")
        except: pass

    try:
        for length in range(start_at, ENDING_LENGTH + 1):
            print(f"\n{'='*30}\n SEARCHING LENGTH: {length}\n{'='*30}")
            json_data["lengths"][str(length)] = {}
            
            for belt_count in [2, 3]:
                print(f"\n--- {belt_count}-Belt ---")
                json_data["lengths"][str(length)][str(belt_count)] = {}
                global_blocked = set()
                
                # Heuristic optimization
                start_k = math.ceil(RATIO_TWO_BELT * length) if belt_count == 2 else math.ceil(RATIO_THREE_BELT * length)
                min_k_found = None
                
                for k in range(start_k, length + 1):
                    if min_k_found is not None and k > (min_k_found + 1): break
                    
                    pure_sols, hybrid_sols = [], []
                    
                    # 1. Pure
                    for viz, raw in solve_pure_braids(length, belt_count, k, global_blocked):
                        if VERBOSE_MODE: print(f"    k={k} [P]: {viz}")
                        pure_sols.append(raw)
                        
                    # 2. Hybrid
                    for viz, raw in solve_hybrid_braids(length, belt_count, k, global_blocked):
                        if VERBOSE_MODE: print(f"    k={k} [H]: {viz}")
                        hybrid_sols.append(raw)

                    if pure_sols or hybrid_sols:
                        if min_k_found is None:
                            min_k_found = k
                            print(f"[*] Optimal k found: {k}")
                        
                        json_data["lengths"][str(length)][str(belt_count)][str(k)] = {
                            "occupation_percentage": round((k / length) * 100, 2),
                            "pure": pure_sols, "hybrid": hybrid_sols
                        }

            with open(JSON_OUTPUT_FILE, 'w') as f: json.dump(json_data, f, indent=4)
            print(f"[Checkpoint] Length {length} saved.")

    except KeyboardInterrupt:
        print("\n[!] Interrupted. Saving...")
        with open(JSON_OUTPUT_FILE, 'w') as f: json.dump(json_data, f, indent=4)

if __name__ == "__main__":
    main()