# -*- coding: utf-8 -*-
import json
import math
import sys
import os
from pysat.solvers import Cadical153
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc

# =============================================================================
# USER-DEFINED CONSTANTS & SETTINGS
# =============================================================================
STARTING_LENGTH_DEFAULT = 4
ENDING_LENGTH           = 34  # Increased to ensure search continues
VERBOSE_MODE            = 1  
JSON_OUTPUT_FILE        = "braid_results.json"

# Ratios for optimization (starting k-value thresholds)
RATIO_TWO_BELT   = 0.374
RATIO_THREE_BELT = 0.646

# =============================================================================
# BELT TIER DATA
# =============================================================================
BELT_DATA = {
    1: {"name": "Yellow", "reach": 3, "label": "Y"},
    2: {"name": "Red",    "reach": 4, "label": "R"},
    3: {"name": "Blue",   "reach": 5, "label": "B"},
    4: {"name": "Green",  "reach": 6, "label": "G"}
}

# =============================================================================
# SYMMETRY & ARCHITECTURE HELPERS
# =============================================================================

def get_architecture_symmetries(occupation_mask, belt_length):
    """Generates all cyclic rotations and reflections of a bitmask."""
    symmetries_found = set()
    current_mask = list(occupation_mask)
    for _ in range(belt_length):
        symmetries_found.add(tuple(current_mask))
        symmetries_found.add(tuple(current_mask[::-1]))
        current_mask = [current_mask[-1]] + current_mask[:-1]
    return symmetries_found

# =============================================================================
# SAT SOLVER GENERATORS
# =============================================================================

def solve_pure_braids(belt_length, active_belt_count, surfacing_count, global_blocked_architectures):
    """Generator yielding unique Pure Braid solutions."""
    variable_pool = IDPool()
    pure_formula = CNF()
    allowed_tiers = [2, 3, 4]
    required_tiers = [3, 4] if active_belt_count == 2 else [2, 3, 4]
    tier_labels = {0: ".", 2: "R", 3: "B", 4: "G"}

    tile_state_vars = {}
    for tile_index in range(belt_length):
        tile_state_vars[tile_index] = {color_code: variable_pool.id(f"t{tile_index}_c{color_code}") for color_code in [0] + allowed_tiers}
        pure_formula.extend(CardEnc.equals(lits=list(tile_state_vars[tile_index].values()), bound=1, vpool=variable_pool).clauses)

    empty_tile_literals = [tile_state_vars[tile_index][0] for tile_index in range(belt_length)]
    pure_formula.extend(CardEnc.equals(lits=empty_tile_literals, bound=belt_length - surfacing_count, vpool=variable_pool).clauses)

    for tile_index in range(belt_length):
        for tier_code in allowed_tiers:
            current_literal = tile_state_vars[tile_index][tier_code]
            reach_limit = BELT_DATA[tier_code]["reach"]
            possible_targets = [tile_state_vars[(tile_index + distance) % belt_length][tier_code] for distance in range(1, reach_limit + 1)]
            pure_formula.append([-current_literal] + possible_targets)
            
    for tier_code in required_tiers:
        pure_formula.append([tile_state_vars[tile_index][tier_code] for tile_index in range(belt_length)])

    solver = Cadical153(bootstrap_with=pure_formula.clauses)
    for architecture_mask in global_blocked_architectures:
        solver.add_clause([tile_state_vars[idx][0] for idx, value in enumerate(architecture_mask) if value == 1])

    while solver.solve():
        model_result = set(solver.get_model())
        visual_output, raw_color_pairs, occupation_mask = [], [], []
        for tile_index in range(belt_length):
            chosen_color = next(color for color in [0] + allowed_tiers if tile_state_vars[tile_index][color] in model_result)
            visual_output.append(f"{tier_labels[chosen_color]}{tier_labels[chosen_color]} ")
            raw_color_pairs.append([chosen_color, chosen_color])
            occupation_mask.append(0 if chosen_color == 0 else 1)
        yield "".join(visual_output), raw_color_pairs
        for symmetry in get_architecture_symmetries(occupation_mask, belt_length):
            global_blocked_architectures.add(tuple(symmetry))
            solver.add_clause([tile_state_vars[idx][0] for idx, val in enumerate(symmetry) if val == 1])
    solver.delete()

def solve_hybrid_braids(belt_length, active_belt_count, surfacing_count, global_blocked_architectures):
    """Generator yielding unique Hybrid Braid solutions."""
    variable_pool = IDPool()
    hybrid_formula = CNF()
    color_options = [0, 1, 2, 3, 4]
    tier_labels = {0: ".", 1: "Y", 2: "R", 3: "B", 4: "G"}
    belt_identity_options = list(range(active_belt_count + 1))

    asc_vars = {i: {c: variable_pool.id(f"t{i}_asc_{c}") for c in color_options} for i in range(belt_length)}
    dsc_vars = {i: {c: variable_pool.id(f"t{i}_dsc_{c}") for c in color_options} for i in range(belt_length)}
    bid_vars = {i: {b: variable_pool.id(f"t{i}_id_{b}") for b in belt_identity_options} for i in range(belt_length)}

    for tile_index in range(belt_length):
        hybrid_formula.extend(CardEnc.equals(lits=list(asc_vars[tile_index].values()), bound=1, vpool=variable_pool).clauses)
        hybrid_formula.extend(CardEnc.equals(lits=list(dsc_vars[tile_index].values()), bound=1, vpool=variable_pool).clauses)
        hybrid_formula.extend(CardEnc.equals(lits=list(bid_vars[tile_index].values()), bound=1, vpool=variable_pool).clauses)
        hybrid_formula.append([-asc_vars[tile_index][0], bid_vars[tile_index][0]])
        hybrid_formula.append([-bid_vars[tile_index][0], asc_vars[tile_index][0]])
        hybrid_formula.append([-asc_vars[tile_index][0], dsc_vars[tile_index][0]])
        hybrid_formula.append([-dsc_vars[tile_index][0], asc_vars[tile_index][0]])

    hybrid_formula.extend(CardEnc.equals(lits=[bid_vars[i][0] for i in range(belt_length)], bound=belt_length - surfacing_count, vpool=variable_pool).clauses)

    for belt_id in range(1, active_belt_count + 1):
        hybrid_formula.append([bid_vars[i][belt_id] for i in range(belt_length)])

    for tile_index in range(belt_length):
        for tier_code in [1, 2, 3, 4]:
            reach = BELT_DATA[tier_code]["reach"]
            for offset in range(1, reach + 1):
                target_index = (tile_index + offset) % belt_length
                pair_literal = variable_pool.id(f"pair_{tile_index}_{target_index}_{tier_code}")
                hybrid_formula.append([-pair_literal, dsc_vars[tile_index][tier_code]])
                hybrid_formula.append([-pair_literal, asc_vars[target_index][tier_code]])
                for step in range(1, offset):
                    hybrid_formula.append([-pair_literal, -asc_vars[(tile_index + step) % belt_length][tier_code]])
                for belt_id in range(1, active_belt_count + 1):
                    hybrid_formula.append([-pair_literal, -bid_vars[tile_index][belt_id], bid_vars[target_index][belt_id]])
                    hybrid_formula.append([-pair_literal, -bid_vars[target_index][belt_id], bid_vars[tile_index][belt_id]])
            possible_pairs = [variable_pool.id(f"pair_{tile_index}_{(tile_index + o) % belt_length}_{tier_code}") for o in range(1, reach + 1)]
            hybrid_formula.append([-dsc_vars[tile_index][tier_code]] + possible_pairs)

    solver = Cadical153(bootstrap_with=hybrid_formula.clauses)
    for architecture_mask in global_blocked_architectures:
        solver.add_clause([bid_vars[idx][0] for idx, value in enumerate(architecture_mask) if value == 1])

    while solver.solve():
        model_result = set(solver.get_model())
        visual_output, raw_color_pairs, occupation_mask = [], [], []
        for i in range(belt_length):
            a_color = next(c for c in color_options if asc_vars[i][c] in model_result)
            d_color = next(c for c in color_options if dsc_vars[i][c] in model_result)
            belt_id = next(b_idx for b_idx in belt_identity_options if bid_vars[i][b_idx] in model_result)
            visual_output.append(f"{tier_labels[a_color]}{tier_labels[d_color]} ")
            raw_color_pairs.append([a_color, d_color])
            occupation_mask.append(0 if belt_id == 0 else 1)
        yield "".join(visual_output), raw_color_pairs
        for symmetry in get_architecture_symmetries(occupation_mask, belt_length):
            global_blocked_architectures.add(tuple(symmetry))
            solver.add_clause([bid_vars[idx][0] for idx, val in enumerate(symmetry) if val == 1])
    solver.delete()

# =============================================================================
# MAIN SEARCH LOOP
# =============================================================================

def main():
    json_data = {"metadata": {"min_length": STARTING_LENGTH_DEFAULT, "max_length": ENDING_LENGTH}, "lengths": {}}
    current_start_length = STARTING_LENGTH_DEFAULT

    # IMPROVED RESUME LOGIC: Check if the highest length key actually contains data
    if os.path.exists(JSON_OUTPUT_FILE):
        try:
            with open(JSON_OUTPUT_FILE, 'r') as file_reader:
                loaded_data = json.load(file_reader)
                if "lengths" in loaded_data and loaded_data["lengths"]:
                    json_data = loaded_data
                    keys = [int(k) for k in loaded_data["lengths"].keys()]
                    highest_key = max(keys)
                    
                    # If the highest key is empty, start there. Otherwise, start at highest + 1.
                    if not loaded_data["lengths"][str(highest_key)]:
                        current_start_length = highest_key
                    else:
                        current_start_length = highest_key + 1
                        
                    print(f"[*] Resuming from Length {current_start_length}...")
        except Exception as e: 
            print(f"[!] Resume failed: {e}. Starting fresh.")

    try:
        # Range is inclusive of ENDING_LENGTH
        for current_length in range(current_start_length, ENDING_LENGTH + 1):
            print(f"\n{'='*70}\n SEARCHING LENGTH: {current_length}\n{'='*70}")
            
            # Ensure the key exists for this length
            if str(current_length) not in json_data["lengths"]:
                json_data["lengths"][str(current_length)] = {}
            
            for belt_count in [2, 3]:
                # If this belt count already has data for this length, skip it
                if str(belt_count) in json_data["lengths"][str(current_length)]:
                    continue

                print(f"\n--- {belt_count}-BELT SOLUTIONS ---")
                json_data["lengths"][str(current_length)][str(belt_count)] = {}
                global_blocked_architectures = set()
                
                if belt_count == 2:
                    starting_k = math.ceil(RATIO_TWO_BELT * current_length)
                else: # belt_count == 3
                    starting_k = math.ceil(RATIO_THREE_BELT * current_length)
                
                optimal_k_found = None
                
                for k_surfacing in range(starting_k, current_length + 1):
                    # TWO-K LIMIT: Only find optimal and optimal + 1
                    if optimal_k_found is not None and k_surfacing > (optimal_k_found + 1):
                        break

                    current_pure_results = []
                    current_hybrid_results = []
                    
                    for visual_string, raw_colors in solve_pure_braids(current_length, belt_count, k_surfacing, global_blocked_architectures):
                        if VERBOSE_MODE and not (current_pure_results or current_hybrid_results):
                            print(f"\n    k={k_surfacing} ({(k_surfacing/current_length)*100:.1f}%):")
                        if VERBOSE_MODE: print(f"        [P] {visual_string}")
                        current_pure_results.append(raw_colors)

                    for visual_string, raw_colors in solve_hybrid_braids(current_length, belt_count, k_surfacing, global_blocked_architectures):
                        if VERBOSE_MODE and not (current_pure_results or current_hybrid_results):
                            print(f"\n    k={k_surfacing} ({(k_surfacing/current_length)*100:.1f}%):")
                        if VERBOSE_MODE: print(f"        [H] {visual_string}")
                        current_hybrid_results.append(raw_colors)

                    if current_pure_results or current_hybrid_results:
                        if optimal_k_found is None:
                            optimal_k_found = k_surfacing
                            print(f"[*] Optimal Minimum k found at {k_surfacing}.")

                        json_data["lengths"][str(current_length)][str(belt_count)][str(k_surfacing)] = {
                            "occupation_percentage": round((k_surfacing / current_length) * 100, 2),
                            "pure": current_pure_results,
                            "hybrid": current_hybrid_results
                        }

            # Immediate save after each length
            with open(JSON_OUTPUT_FILE, 'w') as file_writer:
                json.dump(json_data, file_writer, indent=4)
            print(f"\n[Checkpoint] Length {current_length} saved.")

    except KeyboardInterrupt:
        print("\n\n[!] Interrupted. Final save...")
        with open(JSON_OUTPUT_FILE, 'w') as file_writer: json.dump(json_data, file_writer, indent=4)

    # RE-IMPLEMENTED TOP 10 REPORT
    print(f"\n{'#'*70}\n FINAL EFFICIENCY REPORT\n{'#'*70}")
    tier_labels = {0: ".", 1: "Y", 2: "R", 3: "B", 4: "G"}
    for b_count in [2, 3]:
        leaderboard = []
        for l_key, belts in json_data["lengths"].items():
            if str(b_count) in belts:
                for k_key, data in belts[str(b_count)].items():
                    pct = data["occupation_percentage"]
                    # Extract visual for the first solution
                    first_sol = data["pure"][0] if data["pure"] else (data["hybrid"][0] if data["hybrid"] else None)
                    if first_sol:
                        sol_type = "[P]" if data["pure"] else "[H]"
                        viz = "".join([f"{tier_labels[p[0]]}{tier_labels[p[1]]} " for p in first_sol])
                        leaderboard.append((pct, l_key, k_key, sol_type, viz))
        
        print(f"\n--- Best Occupation Patterns ({b_count}-Belt) ---")
        leaderboard.sort(key=lambda x: x[0])
        for i, (pct, l, k, t, viz) in enumerate(leaderboard[:10]):
            print(f"{i+1:2}. {pct:5.1f}% | L={l:<2} k={k:<2} | {t} {viz}")

if __name__ == "__main__":
    main()