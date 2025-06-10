#include <iostream>
#include <vector>
#include <string>
#include <set>
#include <map>
#include <deque>
#include <algorithm>
#include <random>
#include <chrono>
#include <thread>
#include <functional>
#include <optional>
#include <tuple>
#include <utility>
#include <stdexcept>
#include <sstream>
#include <unordered_map> // For std::unordered_map
#include <memory>


// --- Type Aliases and Helper Structs ---
struct Coord {
    int r, c;

    bool operator<(const Coord& other) const {
        if (r != other.r) return r < other.r;
        return c < other.c;
    }
    bool operator==(const Coord& other) const {
        return r == other.r && c == other.c;
    }
     // For std::unordered_set<Coord> if needed
    struct HashFunction {
        size_t operator()(const Coord& coord) const {
            size_t rHash = std::hash<int>()(coord.r);
            size_t cHash = std::hash<int>()(coord.c);
            return rHash ^ (cHash << 1);
        }
    };
};

struct Move {
    int k, r, c;
    Move(int k_ = 0, int r_ = 0, int c_ = 0) : k(k_), r(r_), c(c_) {}

    bool operator<(const Move& other) const {
        if (k != other.k) return k < other.k;
        if (r != other.r) return r < other.r;
        return c < other.c;
    }
     bool operator==(const Move& other) const {
        return k == other.k && r == other.r && c == other.c;
    }
};

using Grid = std::vector<std::vector<int>>;
using Path = std::vector<Move>;

// --- Custom Hash and Equal for Grid (for std::unordered_map) ---
struct GridHash {
    std::size_t operator()(const Grid& grid) const {
        std::size_t seed = grid.size();
        for (const auto& row : grid) {
            for (int i : row) {
                seed ^= std::hash<int>()(i) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            }
        }
        return seed;
    }
};

struct GridEqual {
    bool operator()(const Grid& a, const Grid& b) const {
        if (a.size() != b.size()) return false;
        for (size_t i = 0; i < a.size(); ++i) {
            if (a[i].size() != b[i].size()) return false; // Should not happen for square grids
            for (size_t j = 0; j < a[i].size(); ++j) {
                if (a[i][j] != b[i][j]) return false;
            }
        }
        return true;
        // A more concise way if vectors are guaranteed to be well-formed:
        // return a == b; // std::vector already has operator==
    }
};


// --- Color Constants (Unix-like systems) ---
const std::string COLOR_RED = "\033[91m";
const std::string COLOR_RESET = "\033[0m";

// --- Forward Declarations for Utility Functions ---
Grid rotate_subgrid(const Grid& grid, int top_left_row, int top_left_col, int k);
void display_grid(const Grid& grid, const std::string& title = "Grid");
std::set<Coord> get_unsolved_pairs_coords(const Grid& grid);


// --- (Existing includes and structs like Coord, Move, Grid, GridHash, GridEqual) ---

class PairFormationSolver {
public:
    static int MAX_BFS_STEPS;

    PairFormationSolver() = default;

private:
    // Helper structs for using std::shared_ptr<const Grid> as unordered_map key
    struct PtrGridHash {
        std::size_t operator()(const std::shared_ptr<const Grid>& grid_ptr) const {
            // It's assumed grid_ptr will not be null in the context of this BFS's visited set
            return GridHash()(*grid_ptr);
        }
    };

    struct PtrGridEqual {
        bool operator()(const std::shared_ptr<const Grid>& a_ptr, const std::shared_ptr<const Grid>& b_ptr) const {
            // It's assumed a_ptr and b_ptr will not be null
            return GridEqual()(*a_ptr, *b_ptr);
        }
    };

    // Type alias for the visited data map
    using VisitedMapType = std::unordered_map<
        std::shared_ptr<const Grid>,
        std::pair<std::optional<std::shared_ptr<const Grid>>, std::optional<Move>>,
        PtrGridHash,
        PtrGridEqual
    >;

    std::optional<Path> _reconstruct_path(
        const VisitedMapType& visited_data,
        std::shared_ptr<const Grid> final_state_ptr, // Changed to shared_ptr
        std::shared_ptr<const Grid> initial_state_ptr) { // Changed to shared_ptr
        
        Path path;
        std::shared_ptr<const Grid> curr_state_ptr = final_state_ptr;
        
        // Compare the Grid objects pointed to, not the pointers themselves
        while (!(PtrGridEqual()(curr_state_ptr, initial_state_ptr))) { 
            auto it = visited_data.find(curr_state_ptr);
            if (it == visited_data.end()) {
                 // This should ideally not happen if logic is correct and final_state_ptr is in visited_data
                return std::nullopt;
            }

            const auto& parent_data = it->second;
            const std::optional<std::shared_ptr<const Grid>>& parent_state_opt_ptr = parent_data.first;
            const std::optional<Move>& move_opt = parent_data.second;

            // If curr_state_ptr is not initial_state_ptr, it must have a parent in BFS path
            if (!parent_state_opt_ptr.has_value() || !move_opt.has_value()) {
                // This indicates an issue, perhaps initial_state_ptr was not properly marked
                // or an unexpected state was encountered.
                // Given the loop condition, parent_state_opt_ptr should always have a value here.
                return std::nullopt; // Error or unexpected break in path
            }

            path.push_back(move_opt.value());
            curr_state_ptr = parent_state_opt_ptr.value(); 
        }
        std::reverse(path.begin(), path.end());
        return path;
    }

public:
    std::optional<Path> find_shortest_pairing_path(
        const Grid& board, int r1_target, int c1_target, int r2_target, int c2_target,
        const std::vector<Coord>& forbidden_coords_vec,
        std::function<Grid(const Grid&, int, int, int)> rotate_func) {
        
        int n_dim = board.size();
        if (std::abs(r1_target - r2_target) + std::abs(c1_target - c2_target) != 1) {
            // This check implies target cells must be adjacent. If they are already a pair, value must match.
             // The problem asks to form a pair, implying values might not match initially.
            // This initial check is fine for adjacency.
        }
        // If already a pair, return empty path.
        if (board[r1_target][c1_target] == board[r2_target][c2_target]) {
            return Path{}; // Empty path, already solved
        }

        std::set<Coord> forbidden_coords_set(forbidden_coords_vec.begin(), forbidden_coords_vec.end());
        std::vector<Move> possible_rotations;
        // ... (possible_rotations generation logic remains the same) ...
        for (int k_rot = 2; k_rot <= n_dim; ++k_rot) {
            for (int tr_rot = 0; tr_rot <= n_dim - k_rot; ++tr_rot) {
                for (int tc_rot = 0; tc_rot <= n_dim - k_rot; ++tc_rot) {
                    bool is_safe_rotation = true;
                    for (int r_offset = 0; r_offset < k_rot; ++r_offset) {
                        for (int c_offset = 0; c_offset < k_rot; ++c_offset) {
                            if (forbidden_coords_set.count({tr_rot + r_offset, tc_rot + c_offset})) {
                                is_safe_rotation = false;
                                break;
                            }
                        }
                        if (!is_safe_rotation) break;
                    }
                    if (is_safe_rotation) {
                        possible_rotations.emplace_back(k_rot, tr_rot, tc_rot);
                    }
                }
            }
        }
        // If no possible moves (e.g., all cells forbidden, or n<2 so k_rot loop doesn't run)
        // This check was: if (possible_rotations.empty() && n_dim > 0)
        // If n_dim < 2, k_rot loop won't run, possible_rotations is empty.
        // if (possible_rotations.empty() && n_dim >=2 ) might be more precise if we want to return nullopt
        // only when moves are expected but none are available.
        // For n_dim < 2, the problem constraints (n>=4) mean this isn't an issue here.
        // But if n_dim is small and all cells are forbidden, it's valid.
        if (possible_rotations.empty() && n_dim >=2 ) { // Check for n_dim >=2 explicitly
             return std::nullopt;
        }


        // Use shared_ptr for states
        auto initial_state_ptr = std::make_shared<const Grid>(board);
        
        std::deque<std::shared_ptr<const Grid>> queue;
        queue.push_back(initial_state_ptr); 

        VisitedMapType visited_data; // Uses PtrGridHash and PtrGridEqual
        visited_data.emplace(initial_state_ptr, std::make_pair(std::nullopt, std::nullopt));

        int bfs_steps_count = 0;

        while (!queue.empty()) {
            bfs_steps_count++;
            if (bfs_steps_count > MAX_BFS_STEPS) {
                return std::nullopt; // Search limit exceeded
            }

            std::shared_ptr<const Grid> current_state_ptr = queue.front(); 
            queue.pop_front();

            for (const auto& move_op : possible_rotations) { 
                // rotate_func returns a new Grid value.
                // *current_state_ptr dereferences to 'const Grid&'
                Grid next_grid_value = rotate_func(*current_state_ptr, move_op.r, move_op.c, move_op.k); 
                // Wrap the new Grid value in a shared_ptr. std::move helps if Grid has move semantics.
                auto next_grid_ptr = std::make_shared<const Grid>(std::move(next_grid_value));
                
                if (visited_data.find(next_grid_ptr) == visited_data.end()) {
                    // Store current_state_ptr (parent) and move_op
                    visited_data.emplace(next_grid_ptr, 
                                         std::make_pair(std::make_optional(current_state_ptr), std::make_optional(move_op)));
                    
                    // Access grid elements via dereferencing the pointer
                    if ((*next_grid_ptr)[r1_target][c1_target] == (*next_grid_ptr)[r2_target][c2_target]) {
                        return _reconstruct_path(visited_data, next_grid_ptr, initial_state_ptr);
                    }
                    queue.push_back(next_grid_ptr); 
                }
            }
        }
        return std::nullopt; // Target pair not formed within MAX_BFS_STEPS
    }
};
// int PairFormationSolver::MAX_BFS_STEPS = 25000; // Ensure this is defined (as it is in original code)
int PairFormationSolver::MAX_BFS_STEPS = 25000;


class HeuristicSolver {
public:
    Grid current_grid;
    int n;
    std::function<Grid(const Grid&, int, int, int)> rotate_subgrid_func; 
    Path total_operations;
    std::set<Coord> protected_coords;
    PairFormationSolver pair_solver;
    int operation_count_for_display;
    std::function<void(const Grid&, const std::string&)> display_func;
    int step_delay_ms;

    HeuristicSolver(const Grid& initial_grid,
                    std::function<Grid(const Grid&, int, int, int)> rot_func, 
                    std::function<void(const Grid&, const std::string&)> disp_func = nullptr,
                    double step_delay_sec = 0.0)
        : current_grid(initial_grid), 
          n(initial_grid.size()),
          rotate_subgrid_func(rot_func),
          operation_count_for_display(0),
          display_func(disp_func),
          step_delay_ms(static_cast<int>(step_delay_sec * 1000.0)) {}

    void _apply_operation_to_current_grid(const Move& op) {
        current_grid = rotate_subgrid_func(current_grid, op.r, op.c, op.k); 
        total_operations.push_back(op);
        operation_count_for_display++;
        if (display_func) {
            std::string op_str = "Op #" + std::to_string(operation_count_for_display) +
                                 ": Rotate k=" + std::to_string(op.k) +
                                 " at (" + std::to_string(op.r) + "," + std::to_string(op.c) + ")";
            display_func(current_grid, op_str);
        }
        if (step_delay_ms > 0) {
            std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
        }
    }
    
    void _apply_operations_to_grid(const Path& operations) { 
        if (operations.empty()) return;
        for (const auto& op : operations) {
            current_grid = rotate_subgrid_func(current_grid, op.r, op.c, op.k);
            total_operations.push_back(op); 
            operation_count_for_display++;
            if (display_func) {
                std::string op_str = "Op #" + std::to_string(operation_count_for_display) +
                                     ": Rotate k=" + std::to_string(op.k) +
                                     " at (" + std::to_string(op.r) + "," + std::to_string(op.c) + ")";
                display_func(current_grid, op_str);
            }
            if (step_delay_ms > 0) {
                std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
            }
        }
    }


    std::set<Coord> _transform_coords(const std::set<Coord>& coords_set, int n_dim, int angle_degrees) const {
        std::set<Coord> new_coords;
        for (const auto& coord : coords_set) {
            int r = coord.r;
            int c = coord.c;
            if (angle_degrees == 90) new_coords.insert({c, n_dim - 1 - r});
            else if (angle_degrees == 180) new_coords.insert({n_dim - 1 - r, n_dim - 1 - c});
            else if (angle_degrees == 270) new_coords.insert({n_dim - 1 - c, r});
            else new_coords.insert({r, c}); 
        }
        return new_coords;
    }

    void _rotate_entire_board_and_protected_coords(int angle_degrees) {
        if (angle_degrees == 0) return;
        int num_rotations = angle_degrees / 90;
        num_rotations %= 4; 
        if (num_rotations == 0 && angle_degrees != 0) num_rotations = 4; 

        for (int i = 0; i < num_rotations; ++i) {
            current_grid = rotate_subgrid_func(current_grid, 0, 0, n);
            total_operations.emplace_back(n, 0, 0); 
            operation_count_for_display++;
             if (display_func) {
                std::string op_str = "Op #" + std::to_string(operation_count_for_display) +
                                     ": Rotate k=" + std::to_string(n) +
                                     " at (0,0) (Entire Board Rotation Step)";
                display_func(current_grid, op_str);
            }
            if (step_delay_ms > 0 && i < num_rotations -1 ) { 
                 std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
            }
            protected_coords = _transform_coords(protected_coords, n, 90); 
        }
         if (step_delay_ms > 0 && num_rotations > 0 ) { 
            std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
        }
    }

    void _align_row_pairs_sequentially(
        int row_idx_sub, int first_pair_col_start_sub, int pair_col_increment, int layer_offset) {
        
        int current_sub_n = n - 2 * layer_offset;
        if (current_sub_n < 2) return; 

        int abs_row_offset = layer_offset;
        int abs_col_offset = layer_offset;

        // `pair_col_increment` は通常1なので、ループの終端条件は c_sub_pair_left <= current_sub_n - 2 となる
        // c_sub_pair_left はペアの左側の列インデックス
        // c_sub_pair_left + pair_col_increment はペアの右側の列インデックス
        for (int c_sub_pair_left = first_pair_col_start_sub; 
             // ループ条件は、ペアの右側のセル (c_sub_pair_left + pair_col_increment) が
             // サブグリッドの最後の列 (current_sub_n - 1) より手前か同じである間、
             // かつ、c_sub_pair_left から2つずつ進むことを考慮
             c_sub_pair_left < current_sub_n - pair_col_increment; // 修正: Pythonのrange(start, end, step)のendはexclusive
                                                                 // C++の <= current_sub_n - 1 - pair_col_increment とほぼ同等
             c_sub_pair_left += 2) {
            
            int r1_target_sub_orig = row_idx_sub;
            int c1_target_sub_orig = c_sub_pair_left;
            int r2_target_sub_orig = row_idx_sub; 
            int c2_target_sub_orig = c_sub_pair_left + pair_col_increment;

            // サブグリッドの範囲外に出るペアはスキップ (c2が右端の列インデックス)
            if (c2_target_sub_orig >= current_sub_n) {
                continue;
            }

            int r1_target_abs_orig = r1_target_sub_orig + abs_row_offset;
            int c1_target_abs_orig = c1_target_sub_orig + abs_col_offset;
            int r2_target_abs_orig = r2_target_sub_orig + abs_row_offset; 
            int c2_target_abs_orig = c2_target_sub_orig + abs_col_offset;


            bool target1_orig_protected = protected_coords.count({r1_target_abs_orig, c1_target_abs_orig});
            bool target2_orig_protected = protected_coords.count({r2_target_abs_orig, c2_target_abs_orig});

            if (target1_orig_protected && target2_orig_protected) {
                continue;
            }
            
            // --- Special Handling for rightmost pair in top row of subgrid (if subgrid > 4x4) ---
            // `row_idx_sub` は、この関数が呼び出される際に常に0 (上1行目を対象とするため)。
            // `c2_target_sub_orig` がサブグリッドの最後の列インデックス (`current_sub_n - 1`) であるかを確認。
            bool is_top_row_rightmost_pair = (r1_target_sub_orig == 0 && c2_target_sub_orig == current_sub_n - 1);
            
            // ヘルパー戦略は、サブグリッドのサイズが4x4より大きい場合にのみ適用
            bool apply_helper_strategy = is_top_row_rightmost_pair && (current_sub_n > 4);

            if (apply_helper_strategy) {
                int r1_target_sub_helper = r1_target_sub_orig + 1; // Helper row is one below

                // Ensure helper row is within subgrid bounds (always true if current_sub_n > 1)
                if (r1_target_sub_helper < current_sub_n) {
                    int r1_target_abs_helper = r1_target_sub_helper + abs_row_offset;
                    int c1_target_abs_helper = c1_target_sub_orig + abs_col_offset; 
                    int r2_target_abs_helper = r1_target_sub_helper + abs_row_offset; 
                    int c2_target_abs_helper = c2_target_sub_orig + abs_col_offset; 
                    
                    bool helper_target1_protected = protected_coords.count({r1_target_abs_helper, c1_target_abs_helper});
                    bool helper_target2_protected = protected_coords.count({r2_target_abs_helper, c2_target_abs_helper});

                    // Only attempt to form helper pair if it's not already formed and protected
                    if (!(helper_target1_protected && helper_target2_protected)) {
                        if (current_grid[r1_target_abs_helper][c1_target_abs_helper] != current_grid[r2_target_abs_helper][c2_target_abs_helper]) {
                            if (display_func) {
                                std::string title = "Special (subgrid > 4x4): Forming helper pair (" + 
                                                    std::to_string(r1_target_abs_helper) + "," + std::to_string(c1_target_abs_helper) + ")-(" +
                                                    std::to_string(r2_target_abs_helper) + "," + std::to_string(c2_target_abs_helper) + ")";
                                display_func(current_grid, title);
                                if (step_delay_ms > 0) std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
                            }
                            std::vector<Coord> protected_coords_vec_for_helper(protected_coords.begin(), protected_coords.end());
                            
                            std::optional<Path> path_opt_helper = pair_solver.find_shortest_pairing_path(
                                current_grid, r1_target_abs_helper, c1_target_abs_helper, r2_target_abs_helper, c2_target_abs_helper,
                                protected_coords_vec_for_helper, this->rotate_subgrid_func );
                            if (path_opt_helper.has_value() && !path_opt_helper.value().empty()) {
                                _apply_operations_to_grid(path_opt_helper.value());
                            }
                        }
                        // Helper pair is NOT protected
                    }
                }
            }
            // --- End of Special Handling ---

            // --- Proceed with the original target pair ---
            if (current_grid[r1_target_abs_orig][c1_target_abs_orig] == current_grid[r2_target_abs_orig][c2_target_abs_orig]) {
                protected_coords.insert({r1_target_abs_orig, c1_target_abs_orig});
                protected_coords.insert({r2_target_abs_orig, c2_target_abs_orig});
                if (display_func) { 
                    std::string title = "Protected (pre-formed/lucky) pair (" + std::to_string(r1_target_abs_orig) + "," +
                                        std::to_string(c1_target_abs_orig) + ")-(" + std::to_string(r2_target_abs_orig) + "," +
                                        std::to_string(c2_target_abs_orig) + ")";
                    display_func(current_grid, title);
                     if (step_delay_ms > 0) std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
                }
                continue;
            }
            
            if (display_func ) {
                 std::string title = "Attempting main target pair (" + 
                                    std::to_string(r1_target_abs_orig) + "," + std::to_string(c1_target_abs_orig) + ")-(" +
                                    std::to_string(r2_target_abs_orig) + "," + std::to_string(c2_target_abs_orig) + ")";
                display_func(current_grid, title);
                if (step_delay_ms > 0) std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
            }

            std::vector<Coord> protected_coords_vec_for_orig(protected_coords.begin(), protected_coords.end());
            std::optional<Path> path_opt_orig = pair_solver.find_shortest_pairing_path(
                current_grid, r1_target_abs_orig, c1_target_abs_orig, r2_target_abs_orig, c2_target_abs_orig,
                protected_coords_vec_for_orig, this->rotate_subgrid_func );

            if (path_opt_orig.has_value()) { 
                const Path& actual_path_from_bfs = path_opt_orig.value();
                if (!actual_path_from_bfs.empty()) {
                    _apply_operations_to_grid(actual_path_from_bfs); 
                }
            }
            
            if (current_grid[r1_target_abs_orig][c1_target_abs_orig] == current_grid[r2_target_abs_orig][c2_target_abs_orig]) {
                protected_coords.insert({r1_target_abs_orig, c1_target_abs_orig});
                protected_coords.insert({r2_target_abs_orig, c2_target_abs_orig});
                if (display_func) { 
                     std::string title = "Protected main target pair (" + std::to_string(r1_target_abs_orig) + "," +
                                        std::to_string(c1_target_abs_orig) + ")-(" + std::to_string(r2_target_abs_orig) + "," +
                                        std::to_string(c2_target_abs_orig) + ")";
                    display_func(current_grid, title);
                    if (step_delay_ms > 0) std::this_thread::sleep_for(std::chrono::milliseconds(step_delay_ms));
                }
            }
        } 
    }


    void solve_layer(int layer_offset) {
        int current_sub_n = n - 2 * layer_offset;
        if (current_sub_n < 2) return;
        // The heuristic is primarily designed for layers larger than 2x2.
        // The 4x4 special case handles the central 4x4, or the whole board if n=4.
        // The original Python code for `solve_layer` had:
        // if self.n - 2 * layer_offset < 4 and layer_offset > 0: return
        // This means if the subgrid is smaller than 4x4 AND it's not the outermost layer, skip.
        // For a 4x4 board (layer_offset=0, current_sub_n=4), solve_layer would run.
        // For a 6x6 board:
        //   layer_offset=0, current_sub_n=6 -> runs
        //   layer_offset=1, current_sub_n=4 -> (inner 4x4)
        //     The Python condition `current_sub_n < 4 and layer_offset > 0` would be `4 < 4 (false) and 1 > 0 (true)` -> false. So it runs.
        //     The heuristic seems to expect `solve_layer` to run on the 4x4 subgrid as well, before the final 4x4 specific logic.
        // Let's ensure the current logic matches the original intent for when `solve_layer` executes.
        // The original `solve_layer` logic in Python seems to apply its 7 steps even to a 4x4 subgrid
        // (when it's an inner subgrid of a larger board).
        // The `if current_sub_n < 4 and layer_offset > 0: return` in Python
        // means that if we are dealing with an *inner* subgrid that is 2x2, we skip `solve_layer`.
        // A 2x2 subgrid occurs when n=4, layer_offset=1. current_sub_n = 4 - 2*1 = 2.
        // So, if current_sub_n = 2 and layer_offset > 0, skip.
        // This is equivalent to: if current_sub_n == 2 (because it can't be <2 and >0), skip for inner layers.
        
        // If the subgrid is 2x2 (i.e., current_sub_n == 2), this layer processing is too complex
        // and should typically be handled by a final BFS or a simpler specific strategy if needed.
        // The Python `solve_outer_layer_sequentially` which calls `_align_row_pairs_sequentially`
        // implies it operates on subgrids. The final 4x4 handling in Python is separate.
        // The condition `if current_sub_n < 4 and layer_offset > 0` prevents `solve_layer` for inner 2x2s.
        // For a 4x4 board, layer_offset=0, current_sub_n=4. The `solve_layer` runs.
        // The special 4x4 logic in `solve()` method then runs after all `solve_layer` calls.
        // This seems correct. The `_align_row_pairs_sequentially` function itself should handle
        // subgrids of size 2x2 or 3x3 gracefully (e.g. fewer pairs to form).

        // The condition `current_sub_n < 4 && layer_offset > 0` from previous C++ meant:
        // If N=4, layer_offset=0, current_sub_n=4. Condition is false. Runs.
        // If N=6, layer_offset=0, current_sub_n=6. Condition is false. Runs.
        // If N=6, layer_offset=1, current_sub_n=4. Condition is false. Runs.
        // If N=8, layer_offset=0, current_sub_n=8. Runs.
        // If N=8, layer_offset=1, current_sub_n=6. Runs.
        // If N=8, layer_offset=2, current_sub_n=4. Runs.
        // This logic seems fine for when `solve_layer` is called.
        // The helper strategy condition `current_sub_n > 4` is inside `_align_row_pairs_sequentially`.

        if (current_sub_n < 4 && layer_offset > 0) { // Skip for inner 2x2 subgrids.
             return;
        }

        // These calls to _align_row_pairs_sequentially target row 0 of the current subgrid.
        _align_row_pairs_sequentially(0, 0, 1, layer_offset); 
        _rotate_entire_board_and_protected_coords(180);      
        _align_row_pairs_sequentially(0, 0, 1, layer_offset); 
        _rotate_entire_board_and_protected_coords(90);       
        _align_row_pairs_sequentially(0, 1, 1, layer_offset); 
        _rotate_entire_board_and_protected_coords(180);      
        _align_row_pairs_sequentially(0, 1, 1, layer_offset); 
    }

    Path solve() {
        int num_layers_to_process_heuristically = (n >= 4) ? (n - 2) / 2 : 0;
        
        for (int layer = 0; layer < num_layers_to_process_heuristically; ++layer) {
            solve_layer(layer);
        }

        if (n >= 4) { 
            // 全探索で事前検証済み、変更を禁ずる
            int offset_4x4 = (n - 4) / 2; 
            int tl_r_abs_4x4 = offset_4x4;
            int tl_c_abs_4x4 = offset_4x4;
            
            int val_00_in_4x4 = current_grid[tl_r_abs_4x4 + 0][tl_c_abs_4x4 + 0];
            int val_01_in_4x4 = current_grid[tl_r_abs_4x4 + 0][tl_c_abs_4x4 + 1];
            int val_11_in_4x4 = current_grid[tl_r_abs_4x4 + 1][tl_c_abs_4x4 + 1];
            int val_22_in_4x4 = current_grid[tl_r_abs_4x4 + 2][tl_c_abs_4x4 + 2];


            Path ops_for_4x4_relative;
            if (val_11_in_4x4 == val_22_in_4x4) { 
                if (val_00_in_4x4 == val_01_in_4x4) {
                    ops_for_4x4_relative = {{2, 0, 0}, {2, 0, 1}, {2, 1, 0}, {2, 1, 2}};
                } else {
                    ops_for_4x4_relative = {{2, 0, 2}, {2, 1, 1}, {2, 0, 1}, {2, 0, 2}};
                }
                
                if (!ops_for_4x4_relative.empty()) {
                    Path ops_for_4x4_absolute;
                    for (const auto& rel_op : ops_for_4x4_relative) {
                        ops_for_4x4_absolute.emplace_back(rel_op.k, 
                                                          tl_r_abs_4x4 + rel_op.r, 
                                                          tl_c_abs_4x4 + rel_op.c);
                    }
                    _apply_operations_to_grid(ops_for_4x4_absolute); 
                    
                    for (int r_off = 0; r_off < 4; ++r_off) {
                        for (int c_off = 0; c_off < 4; ++c_off) {
                            protected_coords.insert({tl_r_abs_4x4 + r_off, tl_c_abs_4x4 + c_off});
                        }
                    }
                }
            }
        } else if (n == 2) {
            if (current_grid[0][0] != current_grid[0][1] && current_grid[0][0] != current_grid[1][0]) {
                std::optional<Path> path_opt = pair_solver.find_shortest_pairing_path(
                    current_grid, 0, 0, 0, 1, {}, this->rotate_subgrid_func
                );
                if (path_opt.has_value() && !path_opt.value().empty()) {
                    _apply_operations_to_grid(path_opt.value());
                }
                if (current_grid[0][0] != current_grid[0][1] && current_grid[0][0] != current_grid[1][0]) {
                     path_opt = pair_solver.find_shortest_pairing_path(
                        current_grid, 0, 0, 1, 0, {}, this->rotate_subgrid_func
                    );
                    if (path_opt.has_value() && !path_opt.value().empty()) {
                         _apply_operations_to_grid(path_opt.value());
                    }
                }
            }
        }
        return total_operations;
    }
};


// --- Utility Functions Implementation ---
Grid generate_initial_grid(int n_val, int seed = -1) { 
    if (n_val < 2 || n_val > 24 || n_val % 2 != 0) {
        throw std::invalid_argument("n_val must be an even integer between 2 and 24.");
    }
    int total_cells = n_val * n_val;
    int num_unique_values = total_cells / 2;
    std::vector<int> values;
    values.reserve(total_cells);
    for (int i = 0; i < num_unique_values; ++i) {
        values.push_back(i);
        values.push_back(i);
    }

    std::mt19937 rng;
    if (seed == -1) {
         rng.seed(std::chrono::high_resolution_clock::now().time_since_epoch().count());
    } else {
        rng.seed(static_cast<unsigned int>(seed));
    }
    std::shuffle(values.begin(), values.end(), rng);

    Grid grid(n_val, std::vector<int>(n_val));
    for (int r = 0; r < n_val; ++r) {
        for (int c = 0; c < n_val; ++c) {
            grid[r][c] = values[static_cast<size_t>(r) * n_val + c];
        }
    }
    return grid;
}

Grid rotate_subgrid(const Grid& grid, int top_left_row, int top_left_col, int k) {
    Grid new_grid = grid; 
    Grid subgrid_original(k, std::vector<int>(k));
    for (int r_s = 0; r_s < k; ++r_s) {
        for (int c_s = 0; c_s < k; ++c_s) {
            subgrid_original[r_s][c_s] = grid[top_left_row + r_s][top_left_col + c_s];
        }
    }
    for (int r_s = 0; r_s < k; ++r_s) {
        for (int c_s = 0; c_s < k; ++c_s) {
            new_grid[top_left_row + r_s][top_left_col + c_s] = subgrid_original[k - 1 - c_s][r_s];
        }
    }
    return new_grid;
}

std::map<int, std::vector<Coord>> _find_all_value_locations(const Grid& grid) {
    std::map<int, std::vector<Coord>> locations;
    if (grid.empty()) return locations;
    for (size_t r_idx = 0; r_idx < grid.size(); ++r_idx) {
        for (size_t c_idx = 0; c_idx < grid[r_idx].size(); ++c_idx) {
            locations[grid[r_idx][c_idx]].push_back({static_cast<int>(r_idx), static_cast<int>(c_idx)});
        }
    }
    return locations;
}

std::set<Coord> get_unsolved_pairs_coords(const Grid& grid) {
    auto value_locations = _find_all_value_locations(grid);
    std::set<Coord> unsolved_coords;
    for (const auto& pair_val_locs : value_locations) {
        const auto& locs = pair_val_locs.second;
        if (locs.size() == 2) {
            const Coord& c1 = locs[0];
            const Coord& c2 = locs[1];
            if (std::abs(c1.r - c2.r) + std::abs(c1.c - c2.c) != 1) {
                unsolved_coords.insert(c1);
                unsolved_coords.insert(c2);
            }
        } else if (locs.size() != 2 && !locs.empty()) { 
            for(const auto& loc : locs) unsolved_coords.insert(loc);
        }
    }
    return unsolved_coords;
}
    
void display_grid(const Grid& grid, const std::string& title) {
#ifndef _WIN32
    // Clear screen for operations or specific messages if they start with "Op #", "Protected", "Special:", "Attempting"
    // This helps in visualizing step-by-step progress.
    bool should_clear = (title.rfind("Op #", 0) == 0); 
    // Add more conditions if other titles should also clear the screen.
    // if (title.rfind("Protected", 0) == 0 || title.rfind("Special:",0)==0 || title.rfind("Attempting",0)==0) {
    //     should_clear = true;
    // }

    if (should_clear) {
        std::cout << "\033[H\033[J" << std::flush;
    }
#endif
    std::cout << "\n--- " << title << " ---" << std::endl;
    if (grid.empty()) {
        std::cout << "Empty grid" << std::endl;
        return;
    }
    int n_val = grid.size(); 
    
    std::set<Coord> unsolved = get_unsolved_pairs_coords(grid);
    int max_val = 0;
    if (n_val > 0 && !grid[0].empty()) {
        for (const auto& r_data : grid) {
            for (int cell_val : r_data) {
                if (cell_val > max_val) max_val = cell_val;
            }
        }
    }
    int cell_width = (max_val > 0) ? static_cast<int>(std::to_string(max_val).length()) : 1;

    std::string header_footer(static_cast<size_t>(n_val) * (cell_width + 1) + 3, '-');
    std::cout << header_footer << std::endl;

    for (int r_idx = 0; r_idx < n_val; ++r_idx) {
        std::cout << "| ";
        for (int c_idx = 0; c_idx < grid[r_idx].size(); ++c_idx) {
            int value = grid[r_idx][c_idx];
            
            std::stringstream temp_ss;
            temp_ss.width(cell_width);
            temp_ss << value;
            std::string cell_str_formatted = temp_ss.str();

            if (unsolved.count({r_idx, c_idx})) {
#ifndef _WIN32
                std::cout << COLOR_RED << cell_str_formatted << COLOR_RESET << " ";
#else
                std::cout << "*" << cell_str_formatted << "* "; 
#endif
            } else {
                std::cout << cell_str_formatted << " ";
            }
        }
        std::cout << "|" << std::endl;
    }
    std::cout << header_footer << std::endl;
    int num_unsolved_pairs = unsolved.size() / 2;
    std::cout << "Unsolved pairs: " << num_unsolved_pairs << std::endl;
    if (num_unsolved_pairs == 0 && n_val > 0) {
        std::cout << "🎉 All pairs are solved!" << std::endl;
    }
    std::cout << std::endl;
}

bool is_solved(const Grid& grid) {
    if (grid.empty() || grid[0].empty()) return true;
    return get_unsolved_pairs_coords(grid).empty();
}


int main() {
#ifndef _WIN32
    std::cout << "\033[H\033[J" << std::flush;
#endif
    std::cout << "Starting Heuristic Solver Test (C++ Version with unordered_map)." << std::endl;

    int grid_size = 4; // Default grid size
    std::cout << "Enter grid size (even, 2-24, default 4): ";
    std::string grid_size_input_str; 
    std::getline(std::cin, grid_size_input_str);
    if (!grid_size_input_str.empty()) {
        try {
            int input_val = std::stoi(grid_size_input_str);
            if (input_val >= 2 && input_val <= 24 && input_val % 2 == 0) {
                grid_size = input_val;
            } else {
                std::cout << "Invalid size. Using default " << grid_size << "." << std::endl;
            }
        } catch (const std::invalid_argument& ) { 
            std::cout << "Invalid input. Using default " << grid_size << "." << std::endl;
        } catch (const std::out_of_range& ) { 
            std::cout << "Input out of range. Using default " << grid_size << "." << std::endl;
        }
    }
    
    double STEP_DELAY_SECONDS = 1.0; // Default no delay
    std::cout << "Enter step delay in seconds (e.g., 0.5, default 0.0 for no step-by-step display): ";
    std::string delay_input_str;
    std::getline(std::cin, delay_input_str);
    if (!delay_input_str.empty()) {
        try {
            double input_delay = std::stod(delay_input_str);
            if (input_delay >= 0) {
                STEP_DELAY_SECONDS = input_delay;
            } else {
                 std::cout << "Invalid delay. Using default " << STEP_DELAY_SECONDS << "s." << std::endl;
            }
        } catch (const std::invalid_argument& ) {
            std::cout << "Invalid input for delay. Using default " << STEP_DELAY_SECONDS << "s." << std::endl;
        } catch (const std::out_of_range& ) {
            std::cout << "Delay input out of range. Using default " << STEP_DELAY_SECONDS << "s." << std::endl;
        }
    }


    Grid initial_board = generate_initial_grid(grid_size);
    // Initial display:
    // If there's a step delay, the first "Op #" will clear the screen.
    // To see the initial board briefly with delay, or non-flickering without delay:
    if (STEP_DELAY_SECONDS == 0.0) {
         display_grid(initial_board, "Initial Board"); // Display once if no step-by-step
    } else {
        // For step-by-step, display it, it will be cleared by the first operation display.
        display_grid(initial_board, "Initial Board (before first operation)");
        if (STEP_DELAY_SECONDS > 0.1) { // If delay is substantial, add a small pause to see it
             std::this_thread::sleep_for(std::chrono::milliseconds(static_cast<int>(STEP_DELAY_SECONDS * 500))); // e.g., half of step delay
        }
    }


    HeuristicSolver solver(initial_board, 
                           rotate_subgrid, 
                           STEP_DELAY_SECONDS > 0 ? display_grid : nullptr, 
                           STEP_DELAY_SECONDS);

    std::cout << "\nSolving a " << grid_size << "x" << grid_size << " board..." << std::endl;
    if (STEP_DELAY_SECONDS > 0) {
        std::cout << "Step-by-step display is ON with " << STEP_DELAY_SECONDS << "s delay per operation/event." << std::endl;
    } else {
        std::cout << "Step-by-step display is OFF (set delay > 0 to enable)." << std::endl;
    }
    std::cout << "PairFormationSolver MAX_BFS_STEPS is set to: " << PairFormationSolver::MAX_BFS_STEPS << std::endl;
    
    auto start_time = std::chrono::high_resolution_clock::now();
    Path operations = solver.solve();
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> execution_time = end_time - start_time;

    if (STEP_DELAY_SECONDS > 0 && solver.operation_count_for_display > 0) { 
        #ifndef _WIN32
        // std::cout << "\033[H\033[J" << std::flush; // Clear screen before final summary if step-by-step was on and ops occurred
        // Let the final "Final Board" display manage its own screen space.
        #endif
    }

    std::cout << "\n--- Heuristic Solve Process Complete ---" << std::endl;
    std::cout << "Execution time: " << execution_time.count() << " seconds" << std::endl;
    std::cout << "Total operations performed: " << operations.size() 
              << " (display count was Op #" << solver.operation_count_for_display << ")" << std::endl;
    
    Grid final_board = solver.current_grid;
    display_grid(final_board, "Final Board after Heuristic Solve"); // This will clear if its title matches clear condition

    int num_unsolved_final = get_unsolved_pairs_coords(final_board).size() / 2;
    if (num_unsolved_final == 0) {
         std::cout << "The board appears to be fully solved by the heuristic." << std::endl;
    } else {
        std::cout << "Board has " << num_unsolved_final << " unsolved pairs remaining." << std::endl;
    }

    std::cout << "\nTest finished." << std::endl;

    return 0;
}