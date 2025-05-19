/*************************************************************************************************
CNFTools -- Copyright (c) 2021, Markus Iser, KIT - Karlsruhe Institute of Technology
ISOHash2 -- Copyright (c) 2025, Timon Passlick, KIT - Karlsruhe Institute of Technology
ISOHash2 Edits -- Copyright (c) 2025, Frederick Gehm, KIT - Karlsruhe Institute of Technology

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOTLIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef ISOHASH2_H_
#define ISOHASH2_H_

#include <algorithm>
#include <atomic>
#include <chrono>
#include <functional>
#include <optional>
#include <type_traits>
#include <unordered_set>
#include <vector>
#include <memory>
#include <fstream>
#include <unistd.h>

#define XXH_INLINE_ALL
#include "xxhash.h"

#include "src/util/CNFFormula.h" // Includes SolverTypes::Lit

// Utility Functions
long get_mem_usage() {
    std::ifstream statm("/proc/self/statm");
    if (!statm.is_open()) return -1;
    long size, resident, share, text, lib, data, dt;
    statm >> size >> resident >> share >> text >> lib >> data >> dt;
    return resident * sysconf(_SC_PAGE_SIZE);
}

namespace CNF {

// Data Structures & Config
struct WLHRuntimeConfig {
    unsigned depth;
    bool cross_reference_literals;
    bool rehash_clauses;
    bool optimize_first_iteration;
    unsigned progress_iteration;
    bool return_measurements;
    bool sort_for_clause_hash;
};

template<typename HashType>
struct LitColorsTpl {
    HashType p = 0;
    HashType n = 0;
    inline void flip() { std::swap(n, p); }
    template <typename Hasher>
    inline void cross_reference(const Hasher& h) {
        const HashType pcr = h(*this);
        flip();
        const HashType ncr = h(*this);
        p = pcr;
        n = ncr;
    }
    template <typename Hasher>
    inline HashType variable_hash(const Hasher& h) const {
        LitColorsTpl copy = *this;
        if (n > p) copy.flip();
        return h(copy);
    }
};

template<typename HashType, typename LiteralType, typename LitColorsType>
struct ColorFunctionTpl {
    std::vector<LitColorsType> colors;
    explicit ColorFunctionTpl(const std::size_t num_vars) : colors(num_vars + 1, {1, 1}) {}
    inline HashType& operator()(const LiteralType lit) {
        return reinterpret_cast<HashType*>(&colors[lit.var().id])[lit.sign()];
    }
};

// Weisfeiler-Leman Hasher
template <typename CNFInput>
struct WeisfeilerLemanHasher {
    static constexpr bool use_xxh3 = true;
    static constexpr bool use_prime_ring = false;
    using Hash = std::uint64_t;

    using Clock = std::chrono::high_resolution_clock;
    using InputClause = typename CNFInput::Clause;
    using Literal = Lit;

    using ActualLitColors = LitColorsTpl<Hash>;
    using ActualColorFunction = ColorFunctionTpl<Hash, Literal, ActualLitColors>;

    const WLHRuntimeConfig cfg;
    const CNFInput cnf;

    ActualColorFunction color_functions[2];
    unsigned iteration = 0;

    std::unordered_set<Hash> unique_hashes;
    unsigned previous_unique_hashes = 1;

    long parsing_start_mem;
    Clock::time_point parsing_start_time;
    long start_mem;
    Clock::time_point start_time;

    WeisfeilerLemanHasher(const char* filename, const WLHRuntimeConfig config)
        : cfg(config),
          parsing_start_mem(get_mem_usage()),
          parsing_start_time(Clock::now()),
          cnf(filename),
          start_mem(get_mem_usage()),
          start_time(Clock::now()),
          color_functions{ActualColorFunction(cnf.nVars()), ActualColorFunction(cnf.nVars())}
    {}

    inline ActualColorFunction& old_color() { return color_functions[iteration % 2]; }
    inline ActualColorFunction& new_color() { return color_functions[(iteration + 1) % 2]; }

    template <typename T>
    static inline Hash hash_object(const T& t) {
        static_assert(std::is_standard_layout<T>::value && std::is_trivial<T>::value, "Object must be POD-like for direct memory hashing.");
        return XXH3_64bits(&t, sizeof(t));
    }

    static inline void combine_hash(Hash* accumulator, Hash input_hash) {
        *accumulator += input_hash;
    }

    template <typename ElementType, typename ContainerType>
    static inline Hash sum_hashes(const ContainerType& container,
                                   const std::function<Hash(const ElementType&)>& element_to_hash_fn) {
        Hash total_hash = 0;
        for (const ElementType& element : container) {
            combine_hash(&total_hash, element_to_hash_fn(element));
        }
        return total_hash;
    }

    // WL Algo Steps
    inline bool in_optimized_iteration() const {
        return iteration == 0 && cfg.optimize_first_iteration;
    }

    void update_literal_cross_references() {
        if (!cfg.cross_reference_literals || in_optimized_iteration()) return;
        auto hasher_func = [this](const ActualLitColors& lc){ return hash_object(lc); };
        for (size_t i = 1; i < old_color().colors.size(); ++i) { // Iterate actual variables
             old_color().colors[i].cross_reference(hasher_func);
        }
    }

    Hash calculate_clause_hash(const InputClause& cl_view) {
        if (!cfg.sort_for_clause_hash) {
            Hash h = sum_hashes<const Literal>(cl_view,
                [this](const Literal lit) { return old_color()(lit); });
            if (cfg.rehash_clauses) h = hash_object(h);
            return h;
        } else {
            std::vector<Hash> sorted_colors;
            sorted_colors.reserve(cl_view.size());
            for (const Literal lit : cl_view) sorted_colors.push_back(old_color()(lit));
            std::sort(sorted_colors.begin(), sorted_colors.end());
            return XXH3_64bits(sorted_colors.data(), sorted_colors.size() * sizeof(Hash));
        }
    }

    void perform_iteration_step() {
        update_literal_cross_references();
        for (const InputClause cl_view : cnf.clauses()) {
            const Hash clause_h = (!in_optimized_iteration())
                                      ? calculate_clause_hash(cl_view)
                                      : cfg.rehash_clauses ? hash_object(cl_view.size()) : cl_view.size();
            for (const Literal lit : cl_view) {
                combine_hash(&new_color()(lit), clause_h);
            }
        }
        ++iteration;
    }

    Hash calculate_variables_hash() {
        if (cfg.cross_reference_literals) {
            auto hasher_func = [this](const ActualLitColors& lc){ return hash_object(lc); };
            Hash total_hash = 0;
            for (size_t i = 1; i < old_color().colors.size(); ++i) { // Iterate actual variables
                 combine_hash(&total_hash, old_color().colors[i].variable_hash(hasher_func));
            }
            return total_hash;
        }
        Hash h = 0;
        for (unsigned var_id = 1; var_id <= cnf.nVars(); ++var_id) {
             combine_hash(&h, old_color()(Literal(Var(var_id), false)));
             combine_hash(&h, old_color()(Literal(Var(var_id), true)));
        }
        return h;
    }

    Hash calculate_cnf_hash() {
        update_literal_cross_references();
        return sum_hashes<InputClause>(cnf.clauses(),
            [this](const InputClause& cl_view) { return calculate_clause_hash(cl_view); });
    }

    // Algo Control
    std::optional<Hash> check_for_progress_stabilization() {
        if (iteration == 0 || iteration < 6 ||
            (iteration != cfg.progress_iteration && iteration != cfg.progress_iteration + 1)) {
            return std::nullopt;
        }
        unique_hashes.clear();
        unique_hashes.reserve(previous_unique_hashes);
        auto hasher_func = [this](const ActualLitColors& lc){ return hash_object(lc); };
        Hash current_variables_hash_sum = 0;
        for (size_t i = 1; i < old_color().colors.size(); ++i) { // Iterate actual variables
            const Hash var_h = old_color().colors[i].variable_hash(hasher_func);
            unique_hashes.insert(var_h);
            combine_hash(current_variables_hash_sum, var_h);
        }
        if (unique_hashes.size() <= previous_unique_hashes) return current_variables_hash_sum;
        previous_unique_hashes = unique_hashes.size();
        return std::nullopt;
    }

    // Run Algo
    Hash execute_wl_algorithm() {
        while (iteration < cfg.depth / 2) {
            if (const auto stabilized_hash = check_for_progress_stabilization()) return *stabilized_hash;
            perform_iteration_step();
        }
        return (cfg.depth % 2 == 0) ? calculate_variables_hash() : calculate_cnf_hash();
    }

    std::string operator()() {
        std::string result_hash_str = std::to_string(execute_wl_algorithm());
        if (cfg.return_measurements) {
            const auto calculation_end_time = Clock::now();
            const auto calculation_time_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(calculation_end_time - start_time).count();
            const auto parsing_time_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(start_time - parsing_start_time).count();
            long final_mem_usage_bytes = get_mem_usage();
            long calculation_mem_delta_bytes = (start_mem != -1 && final_mem_usage_bytes != -1) ? (final_mem_usage_bytes - start_mem) : -1;
            long parsing_mem_delta_bytes = (parsing_start_mem != -1 && start_mem != -1) ? (start_mem - parsing_start_mem) : -1;
            const double actual_iteration_count = std::min<double>(iteration, cfg.depth / 2.0);
            result_hash_str +=
                "," + std::to_string(parsing_time_ns) +
                "," + std::to_string(calculation_time_ns) +
                "," + std::to_string(parsing_mem_delta_bytes) +
                "," + std::to_string(calculation_mem_delta_bytes) +
                "," + std::to_string(actual_iteration_count) +
                "," + std::to_string(cnf.nVars()) +
                "," + std::to_string(cnf.nClauses()) +
                "," + std::to_string(cnf.nLits()) +
                "," + std::to_string(cnf.maxClauseLength());
        }
        return result_hash_str;
    }
};

// Public API Function
/**
 * @brief Comparing Weisfeiler-Leman hashes is approximately as strong as
 * running the Weisfeiler-Leman algorithm on the literal hypergraph.
 * Runtime O(h*n), space O(n).
 * (Doxygen parameters retained from original for API documentation)
 * @param filename benchmark instance
 * @param depth maximum iterations / 2, half iterations hash clause labels
 * @param cross_reference_literals whether the information which literals
 * belong to the same variable should be used in the calculation
 * @param rehash_clauses whether the clause hash input should be
 * rehashed
 * @param optimize_first_iteration whether the first iteration should be
 * optimized
 * @param progress_check_iteration the iteration after which the
 * progress check runs
 * @param return_measurements whether the parsing time, the calculation
 * time (both nanoseconds), the memory usage (bytes) and the amount of
 * iterations that were calculated (possibly half) should be returned
 * @param sort_for_clause_hash whether the clause hash input should be
 * sorted and input directly into the hash function
 * @return comma separated list, std::string Weisfeiler-Leman hash,
 * possibly measurements
 */
std::string weisfeiler_leman_hash(
    const char* filename,
    const unsigned depth = 13,
    const bool cross_reference_literals = true,
    const bool rehash_clauses = true,
    const bool optimize_first_iteration = true,
    const unsigned progress_check_iteration = 6,
    const bool return_measurements = true,
    const bool sort_for_clause_hash = false)
{
    CNF::WLHRuntimeConfig cfg{
        depth, cross_reference_literals, rehash_clauses, optimize_first_iteration,
        progress_check_iteration, return_measurements, sort_for_clause_hash,
    };
    CNF::WeisfeilerLemanHasher<CNFFormula> hasher(filename, cfg);
    return hasher();
}

} // namespace CNF

#endif // ISOHASH2_H_