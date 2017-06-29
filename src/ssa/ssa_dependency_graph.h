/*******************************************************************\

Module: SSA Dependency Graph

Author: Madhukar Kumar

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_SSA_DEPENDENCY_GRAPH_H
#define CPROVER_2LS_SSA_SSA_DEPENDENCY_GRAPH_H

#include <iostream>
#include <util/find_symbols.h>

#include "local_ssa.h"

class ssa_inlinert;
class ssa_dbt;

class ssa_dependency_grapht
{
public:
  ssa_dependency_grapht(ssa_dbt &_db, const namespacet &_ns):
    ssa_db(_db),
    ns(_ns)
  {
  }

  struct annotated_predecessort
  {
    int predecessor_node_index;
    find_symbols_sett annotation;
  };

  typedef std::list<annotated_predecessort> annotated_predecessorst;

  struct depnodet
  {
    exprt node_info;
    exprt guard; // guard binding or loop-head select
    bool is_assertion;
    bool is_function_call;
    bool is_loop;
    // bool trivial_guard;
    int rename_counter;
    find_symbols_sett used_symbols;
    find_symbols_sett modified_symbols;
    annotated_predecessorst predecessors;
    std::vector<int> successors;
    local_SSAt::locationt location;
  };

  // typedef std::map<unsigned, depnodet> depnodest;
  typedef std::vector<depnodet> depnodest;
  depnodest depnodes_map;

  int top_node_index;

  // special source_node and sink_node
  // depnodet source_node=depnodes_map[top_node_index];
  // depnodet sink_node=depnodes_map[0];

  void create(const local_SSAt &SSA, ssa_inlinert &ssa_inliner, bool entry);
  void output(std::ostream &) const;

protected:
  ssa_dbt &ssa_db;
  const namespacet &ns;
};

#endif // CPROVER_2LS_SSA_SSA_DEPENDENCY_GRAPH_H
