/*******************************************************************\

Module: Full strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH3_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH3_H

#include <ssa/local_ssa.h>

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearch3t:public strategy_solver_baset
{
 public:
  explicit strategy_solver_binsearch3t(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    local_SSAt& _SSA,
    literalt _assertion_check,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _assertion_check, _ns),
    SSA(_SSA),
    tpolyhedra_domain(_tpolyhedra_domain),
    sum_bound_counter(0) {}

  virtual progresst iterate(invariantt &inv);

 protected:
  local_SSAt &SSA;
  tpolyhedra_domaint &tpolyhedra_domain;
  unsigned sum_bound_counter;
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH3_H
