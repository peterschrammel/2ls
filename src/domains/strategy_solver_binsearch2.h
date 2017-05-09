/*******************************************************************\

Module: Strategy iteration solver by binary search
        with optimisation of the parameter sum

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH2_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH2_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearch2t:public strategy_solver_baset
{
 public:
  strategy_solver_binsearch2t(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    literalt _assertion_check,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _assertion_check, _ns),
    tpolyhedra_domain(_tpolyhedra_domain),
    sum_bound_counter(0)
  {
  }

  virtual progresst iterate(invariantt &inv);

 protected:
  tpolyhedra_domaint &tpolyhedra_domain;
  unsigned sum_bound_counter;
};

#endif // CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH2_H
