/*******************************************************************\

Module: Solver for equalities/disequalities domain

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_EQUALITY_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_EQUALITY_H

#include "strategy_solver_base.h"
#include "equality_domain.h"

class strategy_solver_equalityt:public strategy_solver_baset
{
public:
  strategy_solver_equalityt(
    equality_domaint &_equality_domain,
    incremental_solvert &_solver,
    literalt _assertion_check,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _assertion_check, _ns),
    equality_domain(_equality_domain)
  {
    equality_domain.get_index_set(todo_equs);
  }

  virtual progresst iterate(invariantt &inv);

 protected:
  equality_domaint &equality_domain;

  typedef std::set<unsigned> worklistt;
  worklistt todo_equs;
  worklistt todo_disequs;
};

#endif
