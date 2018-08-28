/*******************************************************************\

Module: Simplified strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_BINSEARCH_H

#include "strategy_solver_base.h"
#include "tpolyhedra_domain.h"

class strategy_solver_binsearcht:public strategy_solver_baset
{
public:
  strategy_solver_binsearcht(
    tpolyhedra_domaint &_tpolyhedra_domain,
    incremental_solvert &_solver,
    const namespacet &_ns):
    strategy_solver_baset(_solver, _ns),
    tpolyhedra_domain(_tpolyhedra_domain)
  {
  }

  virtual bool iterate(invariantt &inv);
  virtual bool iterate_for_recursive(
  invariantt &inv, tmpl_rename_mapt templ_maps,bool cntxt_sensitive);

protected:
  tpolyhedra_domaint &tpolyhedra_domain;
  exprt get_rec_call_pre_constraints(
   const tpolyhedra_domaint::templ_valuet &val,
   tmpl_rename_mapt templ_maps,
   const std::set<tpolyhedra_domaint::rowt> &symb_rows=
   std::set<tpolyhedra_domaint::rowt>());
  
  std::vector<std::vector<exprt>> get_rec_call_post_constraints(
   const tpolyhedra_domaint::templ_valuet &val,
   tmpl_rename_mapt templ_maps);
  exprt get_rec_call_symb_post_constraints(
   const tpolyhedra_domaint::templ_valuet &val,
   tmpl_rename_mapt templ_maps,
   std::size_t row);
  void get_max_lower(tmpl_rename_mapt templ_maps,std::size_t row);
};

#endif
