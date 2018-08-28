/*******************************************************************\

Module: Simplified strategy iteration solver by binary search

Author: Peter Schrammel

\*******************************************************************/

#ifdef DEBUG
#include <iostream>
#endif

#include "strategy_solver_binsearch.h"
#include "util.h"

/*******************************************************************\

Function: strategy_solver_binsearcht::iterate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool strategy_solver_binsearcht::iterate(invariantt &_inv)
{
  tpolyhedra_domaint::templ_valuet &inv=
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved=false;

  solver.new_context(); // for improvement check

  exprt inv_expr=tpolyhedra_domain.to_pre_constraints(inv);
  
//#if 0
  debug() << "improvement check: " << eom;
  debug() << "pre-inv: " << from_expr(ns, "", inv_expr) << eom;
//#endif

  solver << inv_expr;

  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(
    inv, strategy_cond_exprs, strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

//#if 0
  debug() << "post-inv: ";
//#endif
  for(std::size_t i=0; i<strategy_cond_exprs.size(); i++)
  {
//#if 0
    debug() << (i>0 ? " || " : "") << from_expr(ns, "", strategy_cond_exprs[i]);
//#endif
    strategy_cond_literals[i]=solver.convert(strategy_cond_exprs[i]);
    // solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i]=literal_exprt(strategy_cond_literals[i]);
  }
//#if 0
  debug() << eom;
//#endif

  solver << disjunction(strategy_cond_exprs);

#if 0
  debug() << "solve(): ";
#endif

  if(solver()==decision_proceduret::D_SATISFIABLE) // improvement check
  {
//#if 0
    debug() << "SAT" << eom;
//#endif

#if 0
    for(std::size_t i=0; i<solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i]
              << " " << solver.l_get(solver.formula[i]) << eom;
    }

    for(std::size_t i=0; i<tpolyhedra_domain.template_size(); i++)
    {
      exprt c=tpolyhedra_domain.get_row_post_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " "
              << from_expr(ns, "", solver.get(c)) << eom;
      debug() << "expr: " << from_expr(ns, "", strategy_value_exprs[i]) << " "
              << from_expr(
                ns, "", simplify_const(solver.get(strategy_value_exprs[i])))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", tpolyhedra_domain.templ[i].pre_guard) << " "
              << from_expr(
                ns, "", solver.get(tpolyhedra_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", tpolyhedra_domain.templ[i].post_guard)
              << " "
              << from_expr(
                ns, "", solver.get(tpolyhedra_domain.templ[i].post_guard))
              << eom;
    }
#endif


    std::size_t row=0;
    for(; row<strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true())
        break;  // we've found a row to improve
    }

    debug() << "improving row: " << row << eom;
    std::set<tpolyhedra_domaint::rowt> improve_rows;
    improve_rows.insert(row);

    tpolyhedra_domaint::row_valuet upper=
      tpolyhedra_domain.get_max_row_value(row);
    tpolyhedra_domaint::row_valuet lower=
      simplify_const(solver.get(strategy_value_exprs[row]));

    solver.pop_context();  // improvement check

    solver.new_context(); // symbolic value system

    exprt pre_inv_expr=
      tpolyhedra_domain.to_symb_pre_constraints(inv, improve_rows);

    solver << pre_inv_expr;

    exprt post_inv_expr=tpolyhedra_domain.get_row_symb_post_constraint(row);

    solver << post_inv_expr;

//#if 0
    debug() << "symbolic value system: " << eom;
    debug() << "pre-inv: " << from_expr(ns, "", pre_inv_expr) << eom;
    debug() << "post-inv: " << from_expr(ns, "", post_inv_expr) << eom;
//#endif

    while(tpolyhedra_domain.less_than(lower, upper))
    {
      tpolyhedra_domaint::row_valuet middle=
        tpolyhedra_domain.between(lower, upper);
      if(!tpolyhedra_domain.less_than(lower, middle))
        middle=upper;

      // row_symb_value >= middle
      exprt c=
        tpolyhedra_domain.get_row_symb_value_constraint(row, middle, true);

//#if 0
      debug() << "upper: " << from_expr(ns, "", upper) << eom;
      debug() << "middle: " << from_expr(ns, "", middle) << eom;
      debug() << "lower: " << from_expr(ns, "", lower) << eom;
//#endif

      solver.new_context(); // binary search iteration

//#if 0
      debug() << "constraint: " << from_expr(ns, "", c) << eom;
//#endif

      solver << c;

      if(solver()==decision_proceduret::D_SATISFIABLE)
      {
//#if 0
        debug() << "SAT" << eom;
//#endif

#if 0
        for(std::size_t i=0; i<tpolyhedra_domain.template_size(); i++)
        {
          debug() << from_expr(ns, "", tpolyhedra_domain.get_row_symb_value(i))
                  << " " << from_expr(
                    ns, "", solver.get(tpolyhedra_domain.get_row_symb_value(i)))
                  << eom;
        }
#endif

#if 0
        for(const auto &rm : renaming_map)
        {
          debug() << "replace_map (1st): "
                  << from_expr(ns, "", rm.first) << " "
                  << from_expr(ns, "", solver.get(rm.first)) << eom;
          debug() << "replace_map (2nd): "
                  << from_expr(ns, "", rm.second) << " "
                  << from_expr(ns, "", solver.get(rm.second)) << eom;
        }
#endif

        lower=simplify_const(
          solver.get(tpolyhedra_domain.get_row_symb_value(row)));
      }
      else
      {
//#if 0
        debug() << "UNSAT" << eom;
//#endif

#if 0
        for(std::size_t i=0; i<solver.formula.size(); ++i)
        {
          if(solver.solver->is_in_conflict(solver.formula[i]))
            debug() << "is_in_conflict: " << solver.formula[i] << eom;
          else
            debug() << "not_in_conflict: " << solver.formula[i] << eom;
        }
#endif

        if(!tpolyhedra_domain.less_than(middle, upper))
          middle=lower;
        upper=middle;
      }
      solver.pop_context(); // binary search iteration
    }

    debug() << "update value: " << from_expr(ns, "", lower) << eom;

    solver.pop_context();  // symbolic value system

    tpolyhedra_domain.set_row_value(row, lower, inv);
    improved=true;
  }
  else
  {
//#if 0
    debug() << "UNSAT" << eom;
//#endif

#ifdef DEBUG_FORMULA
    for(std::size_t i=0; i<solver.formula.size(); ++i)
    {
      if(solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }
#endif

    solver.pop_context(); // improvement check
  }

  return improved;
}

bool strategy_solver_binsearcht::iterate_for_recursive(invariantt &_inv,
 tmpl_rename_mapt templ_maps,bool cntxt_sensitive)
{
  tpolyhedra_domaint::templ_valuet &inv=
    static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);

  bool improved=false;

  solver.new_context(); // for improvement check

  exprt inv_expr=tpolyhedra_domain.to_pre_constraints(inv);
  inv_expr=and_exprt(inv_expr,get_rec_call_pre_constraints(inv,templ_maps));

//#if 0
  debug() << "improvement check: " << eom;
  debug() << "pre-inv: " << from_expr(ns, "", inv_expr) << eom;
//#endif

  solver << inv_expr;
  
  exprt::operandst strategy_cond_exprs;
  tpolyhedra_domain.make_not_post_constraints(
    inv, strategy_cond_exprs, strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

//#if 0
  debug() << "post-inv: ";
//#endif
  for(std::size_t i=0; i<strategy_cond_exprs.size(); i++)
  {
//#if 0
    debug() << (i>0 ? " || " : "") << from_expr(ns, "", strategy_cond_exprs[i]);
//#endif
    strategy_cond_literals[i]=solver.convert(strategy_cond_exprs[i]);
    // solver.set_frozen(strategy_cond_literals[i]);
    strategy_cond_exprs[i]=literal_exprt(strategy_cond_literals[i]);
  }
  
  if(cntxt_sensitive)
  {
    std::vector<std::vector<exprt>> constraints=
     get_rec_call_post_constraints(inv,templ_maps);
    std::size_t i=0;
    while(tpolyhedra_domain.templ[i].kind!=domaint::IN) {i++;}
    for(std::vector<exprt> exprs:constraints)
    {
      strategy_cond_literals[i]=solver.convert(disjunction(exprs));
      strategy_cond_exprs[i]=literal_exprt(strategy_cond_literals[i]);
      i++;
    }
    assert(strategy_cond_literals.size()==tpolyhedra_domain.templ.size());
  }
//#if 0
  debug() << eom;
//#endif

  solver << disjunction(strategy_cond_exprs);

//#if 0
  debug() << "solve(): ";
//#endif

  if(solver()==decision_proceduret::D_SATISFIABLE) // improvement check
  {
//#if 0
    debug() << "SAT" << eom;
//#endif

#if 0
    for(std::size_t i=0; i<solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i]
              << " " << solver.l_get(solver.formula[i]) << eom;
    }

    for(std::size_t i=0; i<tpolyhedra_domain.template_size(); i++)
    {
      exprt c=tpolyhedra_domain.get_row_post_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " "
              << from_expr(ns, "", solver.get(c)) << eom;
      debug() << "expr: " << from_expr(ns, "", strategy_value_exprs[i]) << " "
              << from_expr(
                ns, "", simplify_const(solver.get(strategy_value_exprs[i])))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", tpolyhedra_domain.templ[i].pre_guard) << " "
              << from_expr(
                ns, "", solver.get(tpolyhedra_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", tpolyhedra_domain.templ[i].post_guard)
              << " "
              << from_expr(
                ns, "", solver.get(tpolyhedra_domain.templ[i].post_guard))
              << eom;
    }
#endif

    std::size_t row=0;
    for(; row<strategy_cond_literals.size(); row++)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true())
        break;  // we've found a row to improve
    }
    
    debug() << "improving row: " << row << eom;
    std::set<tpolyhedra_domaint::rowt> improve_rows;
    improve_rows.insert(row);
    if(tpolyhedra_domain.templ[row].kind==domaint::IN)
      get_max_lower(templ_maps,row);

    tpolyhedra_domaint::row_valuet upper=
      tpolyhedra_domain.get_max_row_value(row);
    tpolyhedra_domaint::row_valuet lower=
      simplify_const(solver.get(strategy_value_exprs[row]));

    solver.pop_context();  // improvement check

    solver.new_context(); // symbolic value system

    exprt pre_inv_expr=
      tpolyhedra_domain.to_symb_pre_constraints(inv, improve_rows);
    pre_inv_expr=and_exprt(pre_inv_expr,
     get_rec_call_pre_constraints(inv,templ_maps,improve_rows));

    solver << pre_inv_expr;

    exprt post_inv_expr;
    if(tpolyhedra_domain.templ[row].kind!=domaint::IN)
      post_inv_expr=tpolyhedra_domain.get_row_symb_post_constraint(row);
    else
      post_inv_expr=get_rec_call_symb_post_constraints(
       inv,templ_maps,row);

    solver << post_inv_expr;

//#if 0
    debug() << "symbolic value system: " << eom;
    debug() << "pre-inv: " << from_expr(ns, "", pre_inv_expr) << eom;
    debug() << "post-inv: " << from_expr(ns, "", post_inv_expr) << eom;
//#endif

    while(tpolyhedra_domain.less_than(lower, upper))
    {
      tpolyhedra_domaint::row_valuet middle=
        tpolyhedra_domain.between(lower, upper);
      if(!tpolyhedra_domain.less_than(lower, middle))
        middle=upper;

      // row_symb_value >= middle
      exprt c=
        tpolyhedra_domain.get_row_symb_value_constraint(row, middle, true);

//#if 0
      debug() << "upper: " << from_expr(ns, "", upper) << eom;
      debug() << "middle: " << from_expr(ns, "", middle) << eom;
      debug() << "lower: " << from_expr(ns, "", lower) << eom;
//#endif

      solver.new_context(); // binary search iteration

//#if 0
      debug() << "constraint: " << from_expr(ns, "", c) << eom;
//#endif

      solver << c;
      
      if(solver()==decision_proceduret::D_SATISFIABLE)
      {
//#if 0
        debug() << "SAT" << eom;
//#endif

#if 0
        for(std::size_t i=0; i<tpolyhedra_domain.template_size(); i++)
        {
          debug() << from_expr(ns, "", tpolyhedra_domain.get_row_symb_value(i))
                  << " " << from_expr(
                    ns, "", solver.get(tpolyhedra_domain.get_row_symb_value(i)))
                  << eom;
        }
#endif

#if 0
        for(const auto &rm : renaming_map)
        {
          debug() << "replace_map (1st): "
                  << from_expr(ns, "", rm.first) << " "
                  << from_expr(ns, "", solver.get(rm.first)) << eom;
          debug() << "replace_map (2nd): "
                  << from_expr(ns, "", rm.second) << " "
                  << from_expr(ns, "", solver.get(rm.second)) << eom;
        }
#endif

        lower=simplify_const(
          solver.get(tpolyhedra_domain.get_row_symb_value(row)));
      }
      else
      {
#if 0
        debug() << "UNSAT" << eom;
#endif

#if 0
        for(std::size_t i=0; i<solver.formula.size(); ++i)
        {
          if(solver.solver->is_in_conflict(solver.formula[i]))
            debug() << "is_in_conflict: " << solver.formula[i] << eom;
          else
            debug() << "not_in_conflict: " << solver.formula[i] << eom;
        }
#endif

        if(!tpolyhedra_domain.less_than(middle, upper))
          middle=lower;
        upper=middle;
      }
      solver.pop_context(); // binary search iteration
    }

    debug() << "update value: " << from_expr(ns, "", lower) << eom;

    solver.pop_context();  // symbolic value system

    tpolyhedra_domain.set_row_value(row, lower, inv);
    improved=true;
  }
  else
  {
#if 0
    debug() << "UNSAT" << eom;
#endif

#ifdef DEBUG_FORMULA
    for(std::size_t i=0; i<solver.formula.size(); ++i)
    {
      if(solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }
#endif

    solver.pop_context(); // improvement check
  }

  return improved;
}

exprt strategy_solver_binsearcht::get_rec_call_pre_constraints(
 const tpolyhedra_domaint::templ_valuet &val,
 tmpl_rename_mapt templ_maps,
 const std::set<tpolyhedra_domaint::rowt> &symb_rows)
{
  assert(val.size()==tpolyhedra_domain.templ.size());
  std::vector<exprt> constraints;
  for(auto map:templ_maps)
  {
    std::vector<exprt> vars=map.second;
    std::vector<exprt>::iterator it=vars.begin();
    for(std::size_t i=0;i<tpolyhedra_domain.template_size();i=i+2,it++)
    {
      if(tpolyhedra_domain.templ.at(i).kind==domaint::OUT)
      {
        if(symb_rows.find(i)==symb_rows.end())
        {
          if(val[i].get(ID_value)==ID_false)
            constraints.push_back(implies_exprt(map.first,false_exprt()));
          else if(val[i].get(ID_value)==ID_true)
            constraints.push_back(implies_exprt(map.first,true_exprt()));
          else constraints.push_back(implies_exprt(map.first,
           binary_relation_exprt(*it, ID_le, val[i])));
        }
        else
        {
          constraints.push_back(implies_exprt(map.first,
           binary_relation_exprt(*it, ID_le, 
           symbol_exprt("symb_bound#"+i2string(tpolyhedra_domain.domain_number)+"$"+
           i2string(i), it->type()))));
        }
        if(symb_rows.find(i+1)==symb_rows.end())
        {
          if(val[i+1].get(ID_value)==ID_false)
            constraints.push_back(implies_exprt(map.first,false_exprt()));
          else if(val[i+1].get(ID_value)==ID_true)
            constraints.push_back(implies_exprt(map.first,true_exprt()));
          else constraints.push_back(implies_exprt(map.first,
           binary_relation_exprt(unary_minus_exprt(typecast_exprt(*it,
           tpolyhedra_domain.templ.at(i+1).expr.type())),
           ID_le, val[i+1])));
        }
        else
        {
          constraints.push_back(implies_exprt(map.first,
           binary_relation_exprt(unary_minus_exprt(typecast_exprt(*it,
           tpolyhedra_domain.templ.at(i+1).expr.type())),
           ID_le, symbol_exprt("symb_bound#"+i2string(tpolyhedra_domain.domain_number)+"$"+
           i2string(i+1), it->type()))));
        }
      }
    }
  }
  return conjunction(constraints);
}

std::vector<std::vector<exprt>> strategy_solver_binsearcht::
 get_rec_call_post_constraints(
 const tpolyhedra_domaint::templ_valuet &val,
 tmpl_rename_mapt templ_maps)
{
  assert(val.size()==tpolyhedra_domain.templ.size());
  std::vector<std::vector<exprt>> constraints;
  std::size_t i=0;
  for(auto temp:tpolyhedra_domain.templ)
  {
    if(temp.kind==domaint::IN) i++;
  }
  constraints.resize(i);
  constraints[2].push_back(true_exprt());
  for(auto map:templ_maps)
  {
    std::vector<exprt> vars=map.second;
    std::vector<exprt>::iterator it=vars.begin();
    std::size_t j=0;
    for(std::size_t i=0;i<tpolyhedra_domain.template_size();i+=2,it++)
    {
      if(tpolyhedra_domain.templ.at(i).kind==domaint::IN)
      {
        if(val[i].get(ID_value)==ID_false)
          constraints[j].push_back(and_exprt(tpolyhedra_domain.templ[i].aux_expr,
           not_exprt(implies_exprt(map.first,false_exprt()))));
        else if(val[i].get(ID_value)==ID_true)
          constraints[j].push_back(and_exprt(tpolyhedra_domain.templ[i].aux_expr,
           not_exprt(implies_exprt(map.first,true_exprt()))));
        else constraints[j].push_back(and_exprt(tpolyhedra_domain.templ[i].aux_expr,
              not_exprt(implies_exprt(map.first,
              binary_relation_exprt(*it, ID_le, val[i])))));
        
        if(val[i+1].get(ID_value)==ID_false)
          constraints[j+1].push_back(and_exprt(tpolyhedra_domain.templ[i+1].aux_expr,
           not_exprt(implies_exprt(map.first,false_exprt()))));
        else if(val[i+1].get(ID_value)==ID_true)
          constraints[j+1].push_back(and_exprt(tpolyhedra_domain.templ[i+1].aux_expr,
           not_exprt(implies_exprt(map.first,true_exprt()))));
        else constraints[j+1].push_back(and_exprt(tpolyhedra_domain.templ[i+1].aux_expr,
         not_exprt(implies_exprt(map.first,
         binary_relation_exprt(unary_minus_exprt(typecast_exprt(*it,
         tpolyhedra_domain.templ.at(i+1).expr.type())),
         ID_le, val[i+1])))));
//#if 0
        debug() << " || " << from_expr(ns, "", constraints[j].back());
        debug() << " || " << from_expr(ns, "", constraints[j+1].back());
//#endif
        j+=2;
      }
    }
  }
  return constraints;
}

exprt strategy_solver_binsearcht::get_rec_call_symb_post_constraints(
 const tpolyhedra_domaint::templ_valuet &val,
 tmpl_rename_mapt templ_maps,
 std::size_t row)
{
  assert(row<tpolyhedra_domain.templ.size());
  std::vector<exprt> post;
  for(auto map:templ_maps)
  {
    std::vector<exprt> vars=map.second;
    if(row%2==0)
      post.push_back(and_exprt(tpolyhedra_domain.templ[row].aux_expr,not_exprt(
       implies_exprt(map.first,binary_relation_exprt(vars[row/2],ID_le,
       symbol_exprt("symb_bound#"+i2string(tpolyhedra_domain.domain_number)+"$"+
       i2string(row), vars[row/2].type()))))));
    else
      post.push_back(and_exprt(tpolyhedra_domain.templ[row].aux_expr,not_exprt(
       implies_exprt(map.first,binary_relation_exprt(unary_minus_exprt
       (typecast_exprt(vars[(row/2)+1],tpolyhedra_domain.templ[row].expr.type())),ID_le,
       symbol_exprt("symb_bound#"+i2string(tpolyhedra_domain.domain_number)+"$"+
       i2string(row), vars[(row/2)+1].type()))))));
  }
  return disjunction(post);
}

void strategy_solver_binsearcht::get_max_lower(tmpl_rename_mapt templ_maps,
 std::size_t row)
{
  tpolyhedra_domaint::row_valuet val=tpolyhedra_domain.get_min_row_value(row),tmp;
  for(tmpl_rename_mapt::iterator it=templ_maps.begin();
   it!=templ_maps.end();it++)
  {
    if(solver.get(it->first).is_false()) continue;
    std::size_t i=0;
    while(tpolyhedra_domain.templ[i].kind!=domaint::IN) {i++;}
    tmp=to_constant_expr(solver.get(it->second[row-i]));
    if(tpolyhedra_domain.less_than(val,tmp))
    {
      val=tmp;
      strategy_value_exprs[i]=it->second[row-i];
    }
  }
}