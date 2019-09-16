/*******************************************************************\

Module: Disjunctive domain

Author: Johanan Wahlang

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_DISJUNCTIVE_DOMAIN_H
#define CPROVER_2LS_DOMAINS_DISJUNCTIVE_DOMAIN_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <util/i2string.h>
#include <langapi/language_util.h>
#include <util/replace_expr.h>
#include <util/namespace.h>
#include <ssa/local_ssa.h>

#include "domain.h"
#include "tpolyhedra_domain.h"
#include "symbolic_path.h"

class disjunctive_domaint:public domaint
{
public:
  enum template_kindt
  {
    TPOLYHEDRA, HEAP
  };
  typedef unsigned disjunctt;
  typedef std::map<disjunctt, std::map<disjunctt,domaint *>> templatet;

  typedef std::map<disjunctt, std::map<disjunctt,exprt::operandst>> disjunctive_exprst;
  typedef std::map<disjunctt, std::map<disjunctt,bvt>> disjunctive_literalst;

  class disjunctive_valuet:public valuet, public std::vector<valuet *>
  {
  };
  
  class lex_metrict
  {
  public:
    unsigned int incomparable;
    mp_integer distance;

    lex_metrict(
      unsigned int _incomparable=0,
      mp_integer _distance=0):
      incomparable(_incomparable),
      distance(_distance)
      {}
    friend bool operator< (const lex_metrict &m1, const lex_metrict &m2)
    {
      if (m1.incomparable<m2.incomparable)
      {
        return true;
      }
      else if (m2.incomparable<m1.incomparable)
      {
        return false;
      }
      else
      {
        return (m1.distance < m2.distance);
      }
    }
    friend bool operator> (const lex_metrict &m1, const lex_metrict &m2)
    {
      if(m1.incomparable>m2.incomparable)
      {
        return true;
      }
      else if (m2.incomparable>m1.incomparable)
      {
        return false;
      }
      else
      {
        return (m1.distance>m2.distance);
      }
    }
  };
  

  class unresolved_edget
  {
  public:
    disjunctt disjunct;
    symbolic_patht path;

    inline unresolved_edget() { }

    inline unresolved_edget(
      disjunctt _disjunct,
      symbolic_patht _path):
      disjunct(_disjunct),
      path(_path)
    {}
  };
  
  typedef std::vector<unresolved_edget> unresolved_sett;

  struct seen_edget
  {
    disjunctt source;
    symbolic_patht path;
    disjunctt sink;

    seen_edget(
      disjunctt _source,
      symbolic_patht _path,
      disjunctt _sink):
      source(_source),
      path(_path),
      sink(_sink)
    {}
  };
  
  // typedef std::vector<exprt> guardst;
  typedef std::map<disjunctt,std::map<disjunctt,symbolic_patht>> seen_sett;

  disjunctive_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const namespacet &_ns,
    const template_kindt _template_kind,
    const disjunctt _max,
    const lex_metrict _tol):
    domaint(_domain_number, _renaming_map, _ns),
    template_kind(_template_kind),
    max(_max),
    templ(),
    tol(_tol),
    unresolved_set(),
    seen_set()
  {
    if(template_kind==TPOLYHEDRA)
    {
      base_domain_ptr=new tpolyhedra_domaint(domain_number, renaming_map, _ns);
    }
  }

  virtual ~disjunctive_domaint()
  {
    if (base_domain_ptr!=NULL)
      delete base_domain_ptr;
    for (auto &i:templ)
    {
      for (auto &j:i.second)
      {
        if (j.second!=NULL)
          delete j.second;
      }
    }
  }

  virtual void initialize(valuet &value);
  
  virtual void join(valuet &value1, const valuet &value2);

  // printing
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result) override;

  inline template_kindt &get_template_kind()
  {
    return template_kind;
  }
  inline domaint *base_domain()
  {
    return base_domain_ptr;
  }

  disjunctt merge_heuristic(disjunctive_valuet &dv,valuet &v);
  lex_metrict hausdorff_distance(
    const tpolyhedra_domaint::templ_valuet &value1,
    const tpolyhedra_domaint::templ_valuet &value2);
  mp_integer distance(const constant_exprt &v1, const constant_exprt &v2);

  // exprt to_pre_constraints(const disjunctive_valuet &value);
  // exprt make_not_post_constraints(
  //   const disjunctive_valuet &value,
  //   disjunctive_exprst &cond_exprs,
  //   disjunctive_exprst &value_exprs);

protected:
  domaint *base_domain_ptr;
  template_kindt template_kind;
  disjunctt max;
  templatet templ;
  lex_metrict tol;
  unresolved_sett unresolved_set;
  seen_sett seen_set;

  friend class strategy_solver_disjunctivet;
};

#endif // CPROVER_2LS_DOMAINS_DISJUNCTIVE_DOMAIN_H
