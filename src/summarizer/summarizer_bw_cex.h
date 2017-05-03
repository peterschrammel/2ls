/*******************************************************************\

Module: Counterexample-based Backward Analysis Base

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_BW_CEX_H
#define CPROVER_SUMMARIZER_BW_CEX_H

#include <util/message.h>
#include <goto-programs/property_checker.h>
#include <util/options.h>
#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include "summarizer_bw.h"

class summarizer_bw_cex_baset : public summarizer_bwt
{
 public:
  struct reason_infot
  {
    typedef local_SSAt::locationt function_infot; //call_site; restriction: we assume that there is a single function call in an SSA node
    typedef local_SSAt::locationt loop_infot;
    std::set<function_infot> functions;
    std::set<loop_infot> loops; 
  };

  class reasont : public std::map<irep_idt, reason_infot>
  {
  public:
    void merge(const reasont &other)
    {
      for(reasont::const_iterator it = other.begin();
	  it != other.end(); ++it)
      {
	reason_infot &r = (*this)[it->first];
        r.functions.insert(it->second.functions.begin(), 
			   it->second.functions.end());
        r.loops.insert(it->second.loops.begin(), it->second.loops.end());
      }
    }
  };

  virtual void summarize();
  virtual void summarize(const function_namet &entry_function);
  virtual void summarize(const exprt &_error_assertion);

  virtual property_checkert::resultt check();
  virtual void get_reason(reasont &_reason) { _reason.merge(reason); }  

 protected:
  function_namet entry_function;
  function_namet error_function;
  exprt error_assertion;
  reasont reason;

  explicit summarizer_bw_cex_baset(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner,
	     function_namet _entry_function,
	     function_namet _error_function): 
  summarizer_bwt(_options,_summary_db,_ssa_db,_ssa_unwinder,_ssa_inliner),
  entry_function(_entry_function),
  error_function(_error_function)
  {}

};


#endif
