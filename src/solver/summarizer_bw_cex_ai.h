/*******************************************************************\

Module: Summarizer for Backwards Error Analysis

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SOLVER_SUMMARIZER_BW_CEX_AI_H
#define CPROVER_2LS_SOLVER_SUMMARIZER_BW_CEX_AI_H

#include <util/message.h>
#include <util/options.h>
#include <ssa/ssa_inliner.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>

#include <util/time_stopping.h>

#include "summarizer_bw_cex.h"

class summarizer_bw_cex_ait:public summarizer_bw_cex_baset
{
public:
  summarizer_bw_cex_ait(
    optionst &_options,
    summary_dbt &_summary_db,
    ssa_dbt &_ssa_db,
    ssa_unwindert &_ssa_unwinder,
    ssa_inlinert &_ssa_inliner,
    function_namet _entry_function,
    function_namet _error_function):
    summarizer_bw_cex_baset(
      _options,
      _summary_db,
      _ssa_db,
      _ssa_unwinder,
      _ssa_inliner,
      _entry_function,
      _error_function)
  {
  }

  virtual void summarize(const function_namet &entry_function);
  virtual void summarize(const exprt &_error_assertion);

  virtual property_checkert::resultt check();

protected:
  virtual void compute_summary_rec(
    const function_namet &function_name,
    const summaryt::call_sitet &call_site,
    const exprt &postcondition,
    bool context_sensitive);

  virtual void inline_summaries(
    const function_namet &function_name,
    local_SSAt &SSA,
    const summaryt &old_summary,
    const exprt &postcondition,
    bool context_sensitive,
    bool sufficient);

  virtual void do_summary(
    const function_namet &function_name,
    const summaryt::call_sitet &call_site,
    local_SSAt &SSA,
    const summaryt &old_summary,
    summaryt &summary,
    const exprt &postcondition,
    bool context_sensitive);

  virtual exprt compute_calling_context2(
    const function_namet &function_name,
    local_SSAt &SSA,
    summaryt old_summary,
    local_SSAt::nodest::const_iterator n_it,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    const exprt &postcondition,
    bool sufficient);
};

#endif // CPROVER_2LS_SOLVER_SUMMARIZER_BW_CEX_AI_H
