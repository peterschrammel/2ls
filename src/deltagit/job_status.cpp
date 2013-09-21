/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>

#include <util/xml.h>
#include <util/cout_message.h>

#include <xmllang/xml_parser.h>

#include "git_log.h"
#include "job_status.h"

/*******************************************************************\

Function: job_statust::next_stage

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::next_stage()
{
  assert(stage!=DONE);
  stage=(staget)((int)stage+1);
  status=WAITING;
}

/*******************************************************************\

Function: job_statust::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::read()
{
  xmlt src;
  
  console_message_handlert message_handler;
      
  if(parse_xml(id+".status", message_handler, src))
  {
    // assume it's new
    clear();
    return;
  }

  if(src.name!="deltagit_jobstatus")
    throw std::string("unexpected XML for job status");

  const std::string stage_string=src.get_attribute("stage");
  
  if(stage_string=="init")
    stage=INIT;
  else if(stage_string=="check out")
    stage=CHECK_OUT;
  else if(stage_string=="build")
    stage=BUILD;
  else if(stage_string=="analyse")
    stage=ANALYSE;
  else if(stage_string=="done")
    stage=DONE;
  else
    throw std::string("unexpected stage");

  const std::string status_string=src.get_attribute("status");
  
  if(status_string=="waiting")
    status=WAITING;
  else if(status_string=="running")
    status=RUNNING;
  else if(status_string=="failure")
    status=FAILURE;
  else if(status_string=="completed")
    status=COMPLETED;
  else
    throw std::string("unexpected status");

  added=atol(src.get_attribute("added").c_str());
  deleted=atol(src.get_attribute("deleted").c_str());
  message=src.get_element("message");
  author=src.get_attribute("author");
  date=src.get_attribute("date");
}

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_string(job_statust::staget stage)
{
  switch(stage)
  {
  case job_statust::INIT: return "init";
  case job_statust::CHECK_OUT: return "check out";
  case job_statust::BUILD: return "build";
  case job_statust::ANALYSE: return "analyse";
  case job_statust::DONE: return "done";
  default: return "";
  }
}

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_string(job_statust::statust status)
{
  switch(status)
  {
  case job_statust::WAITING: return "waiting";
  case job_statust::RUNNING: return "running";
  case job_statust::FAILURE: return "failure";
  case job_statust::COMPLETED: return "completed";
  default: return "";
  }
}

/*******************************************************************\

Function: job_statust::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void job_statust::write()
{
  xmlt xml;
  xml.name="deltagit_jobstatus";

  xml.set_attribute("id", id);
  xml.set_attribute("status", as_string(status));
  xml.set_attribute("stage", as_string(stage));
  xml.set_attribute("commit", commit);
  xml.set_attribute("added", added);
  xml.set_attribute("deleted", deleted);
  xml.set_attribute("author", author);
  xml.set_attribute("date", date);
  xml.new_element("message").data=message;
  
  std::ofstream out((id+".status").c_str());
  out << xml;
}

/*******************************************************************\

Function: get_extension

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_extension(const std::string &s)
{
  std::size_t pos=s.rfind('.');
  if(pos==std::string::npos) return "";
  return s.substr(pos+1, std::string::npos);
}

/*******************************************************************\

Function: get_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_file(const std::string &s)
{
  std::size_t pos=s.rfind('/');
  if(pos==std::string::npos) return s;
  return s.substr(pos+1, std::string::npos);
}

/*******************************************************************\

Function: get_jobs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_jobs(std::list<job_statust> &jobs)
{
  // get the git log
  git_logt git_log;
  
  // rummage through it, looking for 'interesting' commits
  // we reverse, to start with older commits
  for(git_logt::entriest::const_reverse_iterator
      l_it=git_log.entries.rbegin();
      l_it!=git_log.entries.rend();
      l_it++)
  {
    bool found=false;
  
    for(std::list<std::string>::const_iterator
        f_it=l_it->files.begin();
        f_it!=l_it->files.end();
        f_it++)
    {
      std::string file=get_file(*f_it);
      std::string ext=get_extension(file);

      if(ext=="c" || ext=="C" ||
         ext=="cpp" || ext=="c++" ||
         ext=="h" || ext=="hpp")
      {
        found=true;
        break;
      }    
    }

    if(found)
    {
      std::string id;

      if(l_it->git_svn_id!="")
        id="r"+l_it->git_svn_id;
      else
        id=l_it->commit;
      
      job_statust job_status(id);
      job_status.commit=l_it->commit;
      
      jobs.push_back(job_status);
    }
  }
}