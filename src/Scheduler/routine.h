/*
 * This file is part of the MIAMI framework. For copyright information, see
 * the LICENSE file in the MIAMI root folder.
 */
/* 
 * File: routine.h
 * Author: Gabriel Marin, mgabi99@gmail.com
 *
 * Description: Data bookkeeping and analysis at the routine level for the
 * MIAMI scheduler. Extends the PrivateRoutine implementation with 
 * functionality specific to the MIAMI post-processing tool.
 */

#ifndef MIAMI_SCHEDULER_ROUTINE_H
#define MIAMI_SCHEDULER_ROUTINE_H

#include <list>
#include <string>
#include "CFG.h"
#include "private_routine.h"
#include "load_module.h"
#include "prog_scope.h"
#include "slice_references.h"
#include "hashmaps.h"
#include "static_memory_analysis.h"
#include "miami_options.h"
#include "miami_containers.h"
#include "instruction_class.h"

namespace MIAMI
{
typedef std::list<std::string> StringList;
typedef std::map<AddrIntPair, InstructionClass, AddrIntPair::OrderPairs> RefIClassMap;

class ScopeImplementation;

class RefStrideId
{
public:
   RefStrideId(addrtype _pc, int _idx, int _lev) :
       pc(_pc), opidx(_idx), level(_lev)
   { 
      visited = 0;
   }
   
   addrtype pc;
   int opidx;
   int level;
   int visited;
};

typedef std::map<AddrIntPair, RefStrideId, AddrIntPair::OrderPairs> RefInfoMap;



class Routine : public PrivateRoutine
{
public:
   Routine(LoadModule *_img, addrtype _start, usize_t _size, 
         const std::string& _name, addrtype _offset, addrtype _reloc);
   virtual ~Routine();
   
   int loadCFGFromFile(FILE *fd);
   CFG* ControlFlowGraph() const { return (static_cast<CFG*>(g)); }
   
   // main analysis function. Compute BB/edge counts, reconstruct executed paths,
   // compute schedule for paths.
   int main_analysis(ImageScope *img, const MiamiOptions *mo);
   LoadModule* InLoadModule() const;
   
   // check if routine should be analyzed
   bool is_valid_for_analysis();
   static int parse_include_exclude_files(const std::string& _include, const std::string& _exclude);

   RFormulasMap& getRefFormulas() {
      return (*rFormulas); 
   }
   
   uint64_t SaveStaticData(FILE *fd);
   void FetchStaticData(FILE *fd, uint64_t offset);
   
private:
   bool IsScalarStackReference(addrtype pc, int memop);
   
   const char * ComputeObjectNameForRef(addrtype pc, int32_t memop);

   int build_paths_for_interval(ScopeImplementation *pscope, RIFGNodeId node, 
           TarjanIntervals *tarj, MiamiRIFG* mCfg, int marker, int level, 
           int no_fpga_acc, CFG::AddrEdgeMMap *entryEdges, CFG::AddrEdgeMMap *callEntryEdges);

   void constructPaths(ScopeImplementation *pscope, CFG::Node *b, int marker,
            int no_fpga_acc, CFG::AddrEdgeMMap *entryEdges, CFG::AddrEdgeMMap *callEntryEdges);

   CFG::NodeList::iterator addBlock(ScopeImplementation *pscope, CFG::Node *pentry, 
           CFG::Node *thisb, CFG::Edge *lastE, CFG::NodeList& ba, CFG::EdgeList &ea, 
           RSIListList &rl, int marker, BPMap *bpm, int64_t& iCount);

   void compute_lineinfo_for_block(ScopeImplementation *pscope, CFG::Node* b);
   void decode_instructions_for_block (ScopeImplementation *pscope, CFG::Node *b, int64_t count,
           AddrIntSet& memRefs, RefIClassMap& refsClass);

   void computeBaseFormulas(ReferenceSlice *rslice, CFG *g, RFormulasMap& refFormulas);
   
   void computeStrideFormulasForRoutine(RIFGNodeId node, TarjanIntervals *tarj, 
            MiamiRIFG* mCfg, int marker, int level, ReferenceSlice *rslice);
   void computeStrideFormulasForScope(StrideSlice &sslice, ReferenceSlice *rslice, 
               RIFGNodeId node, TarjanIntervals *tarj, MiamiRIFG* mCfg, int level,
               RFormulasMap& refFormulas, RefInfoMap& memRefs);

   bool clarifyIndirectAccessForRef(RefStrideId& rsi, GFSliceVal& _formula, 
               RFormulasMap& refFormulas, RefInfoMap& memRefs);

   static StringList includePatterns, excludePatterns;
   addrtype reloc_offset;
   
   const MiamiOptions *mo;

   // store symbolic formulas associated with each memory instruction
   RFormulasMap *rFormulas;
   
   // use two bitflags to compute and cache if the routine is valid
   // for analysis
   char valid_for_analysis : 1;
   char validity_computed : 1;
};


};

#endif
