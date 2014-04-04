/*
 * This file is part of the MIAMI framework. For copyright information, see
 * the LICENSE file in the MIAMI root folder.  
 */
/* 
 * File: routine.C
 * Author: Gabriel Marin, mgabi99@gmail.com
 *
 * Data bookkeeping and analysis at the routine level for a data reuse 
 * analysis tool. Extends the PrivateRoutine implementation with 
 * functionality specific to the data reuse tool.
 */

#include <assert.h>
#include <string.h>
#include "routine.h"

using namespace std;
using namespace MIAMI;

extern int MIAMI_MEM_REUSE::verbose_level;

#define DEBUG_BBLs 0

#if DEBUG_BBLs
const char *debugName = "__mempcpy";
#endif

Routine::Routine(LoadModule *_img, addrtype _start, usize_t _size, 
           const std::string& _name, addrtype _offset)
     : PrivateRoutine(_img, _start, _size, _name, _offset)
{
   g = new CFG(this, _name);
}

Routine::~Routine()
{
   if (g)
      delete g;
}

/* This method build the tarjan intervals for our graph, and performs several types 
 * of static analyses on the graph: build a scope tree, find edges that enter or exit
 * from loops. Optionally, perform data flow analysis on memory operands to understand
 * which ones access the stack and which ones are related.
 */
void
Routine::DetermineInstrumentationPoints(bool do_static_mem)
{
   if (! g)
   {
      fprintf(stderr, "ERROR: Routine::DetermineInstrumentationPoints: routine %s does not have a control flow graph yet?? Unacceptable.\n", 
              name.c_str());
      assert(!"No CFG for routine.");
      return;
   }
   
   MiamiRIFG mCfg(g);
   TarjanIntervals tarj(mCfg);
   RIFGNodeId root = mCfg.GetRootNode();
   if (MIAMI_MEM_REUSE::verbose_level > 1)
   {
      fprintf(stderr, ">> Routine::DetermineInstrumentationPoints: tarjan root node for routine %s, [0x%" 
          PRIxaddr ",0x%" PRIxaddr "], root=%d\n", 
               name.c_str(), start_addr, start_addr+size, root);
   }
   // I need to do a DFS traversal of the graph, and determine the places 
   // where I need to insert scope ENTRY/EXIT/ITER CHANGE/etc. events
   FindScopesRecursively(root, &tarj, &mCfg, 0);
   FindLoopEntryExitEdges(root, &tarj, &mCfg;
   
   if (do_static_mem)
      PerformStaticMemoryAnalysis(g, root, &tarj, &mCfg);
}

void
Routine::PerformStaticMemoryAnalysis(PrivateCFG *cfg, RIFGNodeId root, TarjanIntervals *tarj,
                   MiamiRIFG *mCfg)
{
   // declare the map as automatic variable; We are not going to preserve the 
   // formulas when we return. We'll have to save all the higher order information
   // once we return.
   RFormulasMap refFormulas;
   
   // build base location formulas first; use topological traversal of the CFG, 
   // so that when I analyze an instruction, all references on all paths to that 
   // instruction are already analyzed (have symbolic formulas)
   ReferenceSlice *rslice = 0;
   if (MIAMI_MEM_REUSE::verbose_level > 1)
   {
      fprintf(stderr, "Computing base formulas for routine %s \n", Name().c_str());
   }
   rslice = new ReferenceSlice(cfg, refFormulas);
   ComputeBaseFormulas(rslice, cfg, refFormulas);
   
   // build stride formulas now
   ComputeStrideFormulasForRoutine(root, tarj, mCfg, tarj->LoopIndex(root), 0, rslice);
   if (rslice) {
      delete (rslice);
      rslice = 0;
   }
   
   // We have the formulas in refFormulas. I must traverse all scopes and mark
   // references that are scalar stack accesses and references that are related.
}

//--------------------------------------------------------------------------------------------------------------------

void
//CFG::Node::record_scopeid_for_memory_references(LoadModule *img, uint32_t scopeId,
Routine::decode_memory_references_in_block(CFG::Node *node, AddrIntSet &memRefs)
{
   // I must traverse all the instructions in this block, and record the
   // scope Id for each one
   // I will use a BucketHashTable to store both the index and the scope ID
   // for a memory operand. We only record scopeIds right now.
   // Later, when we execute a trace, we will assign a unique index to
   // each memory operand. That way, I should have a more compact numbering 
   // scheme, i.e. fewer holes in my indices.
   MIAMI::DecodedInstruction dInst;
   LoadModule *img = InLoadModule();
   addrtype reloc = img->RelocationOffset();
/*
   fprintf(stderr, "record_scopeid: img=%d, reloc=0x%" PRIxaddr ", scopeId=%d, crt block [0x%" 
         PRIxaddr ",0x%" PRIxaddr "]\n", img->ImageID(), reloc, scopeId, 
         getStartAddress(), getEndAddress());
*/
   CFG::ForwardInstructionIterator iit(node);
   while ((bool)iit)
   {
      addrtype pc = iit.Address();
      int res = decode_instruction_at_pc((void*)(pc+reloc), node->getEndAddress()-pc, &dInst);
      if (res < 0)  // error while decoding
         return;
      if (pc+dInst.len <= node->getEndAddress())
      {
         // Now iterate over the micro-ops of the decoded instruction
         MIAMI::InstrList::iterator lit = dInst.micro_ops.begin();
         for (int i=0 ; lit!=dInst.micro_ops.end() ; ++lit, ++i)
         {
            MIAMI::instruction_info& iiobj = (*lit);
            if (InstrBinIsMemoryType(iiobj.type))
            {
               int opidx = iiobj.get_memory_operand_index();
               assert(opidx >= 0);
               memRefs.insert(AddrIntPair(pc, opidx));
            }
         }
      } else  // instruction extends beyond the block end, skip; this block must include the prefix
      {
//         fprintf(stderr, "Instruction at address 0x%" PRIxaddr " has length %d and extends beyond the block end. Skip.\n",
//              pc, dInst.len);
      }
      ++ iit;
   }
}


/*
 * Find scopes recursively. I want to give a unique ID (inside each Image)
 * to each program scope, routine or loop. I also want the identifying 
 * information to be repeatable for a given executable file.
 * Idea: We use two pieces of information to identify a scope:
 *  - starting address of the header node
 *  - scope level (routines are at level 0, loops are at levels 1, 2, ...)
 * There is a potential problem when dealing with Irreducible intervals, 
 * which do not have a unique loop header.
 *
 * Algorithm: 
 *  - Traverse each block
 *     - determine the scope ID of the block. For this, we need to find the
 *       loop header of this scope. Use Tarjan information. If block is 
 *       interval header, we have our guy. Otherwise, get the block's Outer 
 *       node. Get scope ID based on header address and level.
 *     - if block is call surrogate, add AFTER_CALL event before the next
 *       instruction after the call. Also, for every other edge flowing into
 *       the successor node (not MIAMI's fall-thru from the Call), add a 
 *       BR_TO_CALL event to detect flow that bypasses the call.
 *     - Traverse each edge incoming into the block
 *        - If Edge is BackEdge, we must add an ITER_CHANGE event along it.
 *          We must find the correct scope ID of this edge. Its source and
 *          sink must be either in the same scope, or they must be in an
 *          inner-outer relationship. Find the outer block, find its scope
 *          header, and find its Scope ID.
 *        - Next, check number of entered and exited scopes by this edge.
 *        - Add one EXIT_SCOPE event even if multiple loops are exited.
 *        - Add one ENTER_SCOPE event for each entered loop.
 *  - For most events we need the correct scope ID (see how to compute above),
 *    the edge on which we insert (end address of source block, and edge type).
 *  - For the AFTER_CALL event we need the address of the instruction after
 *    the call. It must always be the start of a TRACE.
 *
 * I will separate the scope discovery, including the handling of CALL 
 * instructions, from the handling of edges with respect to understanding 
 * loop entry/exit/back edges. I will do scope discovery first.
 * During scope discovery, I traverse scopes in pre-order, assigning them IDs
 * as I find them. When I discover loop entry/exit edges, I can generate scope
 * IDs in random order, because edges incoming into a block can enter multiple
 * loop levels, or exit from arbitrary loops.
 *
 * Because I already discover the scopes and decode all the instructions to 
 * identify memory operations, in the name of efficiency (we are doing this
 * things at runtime), I will piggyback on this routine to understand references
 * that are stack accesses and references that are related.
 */

void
Routine::FindScopesRecursively(RIFGNodeId root, TarjanIntervals *tarj, MiamiRIFG *ecfg,
        uint32_t parentId, RFormulasMap *pFormulas)
{
   RIFGNodeId kid;
   LoadModule *img = InLoadModule();
   uint32_t imgId = img->ImageID();
   AddrIntSet scopeMemRefs;
   
   // Do not insert ITER_CHANGE events for inner loops that do not
   // have function calls
   bool is_inner = true;
   
   Node *root_b = static_cast<Node*>(ecfg->GetRIFGNode (root));
   addrtype saddress = 0;
   int rlevel = 0;
   if (root_b->isCfgEntry())
      saddress = InRoutine()->Start();
   else
   {
      saddress = root_b->getStartAddress();
      rlevel = tarj->GetLevel(root);
   }
   uint32_t rootScopeId = img->getScopeIndex(saddress, rlevel);
   img->SetParentForScope(rootScopeId, parentId);

   if (MIAMI_MEM_REUSE::verbose_level > 1)
   {
      fprintf(stderr, "--> IMG %d, SCOPE %d : scope at address 0x%" PRIxaddr ", level %d\n", 
                imgId, rootScopeId, saddress, rlevel);
   }
   if (root_b->Size()>0)
      root_b->decode_memory_references_in_scope(img, scopeMemRefs);
   
   for (kid = tarj->TarjInners(root) ; kid != RIFG_NIL ; 
                kid = tarj->TarjNext(kid))
   {
      Node *b = static_cast<Node*>(ecfg->GetRIFGNode (kid));
      
      // If b is a call surrogate, I want to insert a routine EXIT event at 
      // IPOINT_BEFORE of the instruction after the call. Also, for any 
      // branches incoming into the successor block, I need to insert 
      // BR_TO_CALL events, to catch paths that bypass the call.
      // I instrument routine entry points to understand routine ENTRY events.
      // Instrumenting first instruction of a routine, do we bother with
      // other entry points for this tool??
      if (b->isCallSurrogate())
      {
         is_inner = false;
         Edge *outE = NULL;
         int succSize = b->num_outgoing();
         if (succSize)  // if it has successors, it can have only one
         {
            outE = static_cast<Edge*>(b->firstOutgoingOfType(CFG::MIAMI_FALLTHRU_EDGE));
//            assert (outE != 0);
         }
         if (outE && outE->sink()->isCodeNode())
         {
            // outE->sink() is the successor node
            Node *suc = outE->sink();
#if DEBUG_SCOPE_DETECTION
            if (MIAMI_MEM_REUSE::verbose_level > 1)
            {
               fprintf(stderr, "Found call surrogate at 0x%" PRIxaddr ", block after call starts at 0x%" PRIxaddr ", rootScopeId=%d\n",
                      b->getStartAddress(), suc->getStartAddress(), rootScopeId);
            }
#endif
            ListOfEvents* &bList = img->bblEvents[suc->getStartAddress()];
            if (! bList)
               bList = new ListOfEvents();
            bList->push_back(MIAMI_MEM_REUSE::ScopeEventRecord(rootScopeId, imgId,
                MIAMI_MEM_REUSE::MEMREUSE_EVTYPE_AFTER_CALL));
                
            IncomingEdgesIterator iei(suc);
            while ((bool)iei)
            {
               Edge *iE = (Edge*)iei;
               // mark edges other than the call's fall-thru edge
               if (iE != outE)
               {
                  // this cannot be a fall-thru edge
                  EdgeType etype = iE->getType();
#if DEBUG_SCOPE_DETECTION
                  if (MIAMI_MEM_REUSE::verbose_level > 1)
                  {
                     fprintf(stderr, "Found EDGE of type %d from block [0x%" PRIxaddr ",0x%" PRIxaddr 
                              "] to block [0x%" PRIxaddr ",0x%" PRIxaddr "]\n", 
                              etype, 
                              iE->source()->getStartAddress(), iE->source()->getEndAddress(),
                              suc->getStartAddress(), suc->getEndAddress());
                  }
#endif
                  if (etype!=MIAMI_DIRECT_BRANCH_EDGE &&
                         etype!=MIAMI_INDIRECT_BRANCH_EDGE)
                  {
                     fprintf(stderr, "Found EDGE of type %d going to block [0x%" PRIxaddr ",0x%" PRIxaddr "]\n", 
                              etype, suc->getStartAddress(), suc->getEndAddress());
                     assert (etype==MIAMI_DIRECT_BRANCH_EDGE ||
                            etype==MIAMI_INDIRECT_BRANCH_EDGE);
                  }
                  // iE->source() is the preceding block
                  ListOfEvents* &eList = img->edgeEvents[iE->source()->getEndAddress()];
                  if (! eList)
                     eList = new ListOfEvents();
                  // pass the edge type in the aux field. Indirect jumps are not always accurate.
                  eList->push_back(MIAMI_MEM_REUSE::ScopeEventRecord(rootScopeId, imgId,
                      MIAMI_MEM_REUSE::MEMREUSE_EVTYPE_BR_BYPASS_CALL, 1, etype));
                  // I want to always insert last the BR_BYPASS_CALL events on an edge !!!
               }
               ++ iei;
            }
         }
      }  // b is CallSurrogate

      if (tarj->NodeIsLoopHeader(kid))
      {
         is_inner = false;
         FindScopesRecursively (kid, tarj, ecfg, img, rootScopeId, pFormulas);
      } else
      {
         if (b->Size()>0)
            b->decode_memory_references_in_scope(img, scopeMemRefs);
//            b->record_scopeid_for_memory_references(img, rootScopeId, scopeMemRefs);
      }
   }
   
   long sz = img->scopeIsInner.size();
   if (sz <= rootScopeId)
   {
      do {
         sz <<= 1;
      } while (sz <= rootScopeId);
      img->scopeIsInner.resize(sz);
   }
   img->scopeIsInner[rootScopeId] = is_inner;
   
   AddrIntSet::iterator ais = scopeMemRefs.begin();
   for ( ; ais!=scopeMemRefs.end() ; ++ais)
   {
      // assign the scope ID for all references in this scope
      img->setScopeIdForReference(ais->first, ais->second, rootScopeId);
      
      // for each memory reference, track which ones are scalar stack accesses
      // for the others, try to group them into related sets
      
   }
}


void
Routine::FindLoopEntryExitEdges(RIFGNodeId root, TarjanIntervals *tarj, MiamiRIFG *ecfg)
{
   uint32_t imgId = img->ImageID();
   
   // I just need to iterate over all the edges in the graph. I do not even 
   // need a recursive function
   MiamiAllEdgesIterator eit(ecfg);
   RIFGEdgeId inEdge;
   for (inEdge = eit.Current(); inEdge != RIFG_NIL; inEdge = eit++)
   {
      Edge* e = static_cast<Edge*>(ecfg->GetRIFGEdge(inEdge));
      EdgeType etype = e->getType();
      if (etype==MIAMI_CFG_EDGE || etype==MIAMI_BYPASS_EDGE || etype==MIAMI_RETURN_EDGE)
         continue;
         
      Node* b = e->sink();
      RIFGNodeId kid = ecfg->GetEdgeSink(inEdge);
      if (etype!=MIAMI_DIRECT_BRANCH_EDGE &&
             etype!=MIAMI_INDIRECT_BRANCH_EDGE &&
             etype!=MIAMI_FALLTHRU_EDGE)
      {
         fprintf(stderr, "Found EDGE of type %d going to block [0x%" PRIxaddr ",0x%" PRIxaddr "]\n", 
                  etype, b->getStartAddress(), b->getEndAddress());
         assert (etype==MIAMI_DIRECT_BRANCH_EDGE ||
                 etype==MIAMI_INDIRECT_BRANCH_EDGE ||
                 etype==MIAMI_FALLTHRU_EDGE);
      }
      
      Node* srcN = e->source();
      RIFGNodeId src = ecfg->GetEdgeSrc(inEdge);
      int lEnter = 0, lExit = 0;   // store number of levels crossed
      tarj->tarj_entries_exits (src, kid, lEnter, lExit);
#if DEBUG_SCOPE_DETECTION
      if (MIAMI_MEM_REUSE::verbose_level>1 && (lEnter || lExit))
      {
         cerr << "Edge E " << e->getId() << " of type " << etype 
              << " from  b " << srcN->getId() 
              << " to b " << b->getId() << " enters "
              << lEnter << " loops and exits " << lExit << " loops." << endl;
      }
#endif
      // Process the SCOPE EXIT events first
      if (lExit > 0) // it is a loop exit edge
      {
         // get the outermost loop exited using the tarjans
         RIFGNodeId lhead = tarj->tarj_loop_exited (src, kid);
         assert (lhead != RIFG_NIL);
         assert (tarj->numExitEdges (lhead) > 0);
         // add SCOPE_EXIT event on e (e->source(), e->getType())
         // specifying also the number of levels exited, lExit.
         Node* btemp = static_cast<Node*>(ecfg->GetRIFGNode (lhead));
         // I need to find the level of the outermost loop exited.
         // We could check the level of the header node, but a node can
         // be a header for multiple loops. However, we know that the
         // edge from src to kid exited lExit levels. 'src' must have 
         // been part of the innermost loop exited. Use this insight
         // to compute the level.
         int llevel = tarj->GetLevel(src) - lExit + 1;
         assert(llevel > 0);  // it should not be a routine body
         uint32_t scopeId = img->getScopeIndex(btemp->getStartAddress(), llevel);
         
         ListOfEvents* &eList = img->edgeEvents[srcN->getEndAddress()];
         if (! eList)
            eList = new ListOfEvents();
         eList->push_back(MIAMI_MEM_REUSE::ScopeEventRecord(scopeId, imgId,
             MIAMI_MEM_REUSE::MEMREUSE_EVTYPE_EXIT_SCOPE, 
             etype!=MIAMI_FALLTHRU_EDGE, lExit));
#if DEBUG_SCOPE_DETECTION
         if (MIAMI_MEM_REUSE::verbose_level > 1)
         {
            fprintf (stderr, "Record EXIT edge for Loop %d, Level exited %d/%d, Img %d, header at PC 0x%" 
                 PRIxaddr ", edge starts at 0x%" PRIxaddr "\n",
                  scopeId, llevel, lExit, imgId, btemp->getStartAddress(), srcN->getEndAddress());
         }
#endif
      }
      
      // Now process any ITERATION CHANGE events
      if (tarj->IsBackEdge(inEdge))
      {
         // e is the loop back edge; I need to add an ITER_CHANGE event
         // Find the loop for which this edge is a back edge
         RIFGNodeId loop_node = ecfg->GetEdgeSrc(inEdge);
         RIFGNodeId sink_node = ecfg->GetEdgeSink(inEdge);
         if (tarj->LoopIndex(loop_node) > tarj->LoopIndex(sink_node))
            loop_node = sink_node;
         int llevel = tarj->GetLevel(loop_node);
         assert(llevel > 0);  // it should not be a routine body
         
         // Now we need to find the header of the loop
         if (! tarj->NodeIsLoopHeader(loop_node))
            loop_node = tarj->TarjOuter(loop_node);
         Node* btemp = static_cast<Node*>(ecfg->GetRIFGNode (loop_node));
         uint32_t scopeId = img->getScopeIndex(btemp->getStartAddress(), llevel);
         
         ListOfEvents* &eList = img->edgeEvents[srcN->getEndAddress()];
         if (! eList)
            eList = new ListOfEvents();
         eList->push_back(MIAMI_MEM_REUSE::ScopeEventRecord(scopeId, imgId,
             MIAMI_MEM_REUSE::MEMREUSE_EVTYPE_ITER_CHANGE, 
             etype!=MIAMI_FALLTHRU_EDGE));
#if DEBUG_SCOPE_DETECTION
         if (MIAMI_MEM_REUSE::verbose_level > 1)
         {
            cerr << "FindScopesRecursively: Edge from b " << srcN->getId() 
                 << " [" << hex << srcN->getStartAddress() << "," 
                 << srcN->getEndAddress() << dec << "] to b " 
                 << b->getId() << " [" << hex << b->getStartAddress()
                 << "," << b->getEndAddress() << "] is backedge for Scope " 
                 << dec << scopeId << ", in IMG " << imgId << endl;
         }
#endif
      }
      
      // Finally, add any eventual SCOPE ENTRY events
      if (lEnter > 0)  // it is a loop entry edge
      {
         // get the outermost loop entered using the tarjans
         // I only use lhead for the assert after the loop iterating
         // over all the levels
         RIFGNodeId lhead = tarj->tarj_loop_entered (src, kid);
         assert (lhead != RIFG_NIL);

         // We know that kid is part of the innermost scope. Iteratively,
         // I am going to find each successive outer scope. However, I want
         // to record the ENTRY events in logical order, from outermost to
         // innermost.
         int llevel = tarj->GetLevel(kid);
         assert(llevel >= lEnter);  // it should not be a routine body
         
         RIFGNodeId ikid = kid;
         if (! tarj->NodeIsLoopHeader(kid))
            ikid = tarj->TarjOuter(kid);

         ListOfEvents* &eList = img->edgeEvents[srcN->getEndAddress()];
         if (! eList)
            eList = new ListOfEvents();
         ListOfEvents::iterator eiter = eList->end();
         
         for(int k=1 ; k<=lEnter ; ++k, --llevel)
         {
            assert (ikid != RIFG_NIL);
            Node* btemp = static_cast<Node*>(ecfg->GetRIFGNode (ikid));
            addrtype loopStart = btemp->getStartAddress();
            uint32_t scopeId = img->getScopeIndex(loopStart, llevel);
            
#if DEBUG_SCOPE_DETECTION
            if (MIAMI_MEM_REUSE::verbose_level > 1)
            {
               fprintf (stderr, "Record entry edge for Loop %d, Level entered %d/%d, Img %d, starting at 0x%" 
                   PRIxaddr ", edge starts at 0x%" PRIxaddr "\n",
                     scopeId, llevel, lEnter,imgId, loopStart, srcN->getEndAddress());
            }
#endif
            // save ENTER_SCOPE event for this edge, TODO
            // I must insert them in reverse order
            eiter = eList->insert(eiter, 
                  MIAMI_MEM_REUSE::ScopeEventRecord(scopeId, imgId,
                  MIAMI_MEM_REUSE::MEMREUSE_EVTYPE_ENTER_SCOPE, 
                  etype!=MIAMI_FALLTHRU_EDGE));
            
            if (k<lEnter)
               ikid = tarj->TarjOuter(ikid);
         }
         // at the end I should get the outermost scope entered by the edge
         // which we found before
         assert (ikid == lhead);
      }
   }
}
