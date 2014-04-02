/*
 * This file is part of the MIAMI framework. For copyright information, see
 * the LICENSE file in the MIAMI root folder. 
 */
/* 
 * File: mrd_histograms.C
 * Author: Gabriel Marin, mgabi99@gmail.com
 *
 * Outputs memory reuse histograms at scope level
 */

#include "MiamiDriver.h"
#include "miami_types.h"
#include "memory_reuse_histograms.h"
#include <algorithm>


namespace MIAMI {

static int 
processBinToVector(void* arg0, MIAMI_MEM_REUSE::dist_t key, void* value)
{
   MIAMI_MEM_REUSE::DCVector* histogram = static_cast<MIAMI_MEM_REUSE::DCVector*>(arg0);
   MIAMI_MEM_REUSE::count_t* pValue = (MIAMI_MEM_REUSE::count_t*)value;
   histogram->push_back(MIAMI_MEM_REUSE::DistCountPair(key, *pValue) );
   return 0;
}   

#define ABSOLUTE_BIN_LIMIT  0
#define RELATIVE_BIN_LIMIT  0.02f

static void 
dump_mrd_histograms_for_scope(FILE *fout, ScopeImplementation *pscope, bool use_stack,
              int idx, int nfiles)
{
   MIAMI_MEM_REUSE::HashMapCT *hist = 0;
   if (use_stack)
      hist = &(pscope->getStackHistogramForScope(idx, nfiles));
   else
      hist = &(pscope->getMrdHistogramForScope(idx, nfiles));
      
   if (hist && !hist->empty())
   {
      std::string sname = pscope->ToString();
      std::replace(sname.begin(), sname.end(), ',', ';');
      fprintf(fout, "%s", sname.c_str());
      
      // convert histograms to vectors, compute total counts and compress them
      MIAMI_MEM_REUSE::DCVector dcArray;
      hist->map(processBinToVector, &dcArray); 
      assert(! dcArray.empty());

      // The complete histogram of the scope must be in the dcArray array
      // Sort it and process it
      std::sort(dcArray.begin(), dcArray.end(), 
                         MIAMI_MEM_REUSE::DistCountPair::OrderAscByKey1());
      
      // compress the histogram: aggregating bins with close 
      // absolute or relative distances into one bin
      uint32_t crtBin = 0;
      MIAMI_MEM_REUSE::DCVector::iterator it = dcArray.begin();
      unsigned long long crtDistance = 0;
      MIAMI_MEM_REUSE::count_t crtCount = 0;
      MIAMI_MEM_REUSE::dist_t limit1 = it->first;
      MIAMI_MEM_REUSE::dist_t limit2 = 0;
      MIAMI_MEM_REUSE::count_t totalCount = 0;
      float crtAverage = it->first;
      MIAMI_MEM_REUSE::FloatArray distances;
      MIAMI_MEM_REUSE::CountArray counts;

      while (it != dcArray.end())
      {
         float difference = it->first - limit1;  // crtAverage;
         if (difference <= ABSOLUTE_BIN_LIMIT || 
                  (crtAverage>0 && difference/crtAverage <= RELATIVE_BIN_LIMIT))
         {
            crtDistance += ((unsigned long long)(it->first))*(it->second);
            crtCount += it->second;
            crtAverage = (float)crtDistance/crtCount;
            limit2 = it->first;
            ++ it;
         }
         else
         {
            if (crtCount>0)
            {
               crtBin ++;
               distances.push_back(crtAverage);
               counts.push_back(crtCount);
               totalCount += crtCount;
            }
            crtDistance = 0;
            crtCount = 0;
            crtAverage = (float)it->first;
            limit1 = it->first;
            limit2 = 0;
         }
      }
      if (crtCount > 0)  // there is data not accounted for
      {
         crtBin++;
         distances.push_back(crtAverage);
         counts.push_back(crtCount);
         totalCount += crtCount;
      }
      assert (crtBin==distances.size() && crtBin==counts.size());
      
      fprintf(fout, ", %" PRIcount ", %d\n", totalCount, crtBin);

      MIAMI_MEM_REUSE::FloatArray::iterator fit = distances.begin();
      int i = 0;
      for( ; fit!=distances.end() ; ++fit, ++i)
      {
         // round the floating point number to closest integer
         // May redeuce output file size
         MIAMI_MEM_REUSE::dist_t avgDist = (MIAMI_MEM_REUSE::dist_t)(*fit + .5);  // we know distances are >= 0
         if (i == 0)
            fprintf(fout, "%" PRIdist , avgDist);
         else
            fprintf(fout, ", %" PRIdist , avgDist);
      }
      if (i>0)
         fprintf(fout, "\n");

      MIAMI_MEM_REUSE::CountArray::iterator uit = counts.begin();
      i = 0;
      for( ; uit!=counts.end() ; ++uit, ++i)
      {
         // round the floating point number to closest integer
         // May redeuce output file size
         if (i == 0)
            fprintf(fout, "%" PRIcount , *uit);
         else
            fprintf(fout, ", %" PRIcount , *uit);
      }
      if (i>0)
         fprintf(fout, "\n");
   }
   
   ScopeImplementation::iterator sit;
   for (sit=pscope->begin() ; sit!=pscope->end() ; ++sit)
   {
      ScopeImplementation *sci = 
                dynamic_cast<ScopeImplementation*>(sit->second);
      dump_mrd_histograms_for_scope(fout, sci, use_stack, idx, nfiles);
   }
}

void 
MIAMI_Driver::dump_mrd_histograms(FILE *fout, ScopeImplementation *pscope, 
         bool use_stack, int idx, int nfiles)
{
   // We print one histogram for each scope. We use 3 lines per scope.
   // 1) Scope name, Total count, Num bins
   // 2) Distances for each bin, separated by commas
   // 3) Counts for each bin, separated by commas
   
   // Print an explanatory header first
   fprintf(fout, "# Scope, TotalCount, NumBins\n");
   fprintf(fout, "# Distances for each bin separated by commas\n");
   fprintf(fout, "# Counts for each bin separated by commas\n");
   
   dump_mrd_histograms_for_scope(fout, pscope, use_stack, idx, nfiles);
}


}  /* namespace MIAMI */

