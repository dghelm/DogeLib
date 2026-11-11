// Entry points of core_validation.cpp, the unit that includes Dogecoin Core's
// src/validation.cpp and src/timedata.cpp as text.
#ifndef DOGELIB_HARNESS_CORE_VALIDATION_H
#define DOGELIB_HARNESS_CORE_VALIDATION_H

#include "chain.h"
#include "consensus/validation.h"
#include "primitives/block.h"

#include <cstdint>
#include <vector>

// Call Core's static AcceptBlockHeader (validation.cpp) on the selected
// network's parameters, with cs_main held.
bool harnessAcceptBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex** ppindex);

// Insert an entry into Core's gFailedBlocks (validation.cpp).
void harnessAddFailedBlock(CBlockIndex* entry);

// Return the members of Core's setDirtyBlockIndex (validation.cpp), and clear it.
std::vector<CBlockIndex*> harnessTakeDirtyBlockIndex();

// Make Core's GetAdjustedTime (timedata.cpp) return `adjusted`.
void harnessSetAdjustedTime(int64_t adjusted);

// Restore Core's initial mock time and time offset, which are both 0.
void harnessResetAdjustedTime();

#endif
