// This unit includes Dogecoin Core's src/validation.cpp and src/timedata.cpp
// as text. The compiler sees Core's code unchanged, and the functions below
// can name what those files keep internal: the static AcceptBlockHeader, the
// sets gFailedBlocks and setDirtyBlockIndex of the anonymous namespace, and
// the static nTimeOffset. The link takes neither file from Core's server
// library, because this unit defines every symbol of both.
//
// The functions below contain no validation logic. core_oracle.cpp calls them.
#include "validation.cpp"
#include "timedata.cpp"

#include "core_validation.h"

bool harnessAcceptBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex** ppindex)
{
    LOCK(cs_main);
    return AcceptBlockHeader(block, state, Params(), ppindex);
}

void harnessAddFailedBlock(CBlockIndex* entry)
{
    LOCK(cs_main);
    gFailedBlocks.insert(entry);
}

std::vector<CBlockIndex*> harnessTakeDirtyBlockIndex()
{
    LOCK(cs_main);
    std::vector<CBlockIndex*> entries(setDirtyBlockIndex.begin(), setDirtyBlockIndex.end());
    setDirtyBlockIndex.clear();
    return entries;
}

// GetAdjustedTime returns GetTime() plus nTimeOffset, and GetTime() returns the
// mock time unless that is 0 (utiltime.cpp). Mock time 0 would select the
// system clock, so 0 is the sum of mock time 1 and offset -1.
void harnessSetAdjustedTime(int64_t adjusted)
{
    LOCK(cs_nTimeOffset);
    if (adjusted == 0) {
        SetMockTime(1);
        nTimeOffset = -1;
    } else {
        SetMockTime(adjusted);
        nTimeOffset = 0;
    }
}

void harnessResetAdjustedTime()
{
    LOCK(cs_nTimeOffset);
    SetMockTime(0);
    nTimeOffset = 0;
}
