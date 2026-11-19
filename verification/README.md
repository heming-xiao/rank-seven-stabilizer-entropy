# Reproduce the interval checks

Run the commands from the repository root. Use Python 3 and a C++20
compiler with signed 128-bit integer support. The verification scripts
read certificate data in [certificates/rank7/](../certificates/rank7/).

```sh
python verification/verify_rank7_tail_interval_union.py --require-complete
g++ -std=c++20 -O3 -o rank7_upper verification/verify_rank7_fourth_tie_bilinear.cpp
g++ -std=c++20 -O3 -o rank7_lower verification/verify_rank7_tied_fourth_lower_fifth.cpp
./rank7_upper 8 9 16
./rank7_lower 1 6
```

Use `.exe` for the executable names on Windows. The receipt checker verifies
the recorded central interval coverage and the frozen verifier hashes.
The two C++ commands regenerate interval traversals. The
[proof guide](../proof/rank7_submission_proof_guide.md) lists all bands,
the symbolic checks, and the remaining Python dependencies.
