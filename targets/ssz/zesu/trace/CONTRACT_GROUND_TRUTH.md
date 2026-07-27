# Contract ground truth — per function instance

GENERATED. Regenerate with

```
lake env lean tools/emit_ground_truth_report.lean \
  > targets/ssz/zesu/trace/CONTRACT_GROUND_TRUTH.md
```

This is **falsification evidence about the pinned artifact**, never a proof premise. Every
number below is computed by a definition that a `native_decide` theorem in the same module also
pins to an exact value, so this file cannot drift from the kernel-checked constants without
`lake build BinaryFv.SSZ.Zesu.Validation.BoundarySatisfiability` failing.

A `gap` is never a pass. It means the row was not decided, and the reason is printed with it.

## 1. Static boundary satisfiability — 141 function instances

Decided from `generatedProgram` alone; no run is involved. A `FAIL` here means the named
structure field has no witness, so the corresponding trace step cannot be taken at all.

```
idx | routineTag             | entry  | entryNotExit                       | callNotExit                | inline entries                   | inline exits                   | offending call pcs | children w/o exit edge
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
0   | rawAlloc               | 66124  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
1   | zesuDecodeRaw          | 66224  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 66288,66312
2   | allocatorCtor          | 66288  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
3   | decode                 | 66312  | ok                                 | FAIL CallTransfer.callNotExit | ok                               | FAIL InlineTransfer.exitEdgeMem | 66360 | 66448
4   | hasExactErePrefix      | 66448  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
5   | allocatorFree          | 66624  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
6   | decodeRaw              | 66628  | ok                                 | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 66692,66868,66884,66920,66976,67084,75536,76108,77500
7   | requireU32Length       | 66692  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
8   | readOffset             | 66868  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 66868
9   | readU32                | 66868  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
10  | readOffset             | 66884  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 66884
11  | readU32                | 66884  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
12  | readOffset             | 66920  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 66920
13  | readU32                | 66920  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
14  | readOffset             | 66976  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 66976
15  | readU32                | 66976  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
16  | newPayloadRequest      | 67084  | ok                                 | FAIL CallTransfer.callNotExit | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | 75508 | 67140,67156,67212,67352,73444,73688,73716
17  | readOffset             | 67140  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67140
18  | readU32                | 67140  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
19  | readOffset             | 67156  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67156
20  | readU32                | 67156  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
21  | readOffset             | 67212  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67212
22  | readU32                | 67212  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
23  | executionPayload       | 67352  | ok                                 | FAIL CallTransfer.callNotExit | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | 73048,73076,73104,73132 | 67428,67444,67480,67536,67684,67960,68252,68604,69564,69588,69836,70304,70416,70548,70632,70696,71012,72560,72748,72884
24  | readOffset             | 67428  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67428
25  | readU32                | 67428  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
26  | readOffset             | 67444  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67444
27  | readU32                | 67444  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
28  | readOffset             | 67480  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67480
29  | readU32                | 67480  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
30  | readOffset             | 67536  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 67536
31  | readU32                | 67536  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
32  | readArray              | 67684  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
33  | readArray              | 67960  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
34  | readArray              | 68252  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
35  | readArray              | 68604  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
36  | bytesAt                | 69564  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
37  | readArray              | 69564  | ok                                 | FAIL CallTransfer.callNotExit | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | 69584 | 69564
38  | readArray              | 69588  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
39  | readArray              | 69836  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
40  | readU64                | 70304  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
41  | readU64                | 70416  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
42  | readU64                | 70548  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
43  | readU64                | 70632  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
44  | readU256               | 70696  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
45  | withdrawals            | 71012  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 72132,72232,72332,72372
46  | bytesAt                | 72132  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
47  | readU64                | 72132  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 72132
48  | bytesAt                | 72232  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
49  | readU64                | 72232  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 72232
50  | bytesAt                | 72332  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
51  | readArray              | 72332  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 72332
52  | bytesAt                | 72372  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
53  | readU64                | 72372  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 72372
54  | bytesAt                | 72560  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
55  | readU64                | 72560  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 72560
56  | readU64                | 72748  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
57  | readU64                | 72884  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
58  | versionedHashes        | 73444  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 73620
59  | bytesAt                | 73620  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
60  | readArray              | 73620  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 73620
61  | bytesAt                | 73688  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
62  | readArray              | 73688  | FAIL EnteredScopedTrace.entryNotExit | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 73688
63  | executionRequests      | 73716  | ok                                 | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 73880,73904,73952,74072,74656,75072
64  | readOffset             | 73880  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 73880
65  | readU32                | 73880  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
66  | readOffset             | 73904  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 73904
67  | readU32                | 73904  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
68  | readOffset             | 73952  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 73952
69  | readU32                | 73952  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
70  | depositRequests        | 74072  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 74300,74344,74376,74472,74508
71  | bytesAt                | 74300  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
72  | readArray              | 74300  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74300
73  | bytesAt                | 74344  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
74  | readArray              | 74344  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74344
75  | bytesAt                | 74376  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
76  | readU64                | 74376  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74376
77  | bytesAt                | 74472  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
78  | readArray              | 74472  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74472
79  | bytesAt                | 74508  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
80  | readU64                | 74508  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74508
81  | withdrawalRequests     | 74656  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 74888,74920,74948
82  | bytesAt                | 74888  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
83  | readArray              | 74888  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74888
84  | bytesAt                | 74920  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
85  | readArray              | 74920  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74920
86  | bytesAt                | 74948  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
87  | readU64                | 74948  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 74948
88  | consolidationRequests  | 75072  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 75336,75372,75400
89  | bytesAt                | 75336  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
90  | readArray              | 75336  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75336
91  | bytesAt                | 75372  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
92  | readArray              | 75372  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75372
93  | bytesAt                | 75400  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
94  | readArray              | 75400  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75400
95  | executionWitness       | 75536  | ok                                 | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75680,75696,75752
96  | readOffset             | 75680  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75680
97  | readU32                | 75680  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
98  | readOffset             | 75696  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75696
99  | readU32                | 75696  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
100 | readOffset             | 75752  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 75752
101 | readU32                | 75752  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
102 | chainConfig            | 76108  | FAIL EnteredScopedTrace.entryNotExit | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76124,76224
103 | readOffset             | 76124  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76124
104 | readU32                | 76124  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
105 | forkConfig             | 76224  | FAIL EnteredScopedTrace.entryNotExit | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76316,76340,76480,76592,76888
106 | readOffset             | 76316  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76316
107 | readU32                | 76316  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
108 | readOffset             | 76340  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76340
109 | readU32                | 76340  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
110 | readU64                | 76480  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
111 | forkActivation         | 76592  | FAIL EnteredScopedTrace.entryNotExit | ok                         | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76600,76636
112 | readOffset             | 76600  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76600
113 | readU32                | 76600  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
114 | readOffset             | 76636  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76636
115 | readU32                | 76636  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
116 | optionalBlobSchedule   | 76888  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 76988,77020,77120
117 | readU64                | 76988  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
118 | readU64                | 77020  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
119 | readU64                | 77120  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
120 | publicKeys             | 77500  | FAIL EnteredScopedTrace.entryNotExit | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 77672
121 | bytesAt                | 77672  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
122 | readArray              | 77672  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 77672
123 | allocatorRemap         | 77872  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
124 | optionalU64            | 78136  | ok                                 | gap(no resolved call site) | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 78164
125 | readU64                | 78164  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
126 | byteListList           | 78496  | ok                                 | ok                         | ok                               | FAIL InlineTransfer.exitEdgeMem | - | 78560,78868,78904
127 | requireU32Length       | 78560  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
128 | bytesAt                | 78868  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
129 | readOffset             | 78868  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 78868
130 | readU32                | 78868  | FAIL EnteredScopedTrace.entryNotExit | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 78868
131 | bytesAt                | 78904  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
132 | readOffset             | 78904  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 78904
133 | readU32                | 78904  | ok                                 | gap(no resolved call site) | FAIL InlineBoundary.validFor(entries) | FAIL InlineTransfer.exitEdgeMem | - | 78904
134 | requireCanonicalOffsets | 79648  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
135 | allocatorResize        | 79712  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
136 | allocatorAlloc         | 79720  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
137 | rawError               | 79744  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
138 | rawResult              | 79756  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
139 | memcpy                 | 81592  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
140 | memmove                | 81628  | ok                                 | gap(no resolved call site) | gap(no inlined child)            | gap(no inlined child)          | - | -
```

totals (ok / violated / gap):
```
  entryNotExit    : 108 / 33 / 0
  callNotExit     : 15 / 4 / 122
  inline entries  : 10 / 55 / 76
  inline exits    : 0 / 65 / 76

inline PAIRS (parent,child), not instances:
  pairs                        : 127
  unresolved child identities  : 0
  entry edge inhabited         : 45
  exit  edge inhabited         : 0
  exit  edge inhabited IF the child's own edges counted (mutant, not a valid boundary): 56
```

