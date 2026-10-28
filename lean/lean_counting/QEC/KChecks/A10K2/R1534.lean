import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6136 = true := by
  decide +kernel

theorem tot6136 : totK PA10K2 A10K2.t6136 = [0, 193399754571, 1224499641235, 2209061671529, 1218039216585, 137452897746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6137 = true := by
  decide +kernel

theorem tot6137 : totK PA10K2 A10K2.t6137 = [0, 106702756468, 743739074713, 1856075007147, 1637544336167, 454833234215, 30810868011, 0, 0, 0] := by
  decide +kernel

theorem rows6138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6138 = true := by
  decide +kernel

theorem tot6138 : totK PA10K2 A10K2.t6138 = [0, 405650716229, 1743592545801, 2226118956212, 802260464117, 58501650225, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6139 = true := by
  decide +kernel

theorem tot6139 : totK PA10K2 A10K2.t6139 = [0, 287992640199, 1257462991304, 1997643672283, 1344309478704, 252705777181, 7380853412, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
