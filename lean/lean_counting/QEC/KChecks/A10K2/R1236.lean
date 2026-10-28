import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4944 = true := by
  decide +kernel

theorem tot4944 : totK PA10K2 A10K2.t4944 = [0, 0, 284439791004, 1529169444916, 2113131000658, 642492989577, 38673136708, 0, 0, 0] := by
  decide +kernel

theorem rows4945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4945 = true := by
  decide +kernel

theorem tot4945 : totK PA10K2 A10K2.t4945 = [0, 0, 232431983818, 1056475580083, 1966198992624, 1219172142316, 187669909920, 5685526223, 0, 0] := by
  decide +kernel

theorem rows4946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4946 = true := by
  decide +kernel

theorem tot4946 : totK PA10K2 A10K2.t4946 = [0, 110501856496, 531695456754, 1676155137867, 1982298989801, 659967904154, 51666332465, 0, 0, 0] := by
  decide +kernel

theorem rows4947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4947 = true := by
  decide +kernel

theorem tot4947 : totK PA10K2 A10K2.t4947 = [0, 445720234207, 1869336483109, 1956603690689, 475987522641, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
