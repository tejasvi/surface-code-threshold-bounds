import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4024 = true := by
  decide +kernel

theorem tot4024 : totK PA10K2 A10K2.t4024 = [0, 342520480111, 1572181225020, 2134942560170, 849358834898, 71812324790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4025 = true := by
  decide +kernel

theorem tot4025 : totK PA10K2 A10K2.t4025 = [0, 61758222684, 632446049742, 1904177671641, 1748249476943, 409264309395, 18429085292, 0, 0, 0] := by
  decide +kernel

theorem rows4026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4026 = true := by
  decide +kernel

theorem tot4026 : totK PA10K2 A10K2.t4026 = [0, 523990928391, 1892219072948, 1901529861221, 516601724447, 32149840254, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4027 = true := by
  decide +kernel

theorem tot4027 : totK PA10K2 A10K2.t4027 = [0, 172073925534, 1136118509238, 2133192646792, 1311180556213, 241248540269, 15167097304, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
