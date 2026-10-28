import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5204 = true := by
  decide +kernel

theorem tot5204 : totK PA10K2 A10K2.t5204 = [0, 0, 162737336521, 1354399880761, 2211882954880, 819111187569, 58503570348, 0, 0, 0] := by
  decide +kernel

theorem rows5205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5205 = true := by
  decide +kernel

theorem tot5205 : totK PA10K2 A10K2.t5205 = [0, 310758541238, 1025012435302, 1180564813813, 1115006844952, 861827889115, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5206 = true := by
  decide +kernel

theorem tot5206 : totK PA10K2 A10K2.t5206 = [0, 498831047768, 1834140294685, 1975911541240, 585191372415, 24175405077, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5207 = true := by
  decide +kernel

theorem tot5207 : totK PA10K2 A10K2.t5207 = [0, 0, 606420678749, 2056222802306, 1766924692138, 418928905578, 25351274858, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
