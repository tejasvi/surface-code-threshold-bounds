import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3372 = true := by
  decide +kernel

theorem tot3372 : totK PA10K2 A10K2.t3372 = [0, 0, 0, 392866844511, 1555658519602, 2053199729474, 839673859541, 67554903480, 0, 0] := by
  decide +kernel

theorem rows3373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3373 = true := by
  decide +kernel

theorem tot3373 : totK PA10K2 A10K2.t3373 = [0, 0, 0, 449177658642, 1774294538399, 2022673878810, 635527348394, 27560733286, 0, 0] := by
  decide +kernel

theorem rows3374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3374 = true := by
  decide +kernel

theorem tot3374 : totK PA10K2 A10K2.t3374 = [0, 0, 0, 0, 827212288527, 2256126881297, 1448265416651, 245517337120, 7151180950, 0] := by
  decide +kernel

theorem rows3375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3375 = true := by
  decide +kernel

theorem tot3375 : totK PA10K2 A10K2.t3375 = [0, 0, 0, 755048217192, 2127290139681, 1529354881631, 347547620557, 30107499662, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
