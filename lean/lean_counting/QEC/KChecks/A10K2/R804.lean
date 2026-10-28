import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3216 = true := by
  decide +kernel

theorem tot3216 : totK PA10K2 A10K2.t3216 = [0, 0, 0, 763688648864, 2204536642066, 1660644633274, 280404583209, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3217 = true := by
  decide +kernel

theorem tot3217 : totK PA10K2 A10K2.t3217 = [0, 0, 512905690969, 1803238715029, 1900449908148, 677661150263, 58135435420, 0, 0, 0] := by
  decide +kernel

theorem rows3218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3218 = true := by
  decide +kernel

theorem tot3218 : totK PA10K2 A10K2.t3218 = [0, 0, 323255249417, 1520680515344, 2180244350365, 838308317229, 58591822478, 0, 0, 0] := by
  decide +kernel

theorem rows3219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3219 = true := by
  decide +kernel

theorem tot3219 : totK PA10K2 A10K2.t3219 = [0, 0, 0, 605117179358, 2075608375833, 1922410352900, 360997071129, 6157148557, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
