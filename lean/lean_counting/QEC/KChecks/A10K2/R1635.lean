import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6540 = true := by
  decide +kernel

theorem tot6540 : totK PA10K2 A10K2.t6540 = [0, 0, 358002183444, 1624611321999, 2061684179001, 622687177918, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows6541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6541 = true := by
  decide +kernel

theorem tot6541 : totK PA10K2 A10K2.t6541 = [0, 0, 0, 725874074237, 2103417334893, 1494368289178, 228941018041, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6542 = true := by
  decide +kernel

theorem tot6542 : totK PA10K2 A10K2.t6542 = [0, 0, 0, 495019451175, 1840625567734, 1884411005929, 447637417449, 26712336714, 0, 0] := by
  decide +kernel

theorem rows6543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6543 = true := by
  decide +kernel

theorem tot6543 : totK PA10K2 A10K2.t6543 = [0, 0, 0, 557788492368, 1956711493511, 1857211156504, 436156919365, 18639925796, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
