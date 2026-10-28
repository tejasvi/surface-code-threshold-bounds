import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8148 = true := by
  decide +kernel

theorem tot8148 : totK PA10K2 A10K2.t8148 = [0, 0, 0, 563781224979, 1889583146976, 1868440584486, 596891422129, 50403516269, 0, 0] := by
  decide +kernel

theorem rows8149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8149 = true := by
  decide +kernel

theorem tot8149 : totK PA10K2 A10K2.t8149 = [0, 0, 0, 331364255318, 1545568977829, 2177881952137, 840856758837, 62972848401, 0, 0] := by
  decide +kernel

theorem rows8150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8150 = true := by
  decide +kernel

theorem tot8150 : totK PA10K2 A10K2.t8150 = [0, 0, 0, 0, 592646115474, 2014740392328, 1906710109017, 395674612583, 12224107035, 0] := by
  decide +kernel

theorem rows8151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8151 = true := by
  decide +kernel

theorem tot8151 : totK PA10K2 A10K2.t8151 = [0, 0, 0, 309157067044, 1069347478746, 1532153170515, 1406996392234, 522441368230, 48886019071, 0] := by
  decide +kernel

end QECKChecks.A10K2
