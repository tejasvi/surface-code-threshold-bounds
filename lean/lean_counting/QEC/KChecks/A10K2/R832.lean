import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3328 = true := by
  decide +kernel

theorem tot3328 : totK PA10K2 A10K2.t3328 = [0, 529342468613, 1714880397980, 1861694404806, 726991711096, 70611497610, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3329 = true := by
  decide +kernel

theorem tot3329 : totK PA10K2 A10K2.t3329 = [0, 27363690904, 974633627225, 2306715081972, 1263216997694, 122697539596, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3330 = true := by
  decide +kernel

theorem tot3330 : totK PA10K2 A10K2.t3330 = [0, 495771531347, 1740779863405, 1858365855434, 725734258664, 140962603698, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3331 = true := by
  decide +kernel

theorem tot3331 : totK PA10K2 A10K2.t3331 = [0, 319364795913, 1458301820920, 2178197233229, 1086209116851, 113300226930, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
