import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5132 = true := by
  decide +kernel

theorem tot5132 : totK PA10K2 A10K2.t5132 = [0, 0, 0, 797721759257, 2114269135946, 1410080970490, 310041162211, 25130442608, 0, 0] := by
  decide +kernel

theorem rows5133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5133 = true := by
  decide +kernel

theorem tot5133 : totK PA10K2 A10K2.t5133 = [0, 0, 375139718867, 1406496818190, 1851364696937, 917919482705, 147388456701, 5517381808, 0, 0] := by
  decide +kernel

theorem rows5134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5134 = true := by
  decide +kernel

theorem tot5134 : totK PA10K2 A10K2.t5134 = [0, 0, 405699854225, 1771367759038, 2007450450532, 548056627469, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows5135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5135 = true := by
  decide +kernel

theorem tot5135 : totK PA10K2 A10K2.t5135 = [0, 0, 0, 710865859298, 2201367221943, 1429019576214, 212544869940, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
