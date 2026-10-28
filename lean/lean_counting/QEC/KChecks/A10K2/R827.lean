import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3308 = true := by
  decide +kernel

theorem tot3308 : totK PA10K2 A10K2.t3308 = [0, 0, 238785603865, 1095438274932, 1886011550167, 1210827824448, 196990494554, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3309 = true := by
  decide +kernel

theorem tot3309 : totK PA10K2 A10K2.t3309 = [0, 0, 468580175535, 1650035880284, 1850933120353, 620423542495, 51963961291, 0, 0, 0] := by
  decide +kernel

theorem rows3310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3310 = true := by
  decide +kernel

theorem tot3310 : totK PA10K2 A10K2.t3310 = [0, 0, 113126642960, 1226893728906, 2276771130622, 941411059178, 66260200463, 0, 0, 0] := by
  decide +kernel

theorem rows3311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3311 = true := by
  decide +kernel

theorem tot3311 : totK PA10K2 A10K2.t3311 = [0, 0, 0, 545672285859, 1971160494834, 1702274224432, 363044356418, 11740475125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
