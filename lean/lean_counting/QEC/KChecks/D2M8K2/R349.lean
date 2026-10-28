import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1396 = true := by
  decide +kernel

theorem tot1396 : totK PD2M8K2 D2M8K2.t1396 = [0, 128056042844, 371435157600, 327849835850, 74941851933, 1231290674, 0, 0] := by
  decide +kernel

theorem rows1397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1397 = true := by
  decide +kernel

theorem tot1397 : totK PD2M8K2 D2M8K2.t1397 = [0, 174700740638, 436743066320, 273629950309, 29636797556, 0, 0, 0] := by
  decide +kernel

theorem rows1398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1398 = true := by
  decide +kernel

theorem tot1398 : totK PD2M8K2 D2M8K2.t1398 = [0, 125368878271, 442864362278, 309589145671, 25693942069, 0, 0, 0] := by
  decide +kernel

theorem rows1399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1399 = true := by
  decide +kernel

theorem tot1399 : totK PD2M8K2 D2M8K2.t1399 = [0, 0, 210931579728, 493302062922, 173200917183, 4903313894, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
