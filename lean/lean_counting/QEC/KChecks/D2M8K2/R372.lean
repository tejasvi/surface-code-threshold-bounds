import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1488 = true := by
  decide +kernel

theorem tot1488 : totK PD2M8K2 D2M8K2.t1488 = [0, 0, 55502821843, 327489935998, 415302340124, 79540139040, 1288491354, 0] := by
  decide +kernel

theorem rows1489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1489 = true := by
  decide +kernel

theorem tot1489 : totK PD2M8K2 D2M8K2.t1489 = [0, 0, 72980774252, 371057177956, 390375073260, 39534255389, 0, 0] := by
  decide +kernel

theorem rows1490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1490 = true := by
  decide +kernel

theorem tot1490 : totK PD2M8K2 D2M8K2.t1490 = [0, 0, 188651009633, 471376071711, 228629747749, 18087669958, 0, 0] := by
  decide +kernel

theorem rows1491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1491 = true := by
  decide +kernel

theorem tot1491 : totK PD2M8K2 D2M8K2.t1491 = [0, 0, 206357390743, 473580744913, 205475387126, 15083436772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
