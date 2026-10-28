import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12620 = true := by
  decide +kernel

theorem tot12620 : totK PD2M8K2 D2M8K2.t12620 = [0, 0, 84743791138, 381450519658, 374595705679, 35173136373, 0, 0] := by
  decide +kernel

theorem rows12621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12621 = true := by
  decide +kernel

theorem tot12621 : totK PD2M8K2 D2M8K2.t12621 = [0, 0, 160098110132, 479009478415, 247114477406, 11390216766, 0, 0] := by
  decide +kernel

theorem rows12622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12622 = true := by
  decide +kernel

theorem tot12622 : totK PD2M8K2 D2M8K2.t12622 = [0, 0, 190659259268, 461104314777, 217443850329, 15177561184, 0, 0] := by
  decide +kernel

theorem rows12623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12623 = true := by
  decide +kernel

theorem tot12623 : totK PD2M8K2 D2M8K2.t12623 = [0, 0, 205793224463, 497148234330, 194952080458, 5405003506, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
