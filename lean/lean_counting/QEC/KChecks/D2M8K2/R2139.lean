import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8556 = true := by
  decide +kernel

theorem tot8556 : totK PD2M8K2 D2M8K2.t8556 = [0, 157772069674, 460692463214, 248495948135, 16156443912, 0, 0, 0] := by
  decide +kernel

theorem rows8557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8557 = true := by
  decide +kernel

theorem tot8557 : totK PD2M8K2 D2M8K2.t8557 = [0, 0, 316743295662, 460744684451, 78901423739, 1021600638, 0, 0] := by
  decide +kernel

theorem rows8558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8558 = true := by
  decide +kernel

theorem tot8558 : totK PD2M8K2 D2M8K2.t8558 = [0, 156763095093, 372520774157, 270298710642, 76473184407, 3552795014, 0, 0] := by
  decide +kernel

theorem rows8559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8559 = true := by
  decide +kernel

theorem tot8559 : totK PD2M8K2 D2M8K2.t8559 = [0, 156416194345, 447319072535, 276869479170, 19567755204, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
