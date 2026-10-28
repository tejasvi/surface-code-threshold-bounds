import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t480 = true := by
  decide +kernel

theorem tot480 : totK PD2M8K2 D2M8K2.t480 = [0, 0, 285820792379, 492306561141, 105522670400, 1077684915, 0, 0] := by
  decide +kernel

theorem rows481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t481 = true := by
  decide +kernel

theorem tot481 : totK PD2M8K2 D2M8K2.t481 = [0, 0, 152020558335, 475576378918, 223436864881, 11028107081, 0, 0] := by
  decide +kernel

theorem rows482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t482 = true := by
  decide +kernel

theorem tot482 : totK PD2M8K2 D2M8K2.t482 = [0, 0, 217258622837, 493812626013, 154546269099, 4922956474, 0, 0] := by
  decide +kernel

theorem rows483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t483 = true := by
  decide +kernel

theorem tot483 : totK PD2M8K2 D2M8K2.t483 = [0, 0, 208170845355, 489367467105, 186730358427, 5274443905, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
