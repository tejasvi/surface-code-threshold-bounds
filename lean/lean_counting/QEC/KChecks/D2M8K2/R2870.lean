import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11480 = true := by
  decide +kernel

theorem tot11480 : totK PD2M8K2 D2M8K2.t11480 = [0, 159586473207, 445837666769, 284085681111, 24249600687, 0, 0, 0] := by
  decide +kernel

theorem rows11481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11481 = true := by
  decide +kernel

theorem tot11481 : totK PD2M8K2 D2M8K2.t11481 = [0, 69860819457, 341107458294, 393755461226, 86838077810, 1232609433, 0, 0] := by
  decide +kernel

theorem rows11482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11482 = true := by
  decide +kernel

theorem tot11482 : totK PD2M8K2 D2M8K2.t11482 = [0, 0, 227732451750, 490205624250, 169922440515, 5008494805, 0, 0] := by
  decide +kernel

theorem rows11483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11483 = true := by
  decide +kernel

theorem tot11483 : totK PD2M8K2 D2M8K2.t11483 = [0, 0, 196474175809, 469536465734, 202103595969, 12964618821, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
