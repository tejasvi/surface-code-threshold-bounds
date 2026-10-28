import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10608 = true := by
  decide +kernel

theorem tot10608 : totK PD2M8K2 D2M8K2.t10608 = [0, 0, 291849136697, 517268040293, 100859073672, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10609 = true := by
  decide +kernel

theorem tot10609 : totK PD2M8K2 D2M8K2.t10609 = [0, 148509923255, 367475697466, 282003638779, 90208604524, 3884009855, 0, 0] := by
  decide +kernel

theorem rows10610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10610 = true := by
  decide +kernel

theorem tot10610 : totK PD2M8K2 D2M8K2.t10610 = [0, 177629236443, 448486099110, 275780982544, 28057959645, 0, 0, 0] := by
  decide +kernel

theorem rows10611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10611 = true := by
  decide +kernel

theorem tot10611 : totK PD2M8K2 D2M8K2.t10611 = [0, 19586248967, 309869270779, 463749011740, 101345411316, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
