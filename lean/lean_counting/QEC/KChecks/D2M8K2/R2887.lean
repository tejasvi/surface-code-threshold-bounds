import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11548 = true := by
  decide +kernel

theorem tot11548 : totK PD2M8K2 D2M8K2.t11548 = [0, 0, 209639848310, 450054568907, 229035900012, 23423501648, 0, 0] := by
  decide +kernel

theorem rows11549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11549 = true := by
  decide +kernel

theorem tot11549 : totK PD2M8K2 D2M8K2.t11549 = [0, 0, 190413023265, 471796372608, 217303111935, 9205456698, 0, 0] := by
  decide +kernel

theorem rows11550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11550 = true := by
  decide +kernel

theorem tot11550 : totK PD2M8K2 D2M8K2.t11550 = [0, 0, 0, 311500012918, 483222434328, 87113820979, 1323630408, 0] := by
  decide +kernel

theorem rows11551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11551 = true := by
  decide +kernel

theorem tot11551 : totK PD2M8K2 D2M8K2.t11551 = [0, 0, 155062923995, 441257710859, 284292133921, 21841125667, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
