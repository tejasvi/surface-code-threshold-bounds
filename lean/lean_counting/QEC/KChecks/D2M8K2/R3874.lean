import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15496 = true := by
  decide +kernel

theorem tot15496 : totK PD2M8K2 D2M8K2.t15496 = [0, 0, 179273494639, 458300212425, 240834813037, 16355898272, 0, 0] := by
  decide +kernel

theorem rows15497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15497 = true := by
  decide +kernel

theorem tot15497 : totK PD2M8K2 D2M8K2.t15497 = [0, 0, 64209713546, 357111199391, 403929414001, 69666052454, 1107157161, 0] := by
  decide +kernel

theorem rows15498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15498 = true := by
  decide +kernel

theorem tot15498 : totK PD2M8K2 D2M8K2.t15498 = [0, 0, 39700116054, 292069278972, 429823091849, 108447934832, 3824247485, 0] := by
  decide +kernel

theorem rows15499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15499 = true := by
  decide +kernel

theorem tot15499 : totK PD2M8K2 D2M8K2.t15499 = [0, 0, 188407680887, 465540901038, 247911248110, 20128547347, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
