import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14996 = true := by
  decide +kernel

theorem tot14996 : totK PD2M8K2 D2M8K2.t14996 = [0, 166512705254, 482655548110, 238206888547, 11505826626, 0, 0, 0] := by
  decide +kernel

theorem rows14997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14997 = true := by
  decide +kernel

theorem tot14997 : totK PD2M8K2 D2M8K2.t14997 = [0, 162050865518, 439673509965, 254378443147, 19960481287, 0, 0, 0] := by
  decide +kernel

theorem rows14998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14998 = true := by
  decide +kernel

theorem tot14998 : totK PD2M8K2 D2M8K2.t14998 = [0, 0, 277358716638, 503081398045, 101512527928, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14999 = true := by
  decide +kernel

theorem tot14999 : totK PD2M8K2 D2M8K2.t14999 = [0, 112177858867, 392243376169, 371558149141, 48305673977, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
