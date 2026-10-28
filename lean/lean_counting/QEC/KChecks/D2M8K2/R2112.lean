import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8448 = true := by
  decide +kernel

theorem tot8448 : totK PD2M8K2 D2M8K2.t8448 = [0, 166518511442, 429183369863, 263165522272, 49566519067, 2751766863, 0, 0] := by
  decide +kernel

theorem rows8449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8449 = true := by
  decide +kernel

theorem tot8449 : totK PD2M8K2 D2M8K2.t8449 = [0, 205669090563, 467077742167, 217833091157, 15869081357, 0, 0, 0] := by
  decide +kernel

theorem rows8450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8450 = true := by
  decide +kernel

theorem tot8450 : totK PD2M8K2 D2M8K2.t8450 = [0, 38279877783, 317712432339, 442144300457, 95600140566, 1232609433, 0, 0] := by
  decide +kernel

theorem rows8451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8451 = true := by
  decide +kernel

theorem tot8451 : totK PD2M8K2 D2M8K2.t8451 = [0, 0, 262135332902, 500888944115, 132713513818, 3724448267, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
