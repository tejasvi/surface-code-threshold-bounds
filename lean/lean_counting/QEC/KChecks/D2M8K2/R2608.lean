import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10432 = true := by
  decide +kernel

theorem tot10432 : totK PD2M8K2 D2M8K2.t10432 = [0, 0, 138298449317, 360874164785, 287998779677, 84168673768, 3884009855, 0] := by
  decide +kernel

theorem rows10433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10433 = true := by
  decide +kernel

theorem tot10433 : totK PD2M8K2 D2M8K2.t10433 = [0, 0, 186065475918, 452859408626, 248811039919, 23387773757, 0, 0] := by
  decide +kernel

theorem rows10434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10434 = true := by
  decide +kernel

theorem tot10434 : totK PD2M8K2 D2M8K2.t10434 = [0, 0, 92242864877, 391930306086, 361538424517, 55243686713, 1268739303, 0] := by
  decide +kernel

theorem rows10435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10435 = true := by
  decide +kernel

theorem tot10435 : totK PD2M8K2 D2M8K2.t10435 = [0, 0, 0, 242699625331, 498758370109, 143722787255, 3742744013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
