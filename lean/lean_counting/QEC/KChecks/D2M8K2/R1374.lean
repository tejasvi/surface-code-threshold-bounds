import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5496 = true := by
  decide +kernel

theorem tot5496 : totK PD2M8K2 D2M8K2.t5496 = [0, 0, 0, 89086514936, 443907562519, 333974508210, 28288242255, 0] := by
  decide +kernel

theorem rows5497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5497 = true := by
  decide +kernel

theorem tot5497 : totK PD2M8K2 D2M8K2.t5497 = [0, 0, 0, 75818660868, 325045333181, 371634165890, 78792346461, 1406452163] := by
  decide +kernel

theorem rows5498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5498 = true := by
  decide +kernel

theorem tot5498 : totK PD2M8K2 D2M8K2.t5498 = [0, 0, 0, 177438778902, 482179935431, 223611313380, 12617904510, 0] := by
  decide +kernel

theorem rows5499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5499 = true := by
  decide +kernel

theorem tot5499 : totK PD2M8K2 D2M8K2.t5499 = [0, 0, 0, 151886619858, 457794030285, 259941300611, 17662484302, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
