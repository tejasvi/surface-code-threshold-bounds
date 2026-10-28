import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3112 = true := by
  decide +kernel

theorem tot3112 : totK PD2M8K2 D2M8K2.t3112 = [91792297750, 396780112588, 374066172440, 42809344621, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3113 = true := by
  decide +kernel

theorem tot3113 : totK PD2M8K2 D2M8K2.t3113 = [0, 224546083766, 483574693770, 174659381471, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows3114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3114 = true := by
  decide +kernel

theorem tot3114 : totK PD2M8K2 D2M8K2.t3114 = [0, 182420275949, 462901819061, 222544478897, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows3115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3115 = true := by
  decide +kernel

theorem tot3115 : totK PD2M8K2 D2M8K2.t3115 = [0, 158746266236, 465685369832, 237415008999, 15527224862, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
