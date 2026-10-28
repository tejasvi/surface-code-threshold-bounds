import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6096 = true := by
  decide +kernel

theorem tot6096 : totK PD2M8K2 D2M8K2.t6096 = [0, 133784980717, 356429674900, 297157036058, 115276417359, 6804944647, 0, 0] := by
  decide +kernel

theorem rows6097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6097 = true := by
  decide +kernel

theorem tot6097 : totK PD2M8K2 D2M8K2.t6097 = [0, 168216856199, 436323334223, 277336596656, 30303715720, 0, 0, 0] := by
  decide +kernel

theorem rows6098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6098 = true := by
  decide +kernel

theorem tot6098 : totK PD2M8K2 D2M8K2.t6098 = [0, 107350114340, 422838639532, 332165867183, 40071961089, 0, 0, 0] := by
  decide +kernel

theorem rows6099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6099 = true := by
  decide +kernel

theorem tot6099 : totK PD2M8K2 D2M8K2.t6099 = [0, 0, 228990380611, 487914124197, 169365537153, 7879028762, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
