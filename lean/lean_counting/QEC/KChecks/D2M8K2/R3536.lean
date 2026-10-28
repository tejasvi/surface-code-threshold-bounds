import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14144 = true := by
  decide +kernel

theorem tot14144 : totK PD2M8K2 D2M8K2.t14144 = [0, 164427823115, 482069258319, 245669139091, 11476444046, 0, 0, 0] := by
  decide +kernel

theorem rows14145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14145 = true := by
  decide +kernel

theorem tot14145 : totK PD2M8K2 D2M8K2.t14145 = [0, 170555806903, 462251064376, 227899794152, 11310342365, 0, 0, 0] := by
  decide +kernel

theorem rows14146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14146 = true := by
  decide +kernel

theorem tot14146 : totK PD2M8K2 D2M8K2.t14146 = [0, 200091714391, 469250824777, 209762343723, 13631677425, 0, 0, 0] := by
  decide +kernel

theorem rows14147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14147 = true := by
  decide +kernel

theorem tot14147 : totK PD2M8K2 D2M8K2.t14147 = [0, 206151084584, 467078303584, 204794094315, 12595094539, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
