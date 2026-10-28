import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11196 = true := by
  decide +kernel

theorem tot11196 : totK PD2M8K2 D2M8K2.t11196 = [0, 0, 287586019068, 521148980963, 94564158998, 1096505104, 0, 0] := by
  decide +kernel

theorem rows11197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11197 = true := by
  decide +kernel

theorem tot11197 : totK PD2M8K2 D2M8K2.t11197 = [0, 141484286328, 372525795530, 291149361750, 90274051683, 3884009855, 0, 0] := by
  decide +kernel

theorem rows11198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11198 = true := by
  decide +kernel

theorem tot11198 : totK PD2M8K2 D2M8K2.t11198 = [0, 181213321682, 445677653242, 229177427745, 16954357240, 0, 0, 0] := by
  decide +kernel

theorem rows11199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11199 = true := by
  decide +kernel

theorem tot11199 : totK PD2M8K2 D2M8K2.t11199 = [0, 96670462214, 406708906638, 349183617972, 41917576559, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
