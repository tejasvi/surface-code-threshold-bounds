import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2996 = true := by
  decide +kernel

theorem tot2996 : totK PD2M8K2 D2M8K2.t2996 = [0, 0, 181612058624, 473967766406, 226249654589, 9337917398, 0, 0] := by
  decide +kernel

theorem rows2997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2997 = true := by
  decide +kernel

theorem tot2997 : totK PD2M8K2 D2M8K2.t2997 = [0, 138229103118, 346231580425, 300690981139, 114427375046, 6761253570, 0, 0] := by
  decide +kernel

theorem rows2998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2998 = true := by
  decide +kernel

theorem tot2998 : totK PD2M8K2 D2M8K2.t2998 = [0, 167771478202, 439743878697, 282347056814, 30482942220, 0, 0, 0] := by
  decide +kernel

theorem rows2999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2999 = true := by
  decide +kernel

theorem tot2999 : totK PD2M8K2 D2M8K2.t2999 = [0, 119961603731, 437126775805, 306865593486, 25756386890, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
