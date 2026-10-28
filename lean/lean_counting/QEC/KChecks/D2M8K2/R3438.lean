import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13752 = true := by
  decide +kernel

theorem tot13752 : totK PD2M8K2 D2M8K2.t13752 = [0, 138113149829, 366150482445, 307005203075, 76719308633, 3581949829, 0, 0] := by
  decide +kernel

theorem rows13753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13753 = true := by
  decide +kernel

theorem tot13753 : totK PD2M8K2 D2M8K2.t13753 = [0, 176320716490, 447549357128, 250620947608, 25456463288, 0, 0, 0] := by
  decide +kernel

theorem rows13754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13754 = true := by
  decide +kernel

theorem tot13754 : totK PD2M8K2 D2M8K2.t13754 = [0, 105443762153, 424575506677, 332651268123, 27779049137, 0, 0, 0] := by
  decide +kernel

theorem rows13755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13755 = true := by
  decide +kernel

theorem tot13755 : totK PD2M8K2 D2M8K2.t13755 = [0, 0, 288357120885, 508101966626, 99458184981, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
