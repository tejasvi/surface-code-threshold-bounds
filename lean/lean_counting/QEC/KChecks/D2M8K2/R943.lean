import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3772 = true := by
  decide +kernel

theorem tot3772 : totK PD2M8K2 D2M8K2.t3772 = [0, 312190917461, 496107101517, 90663460628, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3773 = true := by
  decide +kernel

theorem tot3773 : totK PD2M8K2 D2M8K2.t3773 = [138695734110, 360540358451, 290698294758, 89205928944, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows3774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3774 = true := by
  decide +kernel

theorem tot3774 : totK PD2M8K2 D2M8K2.t3774 = [171841100719, 440152423481, 277187550505, 30107575368, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3775 = true := by
  decide +kernel

theorem tot3775 : totK PD2M8K2 D2M8K2.t3775 = [111868955890, 435766214051, 329035489125, 27788246819, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
