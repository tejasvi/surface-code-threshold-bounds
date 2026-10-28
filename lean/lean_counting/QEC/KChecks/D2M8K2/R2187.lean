import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8748 = true := by
  decide +kernel

theorem tot8748 : totK PD2M8K2 D2M8K2.t8748 = [0, 183592876567, 452149982706, 248450727060, 23218246917, 0, 0, 0] := by
  decide +kernel

theorem rows8749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8749 = true := by
  decide +kernel

theorem tot8749 : totK PD2M8K2 D2M8K2.t8749 = [0, 197578875173, 475149554494, 215603335887, 15733242309, 0, 0, 0] := by
  decide +kernel

theorem rows8750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8750 = true := by
  decide +kernel

theorem tot8750 : totK PD2M8K2 D2M8K2.t8750 = [0, 0, 308729478998, 477039179423, 91659886368, 1096505104, 0, 0] := by
  decide +kernel

theorem rows8751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8751 = true := by
  decide +kernel

theorem tot8751 : totK PD2M8K2 D2M8K2.t8751 = [0, 78851247754, 305430523958, 397667099008, 110161379434, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
