import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8996 = true := by
  decide +kernel

theorem tot8996 : totK PD2M8K2 D2M8K2.t8996 = [0, 211638557676, 486163758429, 180564974117, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows8997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8997 = true := by
  decide +kernel

theorem tot8997 : totK PD2M8K2 D2M8K2.t8997 = [0, 185894700346, 471608461308, 222665599699, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows8998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8998 = true := by
  decide +kernel

theorem tot8998 : totK PD2M8K2 D2M8K2.t8998 = [0, 185501779440, 473186845844, 206846682648, 7984731767, 0, 0, 0] := by
  decide +kernel

theorem rows8999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8999 = true := by
  decide +kernel

theorem tot8999 : totK PD2M8K2 D2M8K2.t8999 = [0, 88852439121, 365671713205, 357518577182, 64558965320, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
