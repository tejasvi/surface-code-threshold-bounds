import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16304 = true := by
  decide +kernel

theorem tot16304 : totK PD2M8K2 D2M8K2.t16304 = [0, 0, 0, 192225182318, 480868596887, 172245699596, 6316512032, 0] := by
  decide +kernel

theorem rows16305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16305 = true := by
  decide +kernel

theorem tot16305 : totK PD2M8K2 D2M8K2.t16305 = [0, 0, 0, 86628205362, 359380424776, 344599600644, 56089895180, 1166720416] := by
  decide +kernel

theorem rows16306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16306 = true := by
  decide +kernel

theorem tot16306 : totK PD2M8K2 D2M8K2.t16306 = [0, 0, 0, 91338459007, 432764639992, 330209819748, 27346764486, 0] := by
  decide +kernel

theorem rows16307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16307 = true := by
  decide +kernel

theorem tot16307 : totK PD2M8K2 D2M8K2.t16307 = [0, 0, 0, 265561531035, 475394645020, 168878202961, 7956535775, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
