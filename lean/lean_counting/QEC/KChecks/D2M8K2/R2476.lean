import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9904 = true := by
  decide +kernel

theorem tot9904 : totK PD2M8K2 D2M8K2.t9904 = [0, 146437819848, 398716146732, 291119748692, 72039755836, 2567510802, 0, 0] := by
  decide +kernel

theorem rows9905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9905 = true := by
  decide +kernel

theorem tot9905 : totK PD2M8K2 D2M8K2.t9905 = [0, 177569830925, 440586472297, 266565167175, 26559918375, 0, 0, 0] := by
  decide +kernel

theorem rows9906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9906 = true := by
  decide +kernel

theorem tot9906 : totK PD2M8K2 D2M8K2.t9906 = [0, 115702863969, 437068813422, 334536606233, 29219205540, 0, 0, 0] := by
  decide +kernel

theorem rows9907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9907 = true := by
  decide +kernel

theorem tot9907 : totK PD2M8K2 D2M8K2.t9907 = [0, 0, 208613273088, 491031157250, 172864665010, 4967996017, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
