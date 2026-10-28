import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7860 = true := by
  decide +kernel

theorem tot7860 : totK PD2M8K2 D2M8K2.t7860 = [0, 162674308024, 464714481029, 250100736339, 17024329063, 0, 0, 0] := by
  decide +kernel

theorem rows7861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7861 = true := by
  decide +kernel

theorem tot7861 : totK PD2M8K2 D2M8K2.t7861 = [0, 0, 278840216549, 514044798730, 101181593349, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7862 = true := by
  decide +kernel

theorem tot7862 : totK PD2M8K2 D2M8K2.t7862 = [0, 81349714456, 321569206464, 373661700271, 104958091443, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7863 = true := by
  decide +kernel

theorem tot7863 : totK PD2M8K2 D2M8K2.t7863 = [0, 175026367109, 461150872723, 266634468970, 23866136797, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
