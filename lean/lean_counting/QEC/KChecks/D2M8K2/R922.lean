import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3688 = true := by
  decide +kernel

theorem tot3688 : totK PD2M8K2 D2M8K2.t3688 = [0, 0, 187383681858, 450109013604, 236931709920, 22801359543, 0, 0] := by
  decide +kernel

theorem rows3689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3689 = true := by
  decide +kernel

theorem tot3689 : totK PD2M8K2 D2M8K2.t3689 = [0, 0, 105894248848, 437052260539, 301254471224, 27005494330, 0, 0] := by
  decide +kernel

theorem rows3690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3690 = true := by
  decide +kernel

theorem tot3690 : totK PD2M8K2 D2M8K2.t3690 = [0, 0, 0, 303272042900, 467776874027, 92173893095, 1095107716, 0] := by
  decide +kernel

theorem rows3691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3691 = true := by
  decide +kernel

theorem tot3691 : totK PD2M8K2 D2M8K2.t3691 = [169749411087, 341393312455, 102244770237, 37845548929, 155878543587, 81046118049, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
