import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14684 = true := by
  decide +kernel

theorem tot14684 : totK PD2M8K2 D2M8K2.t14684 = [0, 169573815375, 468267688357, 230425311742, 10971968313, 0, 0, 0] := by
  decide +kernel

theorem rows14685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14685 = true := by
  decide +kernel

theorem tot14685 : totK PD2M8K2 D2M8K2.t14685 = [0, 153082850923, 440841967232, 267580594521, 21711714950, 0, 0, 0] := by
  decide +kernel

theorem rows14686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14686 = true := by
  decide +kernel

theorem tot14686 : totK PD2M8K2 D2M8K2.t14686 = [0, 0, 275873384908, 497230924870, 100268207247, 1310517177, 0, 0] := by
  decide +kernel

theorem rows14687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14687 = true := by
  decide +kernel

theorem tot14687 : totK PD2M8K2 D2M8K2.t14687 = [0, 147472534373, 398620637911, 335663155350, 40344082339, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
