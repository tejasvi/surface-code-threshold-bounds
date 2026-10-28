import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14284 = true := by
  decide +kernel

theorem tot14284 : totK PD2M8K2 D2M8K2.t14284 = [0, 106776214259, 410381775589, 337460712086, 33106460145, 0, 0, 0] := by
  decide +kernel

theorem rows14285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14285 = true := by
  decide +kernel

theorem tot14285 : totK PD2M8K2 D2M8K2.t14285 = [0, 0, 256701602190, 468083627609, 130717334809, 4879840392, 0, 0] := by
  decide +kernel

theorem rows14286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14286 = true := by
  decide +kernel

theorem tot14286 : totK PD2M8K2 D2M8K2.t14286 = [0, 166608574014, 446206804147, 270909577089, 31134578609, 0, 0, 0] := by
  decide +kernel

theorem rows14287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14287 = true := by
  decide +kernel

theorem tot14287 : totK PD2M8K2 D2M8K2.t14287 = [0, 177838460170, 461798213281, 262867533139, 18018096887, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
