import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7092 = true := by
  decide +kernel

theorem tot7092 : totK PD2M8K2 D2M8K2.t7092 = [0, 70796540562, 338373868532, 411560818768, 88357409839, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7093 = true := by
  decide +kernel

theorem tot7093 : totK PD2M8K2 D2M8K2.t7093 = [0, 0, 217283189184, 491929794523, 168335314596, 9404247146, 0, 0] := by
  decide +kernel

theorem rows7094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7094 = true := by
  decide +kernel

theorem tot7094 : totK PD2M8K2 D2M8K2.t7094 = [0, 164868315185, 426198452862, 259611196259, 47176297599, 2481160468, 0, 0] := by
  decide +kernel

theorem rows7095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7095 = true := by
  decide +kernel

theorem tot7095 : totK PD2M8K2 D2M8K2.t7095 = [0, 154018528197, 430459004828, 285897051731, 28471201135, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
