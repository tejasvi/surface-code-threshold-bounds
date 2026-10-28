import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16116 = true := by
  decide +kernel

theorem tot16116 : totK PD2M8K2 D2M8K2.t16116 = [0, 0, 71432936211, 400547574310, 397216440636, 45314829264, 0, 0] := by
  decide +kernel

theorem rows16117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16117 = true := by
  decide +kernel

theorem tot16117 : totK PD2M8K2 D2M8K2.t16117 = [0, 0, 17515826061, 238857562209, 491284379998, 134690912884, 2665309491, 0] := by
  decide +kernel

theorem rows16118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16118 = true := by
  decide +kernel

theorem tot16118 : totK PD2M8K2 D2M8K2.t16118 = [0, 0, 194802873901, 463016212514, 241323723192, 22881355256, 0, 0] := by
  decide +kernel

theorem rows16119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16119 = true := by
  decide +kernel

theorem tot16119 : totK PD2M8K2 D2M8K2.t16119 = [0, 0, 198292033568, 478199241788, 212618759805, 10872989731, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
