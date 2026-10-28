import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7264 = true := by
  decide +kernel

theorem tot7264 : totK PD2M8K2 D2M8K2.t7264 = [0, 0, 171434888783, 473148214362, 240095281368, 12597559134, 0, 0] := by
  decide +kernel

theorem rows7265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7265 = true := by
  decide +kernel

theorem tot7265 : totK PD2M8K2 D2M8K2.t7265 = [0, 0, 180112401003, 459772208623, 239426795242, 14728377376, 0, 0] := by
  decide +kernel

theorem rows7266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7266 = true := by
  decide +kernel

theorem tot7266 : totK PD2M8K2 D2M8K2.t7266 = [0, 0, 193944355474, 451182911180, 218264662500, 14884237666, 0, 0] := by
  decide +kernel

theorem rows7267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7267 = true := by
  decide +kernel

theorem tot7267 : totK PD2M8K2 D2M8K2.t7267 = [0, 0, 19168591844, 342942457838, 433897212022, 67921206646, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
