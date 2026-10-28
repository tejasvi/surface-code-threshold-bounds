import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14500 = true := by
  decide +kernel

theorem tot14500 : totK PD2M8K2 D2M8K2.t14500 = [189872538507, 464863627282, 243455727211, 18422459197, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14501 = true := by
  decide +kernel

theorem tot14501 : totK PD2M8K2 D2M8K2.t14501 = [140452205640, 437205198658, 287158879808, 31938269196, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14502 = true := by
  decide +kernel

theorem tot14502 : totK PD2M8K2 D2M8K2.t14502 = [0, 187539021981, 443487824387, 250259800492, 25182428102, 0, 0, 0] := by
  decide +kernel

theorem rows14503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14503 = true := by
  decide +kernel

theorem tot14503 : totK PD2M8K2 D2M8K2.t14503 = [0, 190622541956, 501958360263, 193847976010, 5430665091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
