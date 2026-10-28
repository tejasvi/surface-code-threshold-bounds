import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1208 = true := by
  decide +kernel

theorem tot1208 : totK PD2M8K2 D2M8K2.t1208 = [0, 179566245728, 495477343448, 221223331188, 6583237743, 0, 0, 0] := by
  decide +kernel

theorem rows1209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1209 = true := by
  decide +kernel

theorem tot1209 : totK PD2M8K2 D2M8K2.t1209 = [0, 173478730646, 459267216273, 242484946720, 13577881100, 0, 0, 0] := by
  decide +kernel

theorem rows1210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1210 = true := by
  decide +kernel

theorem tot1210 : totK PD2M8K2 D2M8K2.t1210 = [93994421500, 299344737225, 359042301106, 164914515872, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows1211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1211 = true := by
  decide +kernel

theorem tot1211 : totK PD2M8K2 D2M8K2.t1211 = [174117065510, 448521971494, 257947657241, 22741284992, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
