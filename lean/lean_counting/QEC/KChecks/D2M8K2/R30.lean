import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t120 = true := by
  decide +kernel

theorem tot120 : totK PD2M8K2 D2M8K2.t120 = [174518392041, 441143988985, 266517668568, 27639114520, 0, 0, 0, 0] := by
  decide +kernel

theorem rows121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t121 = true := by
  decide +kernel

theorem tot121 : totK PD2M8K2 D2M8K2.t121 = [125176578775, 456912392936, 296350074941, 23634285059, 0, 0, 0, 0] := by
  decide +kernel

theorem rows122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t122 = true := by
  decide +kernel

theorem tot122 : totK PD2M8K2 D2M8K2.t122 = [0, 280593769477, 522774298792, 100902179550, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t123 = true := by
  decide +kernel

theorem tot123 : totK PD2M8K2 D2M8K2.t123 = [0, 206401940793, 498609361474, 181301255653, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
