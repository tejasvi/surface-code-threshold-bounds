import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7220 = true := by
  decide +kernel

theorem tot7220 : totK PD2M8K2 D2M8K2.t7220 = [0, 0, 134395582739, 434700600873, 292175104549, 21689951291, 0, 0] := by
  decide +kernel

theorem rows7221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7221 = true := by
  decide +kernel

theorem tot7221 : totK PD2M8K2 D2M8K2.t7221 = [0, 0, 0, 313041329799, 474192333571, 82974796633, 1198073392, 0] := by
  decide +kernel

theorem rows7222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7222 = true := by
  decide +kernel

theorem tot7222 : totK PD2M8K2 D2M8K2.t7222 = [0, 0, 185702167921, 446656517220, 231663872405, 17321241699, 0, 0] := by
  decide +kernel

theorem rows7223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7223 = true := by
  decide +kernel

theorem tot7223 : totK PD2M8K2 D2M8K2.t7223 = [0, 0, 178857782226, 438405032578, 227391512411, 17104814242, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
