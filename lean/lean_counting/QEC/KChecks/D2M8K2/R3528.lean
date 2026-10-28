import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14112 = true := by
  decide +kernel

theorem tot14112 : totK PD2M8K2 D2M8K2.t14112 = [0, 0, 0, 319935029223, 474319772082, 84466494813, 1323630408, 0] := by
  decide +kernel

theorem rows14113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14113 = true := by
  decide +kernel

theorem tot14113 : totK PD2M8K2 D2M8K2.t14113 = [0, 0, 164981134323, 434548532777, 279442547264, 31693776348, 0, 0] := by
  decide +kernel

theorem rows14114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14114 = true := by
  decide +kernel

theorem tot14114 : totK PD2M8K2 D2M8K2.t14114 = [0, 0, 172191131950, 438274866785, 250929273257, 16520169388, 0, 0] := by
  decide +kernel

theorem rows14115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14115 = true := by
  decide +kernel

theorem tot14115 : totK PD2M8K2 D2M8K2.t14115 = [0, 0, 71717306549, 412724411085, 392196124621, 36869283421, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
