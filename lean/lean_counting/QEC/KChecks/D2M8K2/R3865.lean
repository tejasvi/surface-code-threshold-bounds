import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15460 = true := by
  decide +kernel

theorem tot15460 : totK PD2M8K2 D2M8K2.t15460 = [0, 0, 179626906886, 483320600602, 238668979568, 12227244834, 0, 0] := by
  decide +kernel

theorem rows15461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15461 = true := by
  decide +kernel

theorem tot15461 : totK PD2M8K2 D2M8K2.t15461 = [0, 0, 173092305199, 457888049897, 246215737056, 15054696819, 0, 0] := by
  decide +kernel

theorem rows15462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15462 = true := by
  decide +kernel

theorem tot15462 : totK PD2M8K2 D2M8K2.t15462 = [0, 0, 195846429384, 472409064021, 220808239875, 15844255384, 0, 0] := by
  decide +kernel

theorem rows15463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15463 = true := by
  decide +kernel

theorem tot15463 : totK PD2M8K2 D2M8K2.t15463 = [0, 0, 187542761231, 448881769152, 221994357698, 16702988424, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
