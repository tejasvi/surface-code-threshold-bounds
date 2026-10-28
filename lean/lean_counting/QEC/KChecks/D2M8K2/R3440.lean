import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13760 = true := by
  decide +kernel

theorem tot13760 : totK PD2M8K2 D2M8K2.t13760 = [0, 173835435312, 443112914891, 286094890193, 34616791348, 0, 0, 0] := by
  decide +kernel

theorem rows13761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13761 = true := by
  decide +kernel

theorem tot13761 : totK PD2M8K2 D2M8K2.t13761 = [0, 173977021590, 468993464094, 263499420581, 14199453916, 0, 0, 0] := by
  decide +kernel

theorem rows13762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13762 = true := by
  decide +kernel

theorem tot13762 : totK PD2M8K2 D2M8K2.t13762 = [0, 0, 256473427750, 518592439269, 135444474619, 1402015981, 0, 0] := by
  decide +kernel

theorem rows13763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13763 = true := by
  decide +kernel

theorem tot13763 : totK PD2M8K2 D2M8K2.t13763 = [0, 84969655104, 293742070856, 351439533373, 147536357650, 8173611642, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
