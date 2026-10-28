import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15732 = true := by
  decide +kernel

theorem tot15732 : totK PD2M8K2 D2M8K2.t15732 = [0, 0, 62121613378, 302454197490, 403898856770, 96698706869, 3783381897, 0] := by
  decide +kernel

theorem rows15733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15733 = true := by
  decide +kernel

theorem tot15733 : totK PD2M8K2 D2M8K2.t15733 = [0, 0, 176285599562, 463700504118, 246879442492, 22476384962, 0, 0] := by
  decide +kernel

theorem rows15734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15734 = true := by
  decide +kernel

theorem tot15734 : totK PD2M8K2 D2M8K2.t15734 = [0, 0, 179255141055, 475669943833, 242585777726, 13760291752, 0, 0] := by
  decide +kernel

theorem rows15735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15735 = true := by
  decide +kernel

theorem tot15735 : totK PD2M8K2 D2M8K2.t15735 = [0, 0, 0, 280445786044, 500046453214, 106308165972, 1240621948, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
