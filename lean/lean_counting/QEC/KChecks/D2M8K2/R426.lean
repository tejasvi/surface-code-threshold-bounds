import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1704 = true := by
  decide +kernel

theorem tot1704 : totK PD2M8K2 D2M8K2.t1704 = [0, 0, 0, 234259871608, 476925466484, 157713815896, 7392259224, 0] := by
  decide +kernel

theorem rows1705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1705 = true := by
  decide +kernel

theorem tot1705 : totK PD2M8K2 D2M8K2.t1705 = [0, 0, 0, 173086024167, 460553078662, 205917004745, 16562973755, 0] := by
  decide +kernel

theorem rows1706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1706 = true := by
  decide +kernel

theorem tot1706 : totK PD2M8K2 D2M8K2.t1706 = [0, 0, 0, 236876456069, 480857582186, 157630441583, 5241237773, 0] := by
  decide +kernel

theorem rows1707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1707 = true := by
  decide +kernel

theorem tot1707 : totK PD2M8K2 D2M8K2.t1707 = [0, 0, 0, 174763876550, 467937568246, 215050015528, 12984760805, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
