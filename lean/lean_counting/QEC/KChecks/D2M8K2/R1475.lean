import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5900 = true := by
  decide +kernel

theorem tot5900 : totK PD2M8K2 D2M8K2.t5900 = [176990743926, 455475323142, 268226584156, 27881952543, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5901 = true := by
  decide +kernel

theorem tot5901 : totK PD2M8K2 D2M8K2.t5901 = [178274373545, 467875313622, 236981776179, 13262355368, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5902 = true := by
  decide +kernel

theorem tot5902 : totK PD2M8K2 D2M8K2.t5902 = [0, 289854775168, 506464561616, 100155568178, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows5903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5903 = true := by
  decide +kernel

theorem tot5903 : totK PD2M8K2 D2M8K2.t5903 = [0, 226338688660, 494788635529, 164641450480, 5253830308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
