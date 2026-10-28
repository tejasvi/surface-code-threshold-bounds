import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15984 = true := by
  decide +kernel

theorem tot15984 : totK PD2M8K2 D2M8K2.t15984 = [0, 0, 93059647579, 321811835044, 396210948242, 119135980076, 4239164426, 0] := by
  decide +kernel

theorem rows15985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15985 = true := by
  decide +kernel

theorem tot15985 : totK PD2M8K2 D2M8K2.t15985 = [0, 0, 233245503741, 510378847776, 182062825739, 6903410822, 0, 0] := by
  decide +kernel

theorem rows15986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15986 = true := by
  decide +kernel

theorem tot15986 : totK PD2M8K2 D2M8K2.t15986 = [0, 0, 177199076169, 447340416278, 264099060037, 28320750861, 0, 0] := by
  decide +kernel

theorem rows15987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15987 = true := by
  decide +kernel

theorem tot15987 : totK PD2M8K2 D2M8K2.t15987 = [0, 0, 193434792684, 478352873742, 220255041609, 12426737048, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
