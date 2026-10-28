import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10036 = true := by
  decide +kernel

theorem tot10036 : totK PD2M8K2 D2M8K2.t10036 = [0, 176348708448, 455316946268, 267056045704, 26336884798, 0, 0, 0] := by
  decide +kernel

theorem rows10037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10037 = true := by
  decide +kernel

theorem tot10037 : totK PD2M8K2 D2M8K2.t10037 = [0, 179781219229, 468098633468, 247095475621, 14045663379, 0, 0, 0] := by
  decide +kernel

theorem rows10038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10038 = true := by
  decide +kernel

theorem tot10038 : totK PD2M8K2 D2M8K2.t10038 = [0, 0, 265157565192, 503011388769, 123381584165, 1260002070, 0, 0] := by
  decide +kernel

theorem rows10039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10039 = true := by
  decide +kernel

theorem tot10039 : totK PD2M8K2 D2M8K2.t10039 = [0, 0, 178779249288, 480505127285, 213221062821, 7360082600, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
