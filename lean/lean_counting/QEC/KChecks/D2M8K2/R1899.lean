import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7596 = true := by
  decide +kernel

theorem tot7596 : totK PD2M8K2 D2M8K2.t7596 = [0, 0, 280269698108, 509219035504, 101374519230, 1198073392, 0, 0] := by
  decide +kernel

theorem rows7597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7597 = true := by
  decide +kernel

theorem tot7597 : totK PD2M8K2 D2M8K2.t7597 = [0, 163880098198, 386497611676, 265136357558, 70722536387, 3581949829, 0, 0] := by
  decide +kernel

theorem rows7598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7598 = true := by
  decide +kernel

theorem tot7598 : totK PD2M8K2 D2M8K2.t7598 = [0, 171201470523, 437147688830, 277601898123, 30211536632, 0, 0, 0] := by
  decide +kernel

theorem rows7599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7599 = true := by
  decide +kernel

theorem tot7599 : totK PD2M8K2 D2M8K2.t7599 = [0, 102801270229, 422944757195, 332204513242, 31339061383, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
