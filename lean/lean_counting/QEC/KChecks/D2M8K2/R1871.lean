import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7484 = true := by
  decide +kernel

theorem tot7484 : totK PD2M8K2 D2M8K2.t7484 = [0, 205795088613, 495789231414, 180258669227, 3633710624, 0, 0, 0] := by
  decide +kernel

theorem rows7485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7485 = true := by
  decide +kernel

theorem tot7485 : totK PD2M8K2 D2M8K2.t7485 = [0, 82799466859, 362547853541, 366854550014, 69369399455, 1198073392, 0, 0] := by
  decide +kernel

theorem rows7486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7486 = true := by
  decide +kernel

theorem tot7486 : totK PD2M8K2 D2M8K2.t7486 = [0, 36594270515, 285409020475, 444745793635, 109535848383, 3581949829, 0, 0] := by
  decide +kernel

theorem rows7487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7487 = true := by
  decide +kernel

theorem tot7487 : totK PD2M8K2 D2M8K2.t7487 = [0, 205271043488, 464935184659, 219056709959, 17114470299, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
