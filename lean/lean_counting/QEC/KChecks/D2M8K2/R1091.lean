import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4364 = true := by
  decide +kernel

theorem tot4364 : totK PD2M8K2 D2M8K2.t4364 = [0, 0, 0, 93211394557, 432792380797, 350741550946, 23225176244, 0] := by
  decide +kernel

theorem rows4365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4365 = true := by
  decide +kernel

theorem tot4365 : totK PD2M8K2 D2M8K2.t4365 = [0, 0, 0, 0, 238764831560, 495766255248, 119391532717, 2465685039] := by
  decide +kernel

theorem rows4366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4366 = true := by
  decide +kernel

theorem tot4366 : totK PD2M8K2 D2M8K2.t4366 = [0, 135596534594, 290160129450, 94739693949, 67008251388, 199281688199, 104581546405, 7068066807] := by
  decide +kernel

theorem rows4367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4367 = true := by
  decide +kernel

theorem tot4367 : totK PD2M8K2 D2M8K2.t4367 = [0, 188338968742, 454434527468, 224863717522, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
