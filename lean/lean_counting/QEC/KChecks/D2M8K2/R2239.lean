import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8956 = true := by
  decide +kernel

theorem tot8956 : totK PD2M8K2 D2M8K2.t8956 = [172522045356, 442806556551, 274473971334, 30374593025, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8957 = true := by
  decide +kernel

theorem tot8957 : totK PD2M8K2 D2M8K2.t8957 = [128179878783, 445085609362, 305642995414, 23428317185, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8958 = true := by
  decide +kernel

theorem tot8958 : totK PD2M8K2 D2M8K2.t8958 = [0, 202680870014, 480090867797, 192289474017, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows8959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8959 = true := by
  decide +kernel

theorem tot8959 : totK PD2M8K2 D2M8K2.t8959 = [85741851239, 320422754796, 379208020241, 102231853300, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
