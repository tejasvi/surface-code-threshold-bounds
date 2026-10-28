import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7336 = true := by
  decide +kernel

theorem tot7336 : totK PD2M8K2 D2M8K2.t7336 = [0, 0, 0, 223942379624, 491472387293, 153459166760, 5218872685, 0] := by
  decide +kernel

theorem rows7337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7337 = true := by
  decide +kernel

theorem tot7337 : totK PD2M8K2 D2M8K2.t7337 = [0, 0, 169495686935, 436663680604, 267073718540, 32576700726, 0, 0] := by
  decide +kernel

theorem rows7338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7338 = true := by
  decide +kernel

theorem tot7338 : totK PD2M8K2 D2M8K2.t7338 = [0, 0, 187008977517, 457741850191, 228293722089, 15348631570, 0, 0] := by
  decide +kernel

theorem rows7339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7339 = true := by
  decide +kernel

theorem tot7339 : totK PD2M8K2 D2M8K2.t7339 = [0, 0, 55818802401, 400853763487, 407537769638, 39058576355, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
