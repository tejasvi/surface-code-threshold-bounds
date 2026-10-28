import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9380 = true := by
  decide +kernel

theorem tot9380 : totK PD2M8K2 D2M8K2.t9380 = [0, 188009352801, 463478164595, 239596415510, 16313785275, 0, 0, 0] := by
  decide +kernel

theorem rows9381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9381 = true := by
  decide +kernel

theorem tot9381 : totK PD2M8K2 D2M8K2.t9381 = [0, 62674259314, 331841546877, 406291940376, 86710703022, 1164319620, 0, 0] := by
  decide +kernel

theorem rows9382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9382 = true := by
  decide +kernel

theorem tot9382 : totK PD2M8K2 D2M8K2.t9382 = [0, 0, 195154727914, 485723729005, 185764113907, 10381813646, 0, 0] := by
  decide +kernel

theorem rows9383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9383 = true := by
  decide +kernel

theorem tot9383 : totK PD2M8K2 D2M8K2.t9383 = [0, 170510339919, 444866278357, 252395891850, 29424794885, 1503593968, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
