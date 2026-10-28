import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13400 = true := by
  decide +kernel

theorem tot13400 : totK PD2M8K2 D2M8K2.t13400 = [0, 0, 0, 221091220110, 475279070368, 158968550811, 9602367571, 0] := by
  decide +kernel

theorem rows13401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13401 = true := by
  decide +kernel

theorem tot13401 : totK PD2M8K2 D2M8K2.t13401 = [0, 0, 133693195524, 379262469737, 289357417490, 71582613469, 3581949829, 0] := by
  decide +kernel

theorem rows13402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13402 = true := by
  decide +kernel

theorem tot13402 : totK PD2M8K2 D2M8K2.t13402 = [0, 0, 176752855571, 437417986607, 243321202240, 23299516178, 0, 0] := by
  decide +kernel

theorem rows13403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13403 = true := by
  decide +kernel

theorem tot13403 : totK PD2M8K2 D2M8K2.t13403 = [0, 0, 105029848458, 426150276714, 327120467173, 27783303540, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
