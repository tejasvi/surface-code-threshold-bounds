import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8500 = true := by
  decide +kernel

theorem tot8500 : totK PD2M8K2 D2M8K2.t8500 = [173317023195, 466797486588, 245658003816, 14883319959, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8501 = true := by
  decide +kernel

theorem tot8501 : totK PD2M8K2 D2M8K2.t8501 = [0, 278280343856, 512601440416, 117247701726, 1190718505, 0, 0, 0] := by
  decide +kernel

theorem rows8502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8502 = true := by
  decide +kernel

theorem tot8502 : totK PD2M8K2 D2M8K2.t8502 = [29710971438, 211965139377, 432465911884, 185715149598, 12003981235, 0, 0, 0] := by
  decide +kernel

theorem rows8503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8503 = true := by
  decide +kernel

theorem tot8503 : totK PD2M8K2 D2M8K2.t8503 = [196177642464, 456943397994, 241237010627, 23437208677, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
