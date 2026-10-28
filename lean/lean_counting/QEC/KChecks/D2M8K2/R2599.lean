import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10396 = true := by
  decide +kernel

theorem tot10396 : totK PD2M8K2 D2M8K2.t10396 = [0, 0, 0, 185983305099, 474980411250, 190936690821, 10602025244, 0] := by
  decide +kernel

theorem rows10397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10397 = true := by
  decide +kernel

theorem tot10397 : totK PD2M8K2 D2M8K2.t10397 = [0, 0, 0, 249383212666, 498137323987, 144426002297, 4123791985, 0] := by
  decide +kernel

theorem rows10398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10398 = true := by
  decide +kernel

theorem tot10398 : totK PD2M8K2 D2M8K2.t10398 = [0, 0, 38479669074, 211785646482, 440243167831, 199577064803, 12810146349, 0] := by
  decide +kernel

theorem rows10399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10399 = true := by
  decide +kernel

theorem tot10399 : totK PD2M8K2 D2M8K2.t10399 = [0, 0, 173107615095, 453197582236, 271531688494, 27417369388, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
