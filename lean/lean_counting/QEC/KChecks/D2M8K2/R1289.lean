import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5156 = true := by
  decide +kernel

theorem tot5156 : totK PD2M8K2 D2M8K2.t5156 = [0, 0, 176664425682, 456619862815, 260602400318, 22647650083, 0, 0] := by
  decide +kernel

theorem rows5157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5157 = true := by
  decide +kernel

theorem tot5157 : totK PD2M8K2 D2M8K2.t5157 = [0, 0, 0, 286221858687, 509325917705, 111775680066, 1391126877, 0] := by
  decide +kernel

theorem rows5158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5158 = true := by
  decide +kernel

theorem tot5158 : totK PD2M8K2 D2M8K2.t5158 = [0, 0, 194967642921, 461186101090, 215682892425, 13254840988, 0, 0] := by
  decide +kernel

theorem rows5159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5159 = true := by
  decide +kernel

theorem tot5159 : totK PD2M8K2 D2M8K2.t5159 = [0, 0, 177991243676, 476350414719, 222867416159, 13795945806, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
