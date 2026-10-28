import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6428 = true := by
  decide +kernel

theorem tot6428 : totK PD2M8K2 D2M8K2.t6428 = [0, 164087661538, 446139441621, 278780477694, 29848111367, 0, 0, 0] := by
  decide +kernel

theorem rows6429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6429 = true := by
  decide +kernel

theorem tot6429 : totK PD2M8K2 D2M8K2.t6429 = [0, 107684864638, 415265981089, 340023276490, 36402181957, 0, 0, 0] := by
  decide +kernel

theorem rows6430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6430 = true := by
  decide +kernel

theorem tot6430 : totK PD2M8K2 D2M8K2.t6430 = [0, 0, 216753714128, 490275820369, 175608602486, 9583672031, 0, 0] := by
  decide +kernel

theorem rows6431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6431 = true := by
  decide +kernel

theorem tot6431 : totK PD2M8K2 D2M8K2.t6431 = [0, 152621159257, 430351041896, 289827904725, 33560000627, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
