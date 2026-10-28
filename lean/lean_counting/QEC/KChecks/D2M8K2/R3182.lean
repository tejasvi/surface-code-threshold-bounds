import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12728 = true := by
  decide +kernel

theorem tot12728 : totK PD2M8K2 D2M8K2.t12728 = [0, 197357913640, 462901326448, 245162291823, 23437208677, 0, 0, 0] := by
  decide +kernel

theorem rows12729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12729 = true := by
  decide +kernel

theorem tot12729 : totK PD2M8K2 D2M8K2.t12729 = [0, 176545455323, 462108647163, 240516922069, 17012752274, 0, 0, 0] := by
  decide +kernel

theorem rows12730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12730 = true := by
  decide +kernel

theorem tot12730 : totK PD2M8K2 D2M8K2.t12730 = [0, 11585800147, 337790613512, 476084958009, 80086095527, 0, 0, 0] := by
  decide +kernel

theorem rows12731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12731 = true := by
  decide +kernel

theorem tot12731 : totK PD2M8K2 D2M8K2.t12731 = [0, 52008946557, 294635632370, 427466431955, 111503889334, 3867150671, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
