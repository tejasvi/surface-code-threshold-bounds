import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3412 = true := by
  decide +kernel

theorem tot3412 : totK PD2M8K2 D2M8K2.t3412 = [154627715334, 429807161700, 266572339161, 53775780448, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows3413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3413 = true := by
  decide +kernel

theorem tot3413 : totK PD2M8K2 D2M8K2.t3413 = [177179649323, 449159029776, 251596568295, 17258260316, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3414 = true := by
  decide +kernel

theorem tot3414 : totK PD2M8K2 D2M8K2.t3414 = [68433758957, 332547632598, 401379983344, 88518094065, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows3415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3415 = true := by
  decide +kernel

theorem tot3415 : totK PD2M8K2 D2M8K2.t3415 = [0, 206683241081, 480302842948, 178872028359, 9482920370, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
