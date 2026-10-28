import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9532 = true := by
  decide +kernel

theorem tot9532 : totK PD2M8K2 D2M8K2.t9532 = [0, 157466317739, 469470636258, 267750563203, 14536923408, 0, 0, 0] := by
  decide +kernel

theorem rows9533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9533 = true := by
  decide +kernel

theorem tot9533 : totK PD2M8K2 D2M8K2.t9533 = [0, 189646114883, 459659831334, 225408953413, 19933297727, 0, 0, 0] := by
  decide +kernel

theorem rows9534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9534 = true := by
  decide +kernel

theorem tot9534 : totK PD2M8K2 D2M8K2.t9534 = [0, 201560649714, 474945447718, 214633003572, 12183533023, 0, 0, 0] := by
  decide +kernel

theorem rows9535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9535 = true := by
  decide +kernel

theorem tot9535 : totK PD2M8K2 D2M8K2.t9535 = [0, 33867182543, 329263840290, 421780636120, 84490953441, 1162935789, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
