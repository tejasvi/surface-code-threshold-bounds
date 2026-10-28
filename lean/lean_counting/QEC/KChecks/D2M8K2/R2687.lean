import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10748 = true := by
  decide +kernel

theorem tot10748 : totK PD2M8K2 D2M8K2.t10748 = [0, 0, 169712875662, 442746950174, 228751958264, 36278476485, 2481160468, 0] := by
  decide +kernel

theorem rows10749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10749 = true := by
  decide +kernel

theorem tot10749 : totK PD2M8K2 D2M8K2.t10749 = [0, 0, 180462386115, 456554263625, 255618478480, 15183549182, 0, 0] := by
  decide +kernel

theorem rows10750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10750 = true := by
  decide +kernel

theorem tot10750 : totK PD2M8K2 D2M8K2.t10750 = [0, 0, 67023594919, 334743866655, 389066558289, 76569177125, 1162740214, 0] := by
  decide +kernel

theorem rows10751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10751 = true := by
  decide +kernel

theorem tot10751 : totK PD2M8K2 D2M8K2.t10751 = [0, 0, 0, 222905043415, 488204447166, 157163247715, 9377642247, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
