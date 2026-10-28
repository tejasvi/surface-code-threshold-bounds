import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10460 = true := by
  decide +kernel

theorem tot10460 : totK PD2M8K2 D2M8K2.t10460 = [0, 0, 159301758742, 475847694047, 250974253433, 10300574625, 0, 0] := by
  decide +kernel

theorem rows10461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10461 = true := by
  decide +kernel

theorem tot10461 : totK PD2M8K2 D2M8K2.t10461 = [0, 0, 0, 283665376354, 481662162514, 88934116962, 2051644177, 0] := by
  decide +kernel

theorem rows10462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10462 = true := by
  decide +kernel

theorem tot10462 : totK PD2M8K2 D2M8K2.t10462 = [0, 0, 171777442350, 422760487669, 248830277024, 43127978870, 2481160468, 0] := by
  decide +kernel

theorem rows10463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10463 = true := by
  decide +kernel

theorem tot10463 : totK PD2M8K2 D2M8K2.t10463 = [0, 0, 180894072074, 477867851191, 238669324663, 14141968071, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
