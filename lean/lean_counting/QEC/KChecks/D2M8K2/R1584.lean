import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6336 = true := by
  decide +kernel

theorem tot6336 : totK PD2M8K2 D2M8K2.t6336 = [0, 0, 175529028913, 480841249134, 227891647319, 7716189290, 0, 0] := by
  decide +kernel

theorem rows6337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6337 = true := by
  decide +kernel

theorem tot6337 : totK PD2M8K2 D2M8K2.t6337 = [0, 182365284731, 442375423367, 245931111540, 45965742936, 4409629813, 0, 0] := by
  decide +kernel

theorem rows6338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6338 = true := by
  decide +kernel

theorem tot6338 : totK PD2M8K2 D2M8K2.t6338 = [0, 187871000363, 472754754000, 224485902630, 12313560678, 0, 0, 0] := by
  decide +kernel

theorem rows6339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6339 = true := by
  decide +kernel

theorem tot6339 : totK PD2M8K2 D2M8K2.t6339 = [0, 52264778997, 373028167674, 433138884403, 59818121024, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
