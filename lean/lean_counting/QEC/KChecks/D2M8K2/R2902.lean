import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11608 = true := by
  decide +kernel

theorem tot11608 : totK PD2M8K2 D2M8K2.t11608 = [36951561255, 328625792016, 440174263897, 96105754358, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows11609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11609 = true := by
  decide +kernel

theorem tot11609 : totK PD2M8K2 D2M8K2.t11609 = [0, 208837611809, 493275435763, 178684210802, 6291337398, 0, 0, 0] := by
  decide +kernel

theorem rows11610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11610 = true := by
  decide +kernel

theorem tot11610 : totK PD2M8K2 D2M8K2.t11610 = [0, 171524549832, 428294254920, 287349580711, 35306754531, 0, 0, 0] := by
  decide +kernel

theorem rows11611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11611 = true := by
  decide +kernel

theorem tot11611 : totK PD2M8K2 D2M8K2.t11611 = [0, 182682724113, 473010631177, 237199376780, 12893172668, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
