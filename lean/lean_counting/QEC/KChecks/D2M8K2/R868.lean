import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3472 = true := by
  decide +kernel

theorem tot3472 : totK PD2M8K2 D2M8K2.t3472 = [132447351264, 430087736569, 302847532119, 26883910990, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3473 = true := by
  decide +kernel

theorem tot3473 : totK PD2M8K2 D2M8K2.t3473 = [0, 278662705801, 500537456907, 108417454934, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3474 = true := by
  decide +kernel

theorem tot3474 : totK PD2M8K2 D2M8K2.t3474 = [182124285284, 439081268208, 278241231006, 33121375056, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3475 = true := by
  decide +kernel

theorem tot3475 : totK PD2M8K2 D2M8K2.t3475 = [167200204354, 464302722843, 254783885806, 18339826511, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
