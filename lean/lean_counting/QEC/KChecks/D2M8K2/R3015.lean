import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12060 = true := by
  decide +kernel

theorem tot12060 : totK PD2M8K2 D2M8K2.t12060 = [0, 0, 170058384553, 463125146347, 221660350846, 13809284570, 0, 0] := by
  decide +kernel

theorem rows12061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12061 = true := by
  decide +kernel

theorem tot12061 : totK PD2M8K2 D2M8K2.t12061 = [0, 0, 199374969255, 507243012741, 161213708700, 2396478222, 0, 0] := by
  decide +kernel

theorem rows12062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12062 = true := by
  decide +kernel

theorem tot12062 : totK PD2M8K2 D2M8K2.t12062 = [0, 0, 189760994422, 464267284793, 200772056779, 12299451732, 0, 0] := by
  decide +kernel

theorem rows12063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12063 = true := by
  decide +kernel

theorem tot12063 : totK PD2M8K2 D2M8K2.t12063 = [0, 0, 217589266385, 485385926192, 183875050919, 5316431581, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
