import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12624 = true := by
  decide +kernel

theorem tot12624 : totK PD2M8K2 D2M8K2.t12624 = [0, 0, 154925078361, 457618706030, 257150401563, 16158654607, 0, 0] := by
  decide +kernel

theorem rows12625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12625 = true := by
  decide +kernel

theorem tot12625 : totK PD2M8K2 D2M8K2.t12625 = [0, 0, 195500273900, 469482732806, 226054923314, 14002713986, 0, 0] := by
  decide +kernel

theorem rows12626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12626 = true := by
  decide +kernel

theorem tot12626 : totK PD2M8K2 D2M8K2.t12626 = [0, 0, 203886317013, 479014783198, 207258715830, 8373438370, 0, 0] := by
  decide +kernel

theorem rows12627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12627 = true := by
  decide +kernel

theorem tot12627 : totK PD2M8K2 D2M8K2.t12627 = [0, 0, 187016182931, 484789637885, 226656444299, 15015916215, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
