import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3960 = true := by
  decide +kernel

theorem tot3960 : totK PD2M8K2 D2M8K2.t3960 = [0, 102988344640, 348223495004, 340202464361, 82737363318, 3821179711, 0, 0] := by
  decide +kernel

theorem rows3961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3961 = true := by
  decide +kernel

theorem tot3961 : totK PD2M8K2 D2M8K2.t3961 = [0, 180747177171, 444912759030, 257334501864, 26801037403, 0, 0, 0] := by
  decide +kernel

theorem rows3962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3962 = true := by
  decide +kernel

theorem tot3962 : totK PD2M8K2 D2M8K2.t3962 = [0, 138278827267, 446760932928, 304193954170, 26400250240, 0, 0, 0] := by
  decide +kernel

theorem rows3963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3963 = true := by
  decide +kernel

theorem tot3963 : totK PD2M8K2 D2M8K2.t3963 = [0, 0, 218150450330, 479257204450, 169508877647, 4899206309, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
