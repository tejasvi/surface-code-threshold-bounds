import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2144 = true := by
  decide +kernel

theorem tot2144 : totK PD2M8K2 D2M8K2.t2144 = [0, 177279051382, 462687851405, 244149700443, 15269883583, 0, 0, 0] := by
  decide +kernel

theorem rows2145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2145 = true := by
  decide +kernel

theorem tot2145 : totK PD2M8K2 D2M8K2.t2145 = [0, 68961823636, 333501132224, 407905456298, 84487657442, 1163840124, 0, 0] := by
  decide +kernel

theorem rows2146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2146 = true := by
  decide +kernel

theorem tot2146 : totK PD2M8K2 D2M8K2.t2146 = [0, 0, 200730436262, 464673069322, 188697021386, 11873025674, 0, 0] := by
  decide +kernel

theorem rows2147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2147 = true := by
  decide +kernel

theorem tot2147 : totK PD2M8K2 D2M8K2.t2147 = [0, 156251266633, 437046398904, 286314115309, 38854134200, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
