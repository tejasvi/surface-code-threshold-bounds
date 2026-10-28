import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t980 = true := by
  decide +kernel

theorem tot980 : totK PD2M8K2 D2M8K2.t980 = [0, 90799776962, 391703996136, 371656551109, 39005530167, 0, 0, 0] := by
  decide +kernel

theorem rows981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t981 = true := by
  decide +kernel

theorem tot981 : totK PD2M8K2 D2M8K2.t981 = [0, 203220328518, 465925705468, 223026787539, 15714221421, 0, 0, 0] := by
  decide +kernel

theorem rows982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t982 = true := by
  decide +kernel

theorem tot982 : totK PD2M8K2 D2M8K2.t982 = [0, 172632600336, 479706439452, 226616628986, 14343232116, 0, 0, 0] := by
  decide +kernel

theorem rows983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t983 = true := by
  decide +kernel

theorem tot983 : totK PD2M8K2 D2M8K2.t983 = [0, 179841446684, 464042819278, 248054374458, 20821767404, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
