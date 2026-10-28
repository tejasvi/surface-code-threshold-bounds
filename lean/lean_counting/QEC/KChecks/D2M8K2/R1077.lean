import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4308 = true := by
  decide +kernel

theorem tot4308 : totK PD2M8K2 D2M8K2.t4308 = [0, 0, 0, 175758509236, 493594453389, 219739704603, 7994456143, 0] := by
  decide +kernel

theorem rows4309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4309 = true := by
  decide +kernel

theorem tot4309 : totK PD2M8K2 D2M8K2.t4309 = [0, 0, 124865311629, 326428605056, 290512837901, 143801093923, 8100177866, 0] := by
  decide +kernel

theorem rows4310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4310 = true := by
  decide +kernel

theorem tot4310 : totK PD2M8K2 D2M8K2.t4310 = [0, 0, 166028451884, 439778943739, 275688414775, 30368503698, 0, 0] := by
  decide +kernel

theorem rows4311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4311 = true := by
  decide +kernel

theorem tot4311 : totK PD2M8K2 D2M8K2.t4311 = [0, 0, 121020578952, 422879915952, 316628994374, 28326424969, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
