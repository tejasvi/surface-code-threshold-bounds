import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4284 = true := by
  decide +kernel

theorem tot4284 : totK PA10K2 A10K2.t4284 = [0, 0, 0, 575221393442, 1989583004631, 1892773234263, 418940217210, 11864432348, 0, 0] := by
  decide +kernel

theorem rows4285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4285 = true := by
  decide +kernel

theorem tot4285 : totK PA10K2 A10K2.t4285 = [0, 480036688775, 1560508115056, 1488543120065, 520634352918, 484022210686, 333952243856, 43132710386, 0, 0] := by
  decide +kernel

theorem rows4286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4286 = true := by
  decide +kernel

theorem tot4286 : totK PA10K2 A10K2.t4286 = [0, 388985532535, 1660649838822, 2032597552049, 710941749585, 51285196232, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4287 = true := by
  decide +kernel

theorem tot4287 : totK PA10K2 A10K2.t4287 = [0, 0, 522353630619, 1953478275968, 1782459053126, 415731021970, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
