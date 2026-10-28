import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2728 = true := by
  decide +kernel

theorem tot2728 : totK PA10K2 A10K2.t2728 = [0, 0, 456989374110, 1752071742853, 1875179924360, 501917436127, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows2729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2729 = true := by
  decide +kernel

theorem tot2729 : totK PA10K2 A10K2.t2729 = [0, 0, 528947255269, 1898283658430, 1846134524617, 393496107371, 12718857877, 0, 0, 0] := by
  decide +kernel

theorem rows2730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2730 = true := by
  decide +kernel

theorem tot2730 : totK PA10K2 A10K2.t2730 = [0, 0, 452061141222, 1791045539200, 1986321529129, 537150681339, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows2731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2731 = true := by
  decide +kernel

theorem tot2731 : totK PA10K2 A10K2.t2731 = [0, 0, 534561189226, 1841065349307, 1822763849601, 435154746870, 31169761322, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
