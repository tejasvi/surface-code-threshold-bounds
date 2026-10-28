import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6048 = true := by
  decide +kernel

theorem tot6048 : totK PA10K2 A10K2.t6048 = [0, 105046183223, 659784994842, 1832359202814, 1765120898458, 484111165004, 31082886609, 0, 0, 0] := by
  decide +kernel

theorem rows6049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6049 = true := by
  decide +kernel

theorem tot6049 : totK PA10K2 A10K2.t6049 = [0, 494258760089, 1931333205724, 2085545325811, 586202468260, 31878007351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6050 = true := by
  decide +kernel

theorem tot6050 : totK PA10K2 A10K2.t6050 = [300827602965, 1141044967954, 1632267919959, 1375034193694, 552644959800, 50555834002, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6051 = true := by
  decide +kernel

theorem tot6051 : totK PA10K2 A10K2.t6051 = [476997066642, 1771564283741, 1972993588815, 635961863580, 38659061916, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
