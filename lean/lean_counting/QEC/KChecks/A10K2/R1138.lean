import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4552 = true := by
  decide +kernel

theorem tot4552 : totK PA10K2 A10K2.t4552 = [0, 510020427707, 1871884400920, 1974952247052, 584108505071, 32712955001, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4553 = true := by
  decide +kernel

theorem tot4553 : totK PA10K2 A10K2.t4553 = [557742759892, 1666077222561, 1564149658024, 726070054638, 274687557688, 37055555776, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4554 = true := by
  decide +kernel

theorem tot4554 : totK PA10K2 A10K2.t4554 = [93946978215, 965582202992, 2030506529924, 1332031793724, 329503767152, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4555 = true := by
  decide +kernel

theorem tot4555 : totK PA10K2 A10K2.t4555 = [299638544946, 1273949987313, 1897309709275, 1124543991756, 192670179926, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
