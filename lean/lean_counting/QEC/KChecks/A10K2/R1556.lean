import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6224 = true := by
  decide +kernel

theorem tot6224 : totK PA10K2 A10K2.t6224 = [0, 0, 0, 483845271627, 1804198686476, 1814395960486, 470905451996, 31193230065, 0, 0] := by
  decide +kernel

theorem rows6225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6225 = true := by
  decide +kernel

theorem tot6225 : totK PA10K2 A10K2.t6225 = [0, 0, 0, 728909611810, 2184006740491, 1528664435781, 245978120846, 6354603908, 0, 0] := by
  decide +kernel

theorem rows6226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6226 = true := by
  decide +kernel

theorem tot6226 : totK PA10K2 A10K2.t6226 = [0, 0, 0, 477277194775, 1798004700431, 1780134203446, 465871158255, 31009878902, 0, 0] := by
  decide +kernel

theorem rows6227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6227 = true := by
  decide +kernel

theorem tot6227 : totK PA10K2 A10K2.t6227 = [0, 0, 0, 536654557051, 1931634496276, 1754000980426, 367622713444, 5903815910, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
