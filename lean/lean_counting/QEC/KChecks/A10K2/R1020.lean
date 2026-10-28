import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4080 = true := by
  decide +kernel

theorem tot4080 : totK PA10K2 A10K2.t4080 = [0, 0, 0, 269216628779, 1386240144147, 2159122419800, 1048455806582, 109301608682, 0, 0] := by
  decide +kernel

theorem rows4081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4081 = true := by
  decide +kernel

theorem tot4081 : totK PA10K2 A10K2.t4081 = [0, 0, 0, 0, 599145896583, 2037251213678, 1840076253160, 360997753874, 12132367858, 0] := by
  decide +kernel

theorem rows4082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4082 = true := by
  decide +kernel

theorem tot4082 : totK PA10K2 A10K2.t4082 = [362393616899, 1215273910193, 1264746725495, 371785901254, 25686058060, 312585060820, 838925398534, 488280079436, 48886019071, 0] := by
  decide +kernel

theorem rows4083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4083 = true := by
  decide +kernel

theorem tot4083 : totK PA10K2 A10K2.t4083 = [507590503662, 1888034400267, 1895510399266, 507540830839, 14644072143, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
