import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3332 = true := by
  decide +kernel

theorem tot3332 : totK PA10K2 A10K2.t3332 = [0, 0, 613592017148, 2079271978837, 1924676088685, 441845029834, 13814447077, 0, 0, 0] := by
  decide +kernel

theorem rows3333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3333 = true := by
  decide +kernel

theorem tot3333 : totK PA10K2 A10K2.t3333 = [0, 0, 346934163333, 1516704134985, 2076133066155, 852518608825, 75643137603, 0, 0, 0] := by
  decide +kernel

theorem rows3334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3334 = true := by
  decide +kernel

theorem tot3334 : totK PA10K2 A10K2.t3334 = [0, 0, 498879068420, 1859211770968, 2020646880008, 540347374652, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows3335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3335 = true := by
  decide +kernel

theorem tot3335 : totK PA10K2 A10K2.t3335 = [0, 0, 0, 540221530729, 1904919736108, 1771310578841, 431471228844, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
