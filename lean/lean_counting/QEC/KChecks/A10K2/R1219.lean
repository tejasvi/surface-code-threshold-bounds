import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4876 = true := by
  decide +kernel

theorem tot4876 : totK PA10K2 A10K2.t4876 = [0, 423256289305, 1398733919516, 1675287458070, 1084784550507, 358491540499, 29010686974, 0, 0, 0] := by
  decide +kernel

theorem rows4877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4877 = true := by
  decide +kernel

theorem tot4877 : totK PA10K2 A10K2.t4877 = [0, 342554709776, 1611810864522, 2063706449936, 742085048597, 56233027364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4878 = true := by
  decide +kernel

theorem tot4878 : totK PA10K2 A10K2.t4878 = [0, 0, 511824592845, 1850884652557, 1810517824514, 475766332390, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows4879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4879 = true := by
  decide +kernel

theorem tot4879 : totK PA10K2 A10K2.t4879 = [0, 558195267532, 1747506128250, 1805424170927, 690715566898, 65025152198, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
