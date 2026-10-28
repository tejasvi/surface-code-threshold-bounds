import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3160 = true := by
  decide +kernel

theorem tot3160 : totK PA10K2 A10K2.t3160 = [0, 0, 435949150056, 1772228672182, 2050460959221, 706101439268, 51316193605, 0, 0, 0] := by
  decide +kernel

theorem rows3161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3161 = true := by
  decide +kernel

theorem tot3161 : totK PA10K2 A10K2.t3161 = [0, 0, 0, 618529901507, 2035330747136, 1683960196342, 301335283242, 11694325420, 0, 0] := by
  decide +kernel

theorem rows3162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3162 = true := by
  decide +kernel

theorem tot3162 : totK PA10K2 A10K2.t3162 = [0, 0, 536499385769, 1802862200169, 1840156514237, 613587609505, 56907511990, 0, 0, 0] := by
  decide +kernel

theorem rows3163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3163 = true := by
  decide +kernel

theorem tot3163 : totK PA10K2 A10K2.t3163 = [0, 0, 227773083334, 1277543058147, 2190043809548, 1181853182038, 116439546187, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
