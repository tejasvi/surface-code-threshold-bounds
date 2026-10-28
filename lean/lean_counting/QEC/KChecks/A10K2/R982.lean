import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3928 = true := by
  decide +kernel

theorem tot3928 : totK PA10K2 A10K2.t3928 = [0, 77056708891, 758055728046, 2115056835534, 1494448364772, 232559440798, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3929 = true := by
  decide +kernel

theorem tot3929 : totK PA10K2 A10K2.t3929 = [0, 496504212815, 1902049046342, 2034389865125, 577632647623, 37591497070, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3930 = true := by
  decide +kernel

theorem tot3930 : totK PA10K2 A10K2.t3930 = [0, 226651756384, 1239191583248, 2106227981694, 1302642913914, 239012524975, 6840736825, 0, 0, 0] := by
  decide +kernel

theorem rows3931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3931 = true := by
  decide +kernel

theorem tot3931 : totK PA10K2 A10K2.t3931 = [0, 0, 497468715910, 1958241861961, 2040917689044, 515705356829, 18784622171, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
