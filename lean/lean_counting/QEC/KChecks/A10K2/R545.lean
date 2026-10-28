import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2180 = true := by
  decide +kernel

theorem tot2180 : totK PA10K2 A10K2.t2180 = [0, 255765480041, 1147289192944, 1854728899752, 1269200385573, 340031582748, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows2181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2181 = true := by
  decide +kernel

theorem tot2181 : totK PA10K2 A10K2.t2181 = [0, 538139220315, 2006467310065, 2112642380641, 525686394747, 18360023969, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2182 = true := by
  decide +kernel

theorem tot2182 : totK PA10K2 A10K2.t2182 = [474961062806, 1543997385067, 1614877989351, 855172850263, 367445602561, 43766171556, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2183 = true := by
  decide +kernel

theorem tot2183 : totK PA10K2 A10K2.t2183 = [371940607411, 1673170067682, 2140746469723, 766436701645, 56917291833, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
