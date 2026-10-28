import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4228 = true := by
  decide +kernel

theorem tot4228 : totK PA10K2 A10K2.t4228 = [0, 952010132921, 2321584019838, 1304965343602, 141955370908, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4229 = true := by
  decide +kernel

theorem tot4229 : totK PA10K2 A10K2.t4229 = [486355993374, 1758431358407, 1897657505124, 724900359245, 145533633098, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4230 = true := by
  decide +kernel

theorem tot4230 : totK PA10K2 A10K2.t4230 = [316555443509, 1489058847540, 2185866018706, 981049101971, 83890711425, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4231 = true := by
  decide +kernel

theorem tot4231 : totK PA10K2 A10K2.t4231 = [0, 506961210690, 2004003444450, 2140917999991, 500979732224, 13814455608, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
