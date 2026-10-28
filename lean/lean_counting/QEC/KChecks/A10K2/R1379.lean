import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5516 = true := by
  decide +kernel

theorem tot5516 : totK PA10K2 A10K2.t5516 = [0, 62072124316, 1044055297281, 2318870284208, 1220926481478, 100176369962, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5517 = true := by
  decide +kernel

theorem tot5517 : totK PA10K2 A10K2.t5517 = [0, 487223217921, 1750363298794, 1896870589817, 734198864943, 137232861136, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5518 = true := by
  decide +kernel

theorem tot5518 : totK PA10K2 A10K2.t5518 = [0, 316779408161, 1399808969161, 2090881618562, 1147480126497, 186239200380, 6851704726, 0, 0, 0] := by
  decide +kernel

theorem rows5519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5519 = true := by
  decide +kernel

theorem tot5519 : totK PA10K2 A10K2.t5519 = [0, 0, 611006629396, 2121634955515, 1951295462117, 378022650224, 6962742351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
