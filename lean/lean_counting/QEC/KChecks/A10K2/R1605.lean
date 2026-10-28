import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6420 = true := by
  decide +kernel

theorem tot6420 : totK PA10K2 A10K2.t6420 = [149418554193, 666940645261, 1544541185170, 1843807462733, 759454141718, 61190578067, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6421 = true := by
  decide +kernel

theorem tot6421 : totK PA10K2 A10K2.t6421 = [533453343863, 1961258164261, 2020401859025, 551100707375, 31508796447, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6422 = true := by
  decide +kernel

theorem tot6422 : totK PA10K2 A10K2.t6422 = [0, 680814951733, 2114964639208, 1746439304337, 395329719943, 24527926574, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6423 = true := by
  decide +kernel

theorem tot6423 : totK PA10K2 A10K2.t6423 = [404541561496, 1584857323410, 2019692886340, 873484553041, 86853291742, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
