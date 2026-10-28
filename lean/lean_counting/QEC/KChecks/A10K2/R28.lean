import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t112 = true := by
  decide +kernel

theorem tot112 : totK PA10K2 A10K2.t112 = [0, 425786204918, 1748564812132, 2024523870697, 598200229714, 33739454647, 0, 0, 0, 0] := by
  decide +kernel

theorem rows113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t113 = true := by
  decide +kernel

theorem tot113 : totK PA10K2 A10K2.t113 = [0, 551440326330, 1883089344885, 1817580957995, 457884306893, 18754734689, 0, 0, 0, 0] := by
  decide +kernel

theorem rows114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t114 = true := by
  decide +kernel

theorem tot114 : totK PA10K2 A10K2.t114 = [0, 438441308029, 1586815314367, 1862040369709, 590140247038, 50267370225, 0, 0, 0, 0] := by
  decide +kernel

theorem rows115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t115 = true := by
  decide +kernel

theorem tot115 : totK PA10K2 A10K2.t115 = [0, 170006815986, 1389810891629, 2205090041950, 807609130686, 58503570348, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
