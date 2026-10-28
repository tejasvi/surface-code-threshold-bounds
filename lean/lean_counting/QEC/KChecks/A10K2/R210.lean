import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t840 = true := by
  decide +kernel

theorem tot840 : totK PA10K2 A10K2.t840 = [0, 0, 314430716854, 1360220109918, 1921721498946, 1009233293164, 163008563011, 5453062850, 0, 0] := by
  decide +kernel

theorem rows841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t841 = true := by
  decide +kernel

theorem tot841 : totK PA10K2 A10K2.t841 = [0, 0, 241538922767, 1404753155191, 2133144219796, 829404715907, 65721088393, 0, 0, 0] := by
  decide +kernel

theorem rows842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t842 = true := by
  decide +kernel

theorem tot842 : totK PA10K2 A10K2.t842 = [0, 0, 484578401630, 1578617415011, 1805042756245, 855773181695, 148580430375, 5685526223, 0, 0] := by
  decide +kernel

theorem rows843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t843 = true := by
  decide +kernel

theorem tot843 : totK PA10K2 A10K2.t843 = [0, 285766734819, 1183651144739, 1826761160044, 1331079454249, 414744201651, 31276155898, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
