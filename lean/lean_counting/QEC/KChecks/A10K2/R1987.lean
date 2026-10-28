import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7948 = true := by
  decide +kernel

theorem tot7948 : totK PA10K2 A10K2.t7948 = [0, 0, 170431082261, 1249852537808, 2238165293969, 956320865725, 79235116675, 0, 0, 0] := by
  decide +kernel

theorem rows7949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7949 = true := by
  decide +kernel

theorem tot7949 : totK PA10K2 A10K2.t7949 = [0, 0, 509649593070, 1760096295099, 1919367917923, 706518243186, 74289527556, 0, 0, 0] := by
  decide +kernel

theorem rows7950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7950 = true := by
  decide +kernel

theorem tot7950 : totK PA10K2 A10K2.t7950 = [0, 0, 320910162593, 1540379751701, 2193476098898, 939111598681, 75078776682, 0, 0, 0] := by
  decide +kernel

theorem rows7951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7951 = true := by
  decide +kernel

theorem tot7951 : totK PA10K2 A10K2.t7951 = [0, 0, 0, 581603275832, 2076691741508, 2063057139359, 449452490125, 13229391832, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
