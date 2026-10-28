import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4376 = true := by
  decide +kernel

theorem tot4376 : totK PA10K2 A10K2.t4376 = [0, 415783568414, 1485943197526, 1767003737176, 991837015486, 190867043508, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4377 = true := by
  decide +kernel

theorem tot4377 : totK PA10K2 A10K2.t4377 = [0, 363036227506, 1635006180440, 2118014949411, 678092630412, 47517416364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4378 = true := by
  decide +kernel

theorem tot4378 : totK PA10K2 A10K2.t4378 = [0, 0, 752301390356, 2191280358570, 1548048224867, 254074053126, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4379 = true := by
  decide +kernel

theorem tot4379 : totK PA10K2 A10K2.t4379 = [0, 0, 492770718185, 1920526031658, 1901146423973, 447583290839, 26261546811, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
