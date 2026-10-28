import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6460 = true := by
  decide +kernel

theorem tot6460 : totK PA10K2 A10K2.t6460 = [0, 0, 560078929193, 1970173869891, 2008708385033, 525567792965, 18515547658, 0, 0, 0] := by
  decide +kernel

theorem rows6461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6461 = true := by
  decide +kernel

theorem tot6461 : totK PA10K2 A10K2.t6461 = [0, 282573750534, 1054659233667, 1614479334225, 1460460239597, 561134866914, 50432252117, 0, 0, 0] := by
  decide +kernel

theorem rows6462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6462 = true := by
  decide +kernel

theorem tot6462 : totK PA10K2 A10K2.t6462 = [0, 399796758777, 1716385805369, 2164766758738, 771085440296, 55926926292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6463 = true := by
  decide +kernel

theorem tot6463 : totK PA10K2 A10K2.t6463 = [0, 73665327754, 691957574366, 2017226144782, 1799769163520, 386877044251, 11991740650, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
