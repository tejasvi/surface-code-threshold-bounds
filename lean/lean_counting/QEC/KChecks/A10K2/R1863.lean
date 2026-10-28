import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7452 = true := by
  decide +kernel

theorem tot7452 : totK PA10K2 A10K2.t7452 = [0, 0, 506208790771, 1825081034057, 1847394127178, 471046107685, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows7453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7453 = true := by
  decide +kernel

theorem tot7453 : totK PA10K2 A10K2.t7453 = [0, 0, 182187517013, 1447759700511, 2229284512429, 747672653817, 44493944182, 0, 0, 0] := by
  decide +kernel

theorem rows7454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7454 = true := by
  decide +kernel

theorem tot7454 : totK PA10K2 A10K2.t7454 = [0, 493970807510, 1413187190387, 1273840125903, 920179023736, 693309330947, 152273144889, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7455 = true := by
  decide +kernel

theorem tot7455 : totK PA10K2 A10K2.t7455 = [0, 0, 935224799999, 2372576508317, 1580043471505, 277403432658, 13285547580, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
