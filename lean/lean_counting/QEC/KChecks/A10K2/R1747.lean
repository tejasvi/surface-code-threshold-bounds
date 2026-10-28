import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6988 = true := by
  decide +kernel

theorem tot6988 : totK PA10K2 A10K2.t6988 = [0, 0, 0, 0, 867299815209, 2223836646302, 1460934509619, 260737492887, 7380853412, 0] := by
  decide +kernel

theorem rows6989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6989 = true := by
  decide +kernel

theorem tot6989 : totK PA10K2 A10K2.t6989 = [0, 0, 0, 392124710355, 1646642082145, 1974072451937, 644015791771, 49486008595, 0, 0] := by
  decide +kernel

theorem rows6990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6990 = true := by
  decide +kernel

theorem tot6990 : totK PA10K2 A10K2.t6990 = [0, 0, 0, 669750889046, 2065587262847, 1751259373641, 366725255996, 18660999360, 0, 0] := by
  decide +kernel

theorem rows6991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6991 = true := by
  decide +kernel

theorem tot6991 : totK PA10K2 A10K2.t6991 = [0, 0, 304922396905, 991223111756, 1629517691870, 1555609733033, 506412516830, 31276155898, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
