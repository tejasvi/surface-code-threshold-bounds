import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1860 = true := by
  decide +kernel

theorem tot1860 : totK PD2M8K2 D2M8K2.t1860 = [0, 0, 0, 302320569578, 467880442820, 83709080711, 1206465782, 0] := by
  decide +kernel

theorem rows1861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1861 = true := by
  decide +kernel

theorem tot1861 : totK PD2M8K2 D2M8K2.t1861 = [0, 0, 95587989266, 403743669286, 364125257560, 35889372555, 0, 0] := by
  decide +kernel

theorem rows1862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1862 = true := by
  decide +kernel

theorem tot1862 : totK PD2M8K2 D2M8K2.t1862 = [0, 0, 222846115705, 487035138580, 183789725163, 8500385581, 0, 0] := by
  decide +kernel

theorem rows1863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1863 = true := by
  decide +kernel

theorem tot1863 : totK PD2M8K2 D2M8K2.t1863 = [0, 0, 172742953658, 473225622670, 229175152914, 13026492849, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
