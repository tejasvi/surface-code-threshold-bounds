import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2772 = true := by
  decide +kernel

theorem tot2772 : totK PA10K2 A10K2.t2772 = [0, 294587680144, 1227294018726, 1913106090203, 1111770679884, 180161422619, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows2773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2773 = true := by
  decide +kernel

theorem tot2773 : totK PA10K2 A10K2.t2773 = [0, 504368969528, 1918152354508, 2115292723360, 581442130364, 19836780544, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2774 = true := by
  decide +kernel

theorem tot2774 : totK PA10K2 A10K2.t2774 = [479461498523, 1645786447805, 1709178060875, 753793833645, 280139935688, 37646807062, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2775 = true := by
  decide +kernel

theorem tot2775 : totK PA10K2 A10K2.t2775 = [304479794002, 1466725264667, 2159891491902, 958057288943, 83518355677, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
