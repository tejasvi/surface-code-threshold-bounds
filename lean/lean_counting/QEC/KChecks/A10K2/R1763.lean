import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7052 = true := by
  decide +kernel

theorem tot7052 : totK PA10K2 A10K2.t7052 = [0, 0, 362637740926, 1570344489313, 2052494357009, 735063140744, 44911952905, 0, 0, 0] := by
  decide +kernel

theorem rows7053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7053 = true := by
  decide +kernel

theorem tot7053 : totK PA10K2 A10K2.t7053 = [0, 0, 537680587155, 1936197903520, 2032793877453, 576472069352, 29323168872, 0, 0, 0] := by
  decide +kernel

theorem rows7054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7054 = true := by
  decide +kernel

theorem tot7054 : totK PA10K2 A10K2.t7054 = [0, 0, 0, 718313165729, 2211823427531, 1779080631862, 291026911269, 6853348008, 0, 0] := by
  decide +kernel

theorem rows7055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7055 = true := by
  decide +kernel

theorem tot7055 : totK PA10K2 A10K2.t7055 = [0, 0, 0, 435961472680, 1729470190718, 2129957118897, 734532857444, 55498468803, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
