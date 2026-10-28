import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5184 = true := by
  decide +kernel

theorem tot5184 : totK PA10K2 A10K2.t5184 = [0, 0, 773517450529, 2215124084217, 1674596020455, 294699642919, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5185 = true := by
  decide +kernel

theorem tot5185 : totK PA10K2 A10K2.t5185 = [0, 0, 473920424776, 1768189614083, 1959689468159, 644735576447, 41382718353, 0, 0, 0] := by
  decide +kernel

theorem rows5186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5186 = true := by
  decide +kernel

theorem tot5186 : totK PA10K2 A10K2.t5186 = [0, 0, 464789538467, 1788119993108, 1943462314646, 508539538633, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows5187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5187 = true := by
  decide +kernel

theorem tot5187 : totK PA10K2 A10K2.t5187 = [0, 0, 244737982367, 1307915605398, 2096859015094, 1078036505997, 165438730058, 14945844243, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
