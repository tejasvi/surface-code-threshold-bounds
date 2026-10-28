import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7748 = true := by
  decide +kernel

theorem tot7748 : totK PA10K2 A10K2.t7748 = [0, 0, 478711658477, 1822230568160, 2034689695354, 611979398264, 32819721446, 0, 0, 0] := by
  decide +kernel

theorem rows7749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7749 = true := by
  decide +kernel

theorem tot7749 : totK PA10K2 A10K2.t7749 = [0, 0, 0, 591101767362, 2034789401052, 1800543178312, 420364845927, 18682938825, 0, 0] := by
  decide +kernel

theorem rows7750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7750 = true := by
  decide +kernel

theorem tot7750 : totK PA10K2 A10K2.t7750 = [0, 0, 336573588205, 1375045609208, 2019518412301, 1100599384223, 147219368795, 0, 0, 0] := by
  decide +kernel

theorem rows7751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7751 = true := by
  decide +kernel

theorem tot7751 : totK PA10K2 A10K2.t7751 = [0, 0, 546573270266, 1946238668382, 1953075187208, 541758449271, 29617080014, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
