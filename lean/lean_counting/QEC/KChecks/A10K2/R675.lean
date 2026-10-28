import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2700 = true := by
  decide +kernel

theorem tot2700 : totK PA10K2 A10K2.t2700 = [0, 0, 457082881951, 1758989221207, 1957843905844, 546423920863, 32520423844, 0, 0, 0] := by
  decide +kernel

theorem rows2701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2701 = true := by
  decide +kernel

theorem tot2701 : totK PA10K2 A10K2.t2701 = [0, 0, 428704360582, 1812098355713, 2034190211076, 565493021409, 32885668568, 0, 0, 0] := by
  decide +kernel

theorem rows2702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2702 = true := by
  decide +kernel

theorem tot2702 : totK PA10K2 A10K2.t2702 = [0, 0, 0, 492416473209, 1861202654742, 1684349253513, 415102825156, 30220878370, 0, 0] := by
  decide +kernel

theorem rows2703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2703 = true := by
  decide +kernel

theorem tot2703 : totK PA10K2 A10K2.t2703 = [0, 0, 478777902291, 1801205716547, 1926201376249, 500752697347, 31608797364, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
