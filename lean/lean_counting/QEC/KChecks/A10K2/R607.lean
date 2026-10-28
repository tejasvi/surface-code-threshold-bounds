import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2428 = true := by
  decide +kernel

theorem tot2428 : totK PA10K2 A10K2.t2428 = [0, 0, 330021797788, 1551528499699, 2199069570709, 865756539741, 62972848401, 0, 0, 0] := by
  decide +kernel

theorem rows2429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2429 = true := by
  decide +kernel

theorem tot2429 : totK PA10K2 A10K2.t2429 = [0, 0, 0, 568475417970, 1988674565742, 1864042942578, 394224561704, 12224107035, 0, 0] := by
  decide +kernel

theorem rows2430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2430 = true := by
  decide +kernel

theorem tot2430 : totK PA10K2 A10K2.t2430 = [317769054122, 844269817712, 474858316785, 301768961900, 1078811362946, 1354449336259, 522441368230, 48886019071, 0, 0] := by
  decide +kernel

theorem rows2431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2431 = true := by
  decide +kernel

theorem tot2431 : totK PA10K2 A10K2.t2431 = [478252128092, 1766590866237, 1951909274676, 567375461276, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
