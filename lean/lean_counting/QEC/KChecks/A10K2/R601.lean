import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2404 = true := by
  decide +kernel

theorem tot2404 : totK PA10K2 A10K2.t2404 = [0, 495771531347, 1824684754419, 1942166012217, 630473364410, 106541490596, 5982052406, 0, 0, 0] := by
  decide +kernel

theorem rows2405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2405 = true := by
  decide +kernel

theorem tot2405 : totK PA10K2 A10K2.t2405 = [0, 319364795913, 1374396929906, 2064958897996, 1163063614857, 190554826153, 6585347165, 0, 0, 0] := by
  decide +kernel

theorem rows2406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2406 = true := by
  decide +kernel

theorem tot2406 : totK PA10K2 A10K2.t2406 = [0, 0, 613592017148, 2133032834274, 1956367527399, 384889563476, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows2407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2407 = true := by
  decide +kernel

theorem tot2407 : totK PA10K2 A10K2.t2407 = [0, 0, 422813247741, 1552302676834, 1972415100194, 833740622614, 75643137603, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
