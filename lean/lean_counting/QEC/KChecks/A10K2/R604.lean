import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2416 = true := by
  decide +kernel

theorem tot2416 : totK PA10K2 A10K2.t2416 = [0, 476545321076, 1743936339557, 1926899756290, 667859291251, 65142262852, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2417 = true := by
  decide +kernel

theorem tot2417 : totK PA10K2 A10K2.t2417 = [0, 307697978958, 1435749814307, 2168764915856, 1063536863104, 90937066088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2418 = true := by
  decide +kernel

theorem tot2418 : totK PA10K2 A10K2.t2418 = [0, 103238782040, 636595641867, 1767744600352, 1805825561690, 510897937663, 31452269383, 0, 0, 0] := by
  decide +kernel

theorem rows2419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2419 = true := by
  decide +kernel

theorem tot2419 : totK PA10K2 A10K2.t2419 = [0, 439698593328, 1795116393307, 1990638989881, 590911435145, 40423735752, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
