import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7264 = true := by
  decide +kernel

theorem tot7264 : totK PA10K2 A10K2.t7264 = [0, 0, 0, 387214000062, 1675295619568, 2038275063566, 667230884300, 49649068552, 0, 0] := by
  decide +kernel

theorem rows7265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7265 = true := by
  decide +kernel

theorem tot7265 : totK PA10K2 A10K2.t7265 = [0, 0, 0, 76178814289, 826820669343, 2075533846723, 1463871855050, 253079301300, 7007974415, 0] := by
  decide +kernel

theorem rows7266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7266 = true := by
  decide +kernel

theorem tot7266 : totK PA10K2 A10K2.t7266 = [0, 0, 0, 538430442136, 1957679564865, 1775533732661, 326874144942, 11531959710, 0, 0] := by
  decide +kernel

theorem rows7267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7267 = true := by
  decide +kernel

theorem tot7267 : totK PA10K2 A10K2.t7267 = [0, 0, 0, 585214918702, 1999600731821, 2026972775758, 493165388850, 18363904575, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
