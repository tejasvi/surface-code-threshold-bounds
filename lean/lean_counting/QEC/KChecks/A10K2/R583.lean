import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2332 = true := by
  decide +kernel

theorem tot2332 : totK PA10K2 A10K2.t2332 = [0, 481398847354, 1834778333922, 1918889761544, 529381622889, 32440624915, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2333 = true := by
  decide +kernel

theorem tot2333 : totK PA10K2 A10K2.t2333 = [0, 0, 693787586208, 2147904955434, 1575227632632, 231080760827, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2334 = true := by
  decide +kernel

theorem tot2334 : totK PA10K2 A10K2.t2334 = [0, 0, 557764072828, 1953397536610, 1799613812297, 451991012306, 32021558464, 0, 0, 0] := by
  decide +kernel

theorem rows2335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2335 = true := by
  decide +kernel

theorem tot2335 : totK PA10K2 A10K2.t2335 = [0, 0, 486186711538, 1719058033414, 1897573979851, 536707707600, 36734515145, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
