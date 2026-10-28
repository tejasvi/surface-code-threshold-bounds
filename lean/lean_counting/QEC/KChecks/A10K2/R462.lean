import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1848 = true := by
  decide +kernel

theorem tot1848 : totK PA10K2 A10K2.t1848 = [0, 348313302752, 1164694461178, 1366556939569, 1063702566043, 675192978700, 137525537872, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1849 = true := by
  decide +kernel

theorem tot1849 : totK PA10K2 A10K2.t1849 = [0, 453036436125, 1764119129771, 2011641720193, 724340170361, 43607708191, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1850 = true := by
  decide +kernel

theorem tot1850 : totK PA10K2 A10K2.t1850 = [0, 0, 603723147795, 1911309811412, 1777545195232, 480178237055, 30810868011, 0, 0, 0] := by
  decide +kernel

theorem rows1851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1851 = true := by
  decide +kernel

theorem tot1851 : totK PA10K2 A10K2.t1851 = [0, 474133625560, 1657140778835, 1985851442353, 822433212129, 73981465579, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
