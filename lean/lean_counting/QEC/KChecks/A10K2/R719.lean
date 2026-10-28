import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2876 = true := by
  decide +kernel

theorem tot2876 : totK PA10K2 A10K2.t2876 = [0, 0, 602385961494, 2000338430922, 1863536260027, 448015070964, 18533161629, 0, 0, 0] := by
  decide +kernel

theorem rows2877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2877 = true := by
  decide +kernel

theorem tot2877 : totK PA10K2 A10K2.t2877 = [0, 0, 355612379443, 1637735506450, 2050937456726, 598547179235, 37288523557, 0, 0, 0] := by
  decide +kernel

theorem rows2878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2878 = true := by
  decide +kernel

theorem tot2878 : totK PA10K2 A10K2.t2878 = [0, 142762397691, 332990285030, 784343144452, 1825363855835, 1215221285178, 202894274768, 6239673734, 0, 0] := by
  decide +kernel

theorem rows2879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2879 = true := by
  decide +kernel

theorem tot2879 : totK PA10K2 A10K2.t2879 = [0, 413859463496, 1702021626666, 2112574674008, 786975516831, 56416066088, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
