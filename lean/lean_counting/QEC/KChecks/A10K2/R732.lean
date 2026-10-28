import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2928 = true := by
  decide +kernel

theorem tot2928 : totK PA10K2 A10K2.t2928 = [0, 501025875666, 1829046727137, 2010727993014, 598716642023, 23620721234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2929 = true := by
  decide +kernel

theorem tot2929 : totK PA10K2 A10K2.t2929 = [0, 227341616431, 1344074085585, 2202768660002, 1107759604629, 113417152791, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2930 = true := by
  decide +kernel

theorem tot2930 : totK PA10K2 A10K2.t2930 = [0, 0, 604332811912, 2052003001985, 1900973327572, 379620885254, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows2931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2931 = true := by
  decide +kernel

theorem tot2931 : totK PA10K2 A10K2.t2931 = [0, 345924611889, 1178305409627, 1527698138709, 1179708503759, 501811519132, 48886019071, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
