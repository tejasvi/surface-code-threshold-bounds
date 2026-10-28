import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5876 = true := by
  decide +kernel

theorem tot5876 : totK PA10K2 A10K2.t5876 = [0, 0, 0, 488672855123, 1815238791942, 1970990633576, 460254550672, 18560348465, 0, 0] := by
  decide +kernel

theorem rows5877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5877 = true := by
  decide +kernel

theorem tot5877 : totK PA10K2 A10K2.t5877 = [0, 0, 0, 0, 578358915397, 2000871930873, 1580108963266, 352848458769, 24941563133, 0] := by
  decide +kernel

theorem rows5878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5878 = true := by
  decide +kernel

theorem tot5878 : totK PA10K2 A10K2.t5878 = [0, 0, 0, 479856935244, 1748005861333, 1762685707924, 621413075094, 113751368809, 5447185874, 0] := by
  decide +kernel

theorem rows5879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5879 = true := by
  decide +kernel

theorem tot5879 : totK PA10K2 A10K2.t5879 = [0, 0, 0, 294997606512, 1493163088211, 2113244456389, 777090689137, 58994932240, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
