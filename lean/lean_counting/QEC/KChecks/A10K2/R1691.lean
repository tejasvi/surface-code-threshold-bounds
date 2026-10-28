import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6764 = true := by
  decide +kernel

theorem tot6764 : totK PA10K2 A10K2.t6764 = [0, 0, 345173328948, 1423958374189, 1827570295671, 945273685279, 162404464798, 5453062850, 0, 0] := by
  decide +kernel

theorem rows6765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6765 = true := by
  decide +kernel

theorem tot6765 : totK PA10K2 A10K2.t6765 = [0, 0, 233562348309, 1340002792743, 2136738292873, 848096406742, 57254279214, 0, 0, 0] := by
  decide +kernel

theorem rows6766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6766 = true := by
  decide +kernel

theorem tot6766 : totK PA10K2 A10K2.t6766 = [0, 0, 486208102555, 1510851369316, 1739294398174, 899680592967, 163625230266, 5685526223, 0, 0] := by
  decide +kernel

theorem rows6767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6767 = true := by
  decide +kernel

theorem tot6767 : totK PA10K2 A10K2.t6767 = [0, 304922396905, 976511119592, 1633414530016, 1559506265717, 514631391500, 36512104324, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
