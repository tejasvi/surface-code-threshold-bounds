import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7844 = true := by
  decide +kernel

theorem tot7844 : totK PA10K2 A10K2.t7844 = [0, 0, 566762523448, 1949163717563, 1960183713218, 567477546851, 32743093257, 0, 0, 0] := by
  decide +kernel

theorem rows7845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7845 = true := by
  decide +kernel

theorem tot7845 : totK PA10K2 A10K2.t7845 = [0, 304922396905, 1053646347972, 1582967723649, 1457634006611, 568219255076, 50499610055, 0, 0, 0] := by
  decide +kernel

theorem rows7846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7846 = true := by
  decide +kernel

theorem tot7846 : totK PA10K2 A10K2.t7846 = [0, 457794405310, 1863568627838, 2085258609289, 539773786562, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7847 = true := by
  decide +kernel

theorem tot7847 : totK PA10K2 A10K2.t7847 = [0, 0, 539758633624, 1975195283225, 1835936122395, 441592947745, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
