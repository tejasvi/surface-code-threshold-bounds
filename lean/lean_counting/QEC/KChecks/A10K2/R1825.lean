import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7300 = true := by
  decide +kernel

theorem tot7300 : totK PA10K2 A10K2.t7300 = [0, 0, 166722870884, 914618530597, 1934201454297, 1259279040424, 187954683236, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7301 = true := by
  decide +kernel

theorem tot7301 : totK PA10K2 A10K2.t7301 = [0, 0, 551004816312, 1964935520675, 2004042960530, 547591160864, 32392175814, 0, 0, 0] := by
  decide +kernel

theorem rows7302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7302 = true := by
  decide +kernel

theorem tot7302 : totK PA10K2 A10K2.t7302 = [0, 0, 45768258037, 883289711286, 2191927053832, 1629679977636, 294145740289, 6853348008, 0, 0] := by
  decide +kernel

theorem rows7303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7303 = true := by
  decide +kernel

theorem tot7303 : totK PA10K2 A10K2.t7303 = [0, 0, 0, 509052198851, 1813162112721, 2036584594368, 653001535924, 40545095891, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
