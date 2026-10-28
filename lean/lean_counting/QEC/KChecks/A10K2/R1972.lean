import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7888 = true := by
  decide +kernel

theorem tot7888 : totK PA10K2 A10K2.t7888 = [0, 0, 0, 445202945339, 1811526724418, 1924900829605, 516893082278, 32470817489, 0, 0] := by
  decide +kernel

theorem rows7889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7889 = true := by
  decide +kernel

theorem tot7889 : totK PA10K2 A10K2.t7889 = [0, 0, 0, 632717372449, 2068395267703, 1845691396981, 386334452494, 13113133354, 0, 0] := by
  decide +kernel

theorem rows7890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7890 = true := by
  decide +kernel

theorem tot7890 : totK PA10K2 A10K2.t7890 = [0, 0, 171753838140, 770706421744, 1735946291273, 1726496444910, 369361253027, 12260057084, 0, 0] := by
  decide +kernel

theorem rows7891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7891 = true := by
  decide +kernel

theorem tot7891 : totK PA10K2 A10K2.t7891 = [0, 0, 416962992548, 1740660733683, 2168180527112, 743734344843, 43229287191, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
