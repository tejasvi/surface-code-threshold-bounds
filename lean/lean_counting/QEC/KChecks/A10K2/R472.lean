import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1888 = true := by
  decide +kernel

theorem tot1888 : totK PA10K2 A10K2.t1888 = [0, 0, 303896576234, 1403734112210, 2159320186761, 1084406118756, 107047425936, 0, 0, 0] := by
  decide +kernel

theorem rows1889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1889 = true := by
  decide +kernel

theorem tot1889 : totK PA10K2 A10K2.t1889 = [0, 0, 286185292359, 1334746249902, 2064887093816, 1149816448870, 198735157428, 7151180950, 0, 0] := by
  decide +kernel

theorem rows1890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1890 = true := by
  decide +kernel

theorem tot1890 : totK PA10K2 A10K2.t1890 = [0, 0, 576020245237, 1913443650362, 1894455601835, 519088087255, 18905173144, 0, 0, 0] := by
  decide +kernel

theorem rows1891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1891 = true := by
  decide +kernel

theorem tot1891 : totK PA10K2 A10K2.t1891 = [0, 0, 0, 738409913319, 2221495802336, 1708212914323, 300696508902, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
