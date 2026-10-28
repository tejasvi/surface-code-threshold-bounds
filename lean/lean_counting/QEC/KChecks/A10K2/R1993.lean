import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7972 = true := by
  decide +kernel

theorem tot7972 : totK PA10K2 A10K2.t7972 = [0, 0, 298738363490, 1136021032380, 1861891073333, 1324575279763, 191484731559, 0, 0, 0] := by
  decide +kernel

theorem rows7973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7973 = true := by
  decide +kernel

theorem tot7973 : totK PA10K2 A10K2.t7973 = [0, 0, 466524748085, 1896282684048, 2083062662774, 512877578725, 24019274592, 0, 0, 0] := by
  decide +kernel

theorem rows7974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7974 = true := by
  decide +kernel

theorem tot7974 : totK PA10K2 A10K2.t7974 = [0, 0, 0, 672447858051, 2074388785524, 1741989997312, 360898595572, 12219140272, 0, 0] := by
  decide +kernel

theorem rows7975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7975 = true := by
  decide +kernel

theorem tot7975 : totK PA10K2 A10K2.t7975 = [0, 0, 280714159330, 1320186619200, 2110731122611, 1140799551474, 108926642128, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
