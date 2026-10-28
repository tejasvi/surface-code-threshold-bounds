import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7988 = true := by
  decide +kernel

theorem tot7988 : totK PA10K2 A10K2.t7988 = [0, 0, 450701360862, 1829074642345, 1977091738848, 527008997445, 18696211658, 0, 0, 0] := by
  decide +kernel

theorem rows7989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7989 = true := by
  decide +kernel

theorem tot7989 : totK PA10K2 A10K2.t7989 = [0, 0, 0, 552040465162, 1936715200971, 1757059781076, 425473461519, 25371180993, 0, 0] := by
  decide +kernel

theorem rows7990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7990 = true := by
  decide +kernel

theorem tot7990 : totK PA10K2 A10K2.t7990 = [0, 0, 287800902345, 1256427429064, 1921486101255, 1113766986948, 186008406872, 5460492893, 0, 0] := by
  decide +kernel

theorem rows7991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7991 = true := by
  decide +kernel

theorem tot7991 : totK PA10K2 A10K2.t7991 = [0, 0, 294672725543, 1540299895440, 2117995426404, 729298070437, 54047593666, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
