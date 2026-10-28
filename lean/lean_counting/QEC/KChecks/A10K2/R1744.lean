import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6976 = true := by
  decide +kernel

theorem tot6976 : totK PA10K2 A10K2.t6976 = [0, 0, 327291078893, 1515844900933, 2152239120631, 862366465987, 62438350213, 0, 0, 0] := by
  decide +kernel

theorem rows6977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6977 = true := by
  decide +kernel

theorem tot6977 : totK PA10K2 A10K2.t6977 = [0, 0, 0, 560559384868, 2038230170555, 1950979513733, 403451599981, 12224107035, 0, 0] := by
  decide +kernel

theorem rows6978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6978 = true := by
  decide +kernel

theorem tot6978 : totK PA10K2 A10K2.t6978 = [0, 0, 319410457816, 1168821321287, 1576359173825, 1316564321901, 521903357347, 48886019071, 0, 0] := by
  decide +kernel

theorem rows6979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6979 = true := by
  decide +kernel

theorem tot6979 : totK PA10K2 A10K2.t6979 = [0, 0, 528021705356, 1863191927463, 1893643901599, 479527207970, 12129354050, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
