import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1328 = true := by
  decide +kernel

theorem tot1328 : totK PA10K2 A10K2.t1328 = [0, 0, 0, 599436198152, 2043284135276, 1995639545306, 423332814718, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1329 = true := by
  decide +kernel

theorem tot1329 : totK PA10K2 A10K2.t1329 = [0, 0, 0, 525720674870, 1891965488571, 1933748279119, 599580761074, 41407999670, 0, 0] := by
  decide +kernel

theorem rows1330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1330 = true := by
  decide +kernel

theorem tot1330 : totK PA10K2 A10K2.t1330 = [0, 0, 0, 527472828986, 1843992391867, 1857695978249, 475020897463, 31112697984, 0, 0] := by
  decide +kernel

theorem rows1331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1331 = true := by
  decide +kernel

theorem tot1331 : totK PA10K2 A10K2.t1331 = [0, 0, 0, 0, 789316064394, 2237770995319, 1512302052028, 260066619489, 7007974415, 0] := by
  decide +kernel

end QECKChecks.A10K2
