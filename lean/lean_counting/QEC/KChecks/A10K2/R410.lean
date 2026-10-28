import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1640 = true := by
  decide +kernel

theorem tot1640 : totK PA10K2 A10K2.t1640 = [0, 0, 462333369585, 1847616008059, 1871338411950, 440310877550, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1641 = true := by
  decide +kernel

theorem tot1641 : totK PA10K2 A10K2.t1641 = [0, 407498917581, 1562200725772, 1923884638947, 777364483659, 119317863304, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows1642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1642 = true := by
  decide +kernel

theorem tot1642 : totK PA10K2 A10K2.t1642 = [0, 358921836756, 1654590555162, 2022348102137, 694929697613, 53383856823, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1643 = true := by
  decide +kernel

theorem tot1643 : totK PA10K2 A10K2.t1643 = [0, 111822410833, 840006867162, 2035827910050, 1462030041875, 248656676753, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
