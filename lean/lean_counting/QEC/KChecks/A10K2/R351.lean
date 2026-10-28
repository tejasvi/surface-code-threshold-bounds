import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1404 = true := by
  decide +kernel

theorem tot1404 : totK PA10K2 A10K2.t1404 = [0, 0, 0, 0, 572863188959, 1842477631798, 1728781838817, 531333865610, 47952069846, 0] := by
  decide +kernel

theorem rows1405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1405 = true := by
  decide +kernel

theorem tot1405 : totK PA10K2 A10K2.t1405 = [0, 0, 0, 0, 280200798865, 1467615155922, 2135665769747, 787890902865, 60189116917, 0] := by
  decide +kernel

theorem rows1406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1406 = true := by
  decide +kernel

theorem tot1406 : totK PA10K2 A10K2.t1406 = [0, 0, 0, 0, 0, 510997942323, 1793037162976, 1715372320385, 466445579472, 30605747850] := by
  decide +kernel

theorem rows1407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1407 = true := by
  decide +kernel

theorem tot1407 : totK PA10K2 A10K2.t1407 = [0, 0, 0, 0, 496338503450, 1698531090124, 1758170353004, 584518036531, 53548638049, 0] := by
  decide +kernel

end QECKChecks.A10K2
