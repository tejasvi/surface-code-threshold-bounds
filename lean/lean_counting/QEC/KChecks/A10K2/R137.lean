import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t548 = true := by
  decide +kernel

theorem tot548 : totK PA10K2 A10K2.t548 = [0, 528720725284, 1774510768159, 1852138522279, 529906171294, 31936107789, 0, 0, 0, 0] := by
  decide +kernel

theorem rows549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t549 = true := by
  decide +kernel

theorem tot549 : totK PA10K2 A10K2.t549 = [0, 39815911663, 1174888259373, 2397185428303, 1007914468831, 71387666179, 0, 0, 0, 0] := by
  decide +kernel

theorem rows550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t550 = true := by
  decide +kernel

theorem tot550 : totK PA10K2 A10K2.t550 = [113616355882, 530467094329, 1223277106884, 1672324434310, 1024140498384, 173828685864, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t551 = true := by
  decide +kernel

theorem tot551 : totK PA10K2 A10K2.t551 = [464427794452, 1837102631924, 1947616334691, 486792483875, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
